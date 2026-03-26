use std::convert::TryFrom;
use std::iter::FusedIterator;
use std::rc::Rc;
use crate::common::error::{Error, Res};
use crate::sql::catalog::{
  self,
  RelationType,
  INFORMATION_SCHEMA_COLUMNS,
  INFORMATION_SCHEMA_RELATIONS,
  INFORMATION_SCHEMA_SCHEMATA,
};
use crate::sql::plan::{Expression, PhysicalPlan};
use crate::sql::row::Row;
use crate::sql::session::Session;
use crate::sql::types::Type;
use crate::storage::btree::BTreeIter;
use crate::storage::txn::{TransactionRef, next_object_id};

// The runtime value produced by evaluating a single expression against a row.
// Mirrors the SQL type system (Section 1.1 of SQL_SEMANTICS.md) but lives only
// inside the evaluator — it is never stored or returned to callers of `execute`.
#[derive(Debug, PartialEq)]
enum ExprEvalResult {
  // Represents an absent / unknown value (SQL NULL).
  Null,
  Bool(bool),
  Int(i32),
  BigInt(i64),
  Float(f32),
  Double(f64),
  Text(String),
}

// Recursively evaluates `expr` against the given `row`.
//
// The analysis pass guarantees that every `Expression` reaching this function
// is fully type-resolved, so type mismatches hit `unreachable!` rather than
// returning errors. Runtime errors (overflow, division by zero, out-of-range
// casts, unparseable strings) are returned as `Err(SQLExecutionError(...))`.
//
// NULL semantics follow SQL_SEMANTICS.md §2: any operation with a NULL operand
// propagates NULL, except IS NULL / IS NOT NULL which always return a Bool.
fn expr_eval(expr: &Expression, row: &Row) -> Res<ExprEvalResult> {
  match expr {
    Expression::Add(ref left, ref right) => {
      let lvalue = expr_eval(left, row)?;
      let rvalue = expr_eval(right, row)?;
      match (lvalue, rvalue) {
        (ExprEvalResult::Null, _) | (_, ExprEvalResult::Null) => Ok(ExprEvalResult::Null),
        (ExprEvalResult::Int(l), ExprEvalResult::Int(r)) => {
          match l.checked_add(r) {
            Some(value) => Ok(ExprEvalResult::Int(value)),
            None => Err(Error::SQLExecutionError(format!("Int ({} + {}) out of range", l, r)))
          }
        },
        (ExprEvalResult::BigInt(l), ExprEvalResult::BigInt(r)) => {
          match l.checked_add(r) {
            Some(value) => Ok(ExprEvalResult::BigInt(value)),
            None => Err(Error::SQLExecutionError(format!("BigInt ({} + {}) out of range", l, r)))
          }
        },
        (ExprEvalResult::Float(l), ExprEvalResult::Float(r)) => Ok(ExprEvalResult::Float(l + r)),
        (ExprEvalResult::Double(l), ExprEvalResult::Double(r)) => Ok(ExprEvalResult::Double(l + r)),
        (l, r) => unreachable!("Add: unexpected type combination {:?} + {:?}", l, r),
      }
    },
    Expression::Alias(ref child, _) => expr_eval(child, row),
    Expression::And(ref left, ref right) => {
      let lvalue = expr_eval(left, row)?;
      let rvalue = expr_eval(right, row)?;
      match (lvalue, rvalue) {
        // FALSE short-circuits: FALSE AND NULL = FALSE (§2.6).
        (ExprEvalResult::Bool(false), _) | (_, ExprEvalResult::Bool(false)) => {
          Ok(ExprEvalResult::Bool(false))
        },
        (ExprEvalResult::Null, _) | (_, ExprEvalResult::Null) => Ok(ExprEvalResult::Null),
        (ExprEvalResult::Bool(l), ExprEvalResult::Bool(r)) => Ok(ExprEvalResult::Bool(l && r)),
        (l, r) => unreachable!("And: unexpected type combination {:?} AND {:?}", l, r),
      }
    },
    // Cast rules follow §4 of SQL_SEMANTICS.md.
    // Widening casts (§4.1) always succeed. Narrowing casts (§4.2) are checked
    // at runtime and return SQLExecutionError on overflow or parse failure.
    Expression::Cast(ref expr, ref tpe) => {
      match expr_eval(expr, row)? {
        // NULL cast to any type remains NULL (§4.1).
        ExprEvalResult::Null => Ok(ExprEvalResult::Null),
        ExprEvalResult::Bool(v) => match tpe.as_ref() {
          Type::BOOL => Ok(ExprEvalResult::Bool(v)),
          Type::TEXT => Ok(ExprEvalResult::Text(v.to_string())),
          t => unreachable!("Cast: unexpected type combination Bool({}) as {:?}", v, t),
        },
        ExprEvalResult::Int(v) => match tpe.as_ref() {
          Type::INT => Ok(ExprEvalResult::Int(v)),
          Type::BIGINT => Ok(ExprEvalResult::BigInt(v as i64)),
          Type::FLOAT => Ok(ExprEvalResult::Float(v as f32)),
          Type::DOUBLE => Ok(ExprEvalResult::Double(v as f64)),
          Type::TEXT => Ok(ExprEvalResult::Text(v.to_string())),
          t => unreachable!("Cast: unexpected type combination Int({}) as {:?}", v, t),
        },
        ExprEvalResult::BigInt(v) => match tpe.as_ref() {
          // Narrowing: fails if v is outside i32 range (§4.2).
          Type::INT => {
            i32::try_from(v)
              .map(ExprEvalResult::Int)
              .map_err(|_| Error::SQLExecutionError(format!("Cast {} as INT out of range", v)))
          },
          Type::BIGINT => Ok(ExprEvalResult::BigInt(v)),
          Type::FLOAT => Ok(ExprEvalResult::Float(v as f32)),
          Type::DOUBLE => Ok(ExprEvalResult::Double(v as f64)),
          Type::TEXT => Ok(ExprEvalResult::Text(v.to_string())),
          t => unreachable!("Cast: unexpected type combination BigInt({}) as {:?}", v, t),
        },
        ExprEvalResult::Float(v) => match tpe.as_ref() {
          // Widen to f64 first so the range comparisons use exact f64 boundaries.
          // Rust's `as` truncates toward zero; we must check bounds before casting
          // because out-of-range `as` saturates rather than errors (§4.2).
          Type::INT => {
            let v64 = v as f64;
            if !v64.is_finite() || v64 < i32::MIN as f64 || v64 > i32::MAX as f64 {
              return Err(Error::SQLExecutionError(format!("Cast {} as INT out of range", v)));
            }
            Ok(ExprEvalResult::Int(v as i32))
          },
          Type::BIGINT => {
            let v64 = v as f64;
            // Upper bound: i64::MAX as f64 rounds up to 2^63, so use +1 to detect overflow.
            if !v64.is_finite() || v64 < i64::MIN as f64 || v64 >= (i64::MAX as f64) + 1.0 {
              return Err(Error::SQLExecutionError(format!("Cast {} as BIGINT out of range", v)));
            }
            Ok(ExprEvalResult::BigInt(v as i64))
          },
          Type::FLOAT => Ok(ExprEvalResult::Float(v)),
          Type::DOUBLE => Ok(ExprEvalResult::Double(v as f64)),
          Type::TEXT => Ok(ExprEvalResult::Text(v.to_string())),
          t => unreachable!("Cast: unexpected type combination Float({}) as {:?}", v, t),
        },
        ExprEvalResult::Double(v) => match tpe.as_ref() {
          Type::INT => {
            if !v.is_finite() || v < i32::MIN as f64 || v > i32::MAX as f64 {
              return Err(Error::SQLExecutionError(format!("Cast {} as INT out of range", v)));
            }
            Ok(ExprEvalResult::Int(v as i32))
          },
          Type::BIGINT => {
            if !v.is_finite() || v < i64::MIN as f64 || v >= (i64::MAX as f64) + 1.0 {
              return Err(Error::SQLExecutionError(format!("Cast {} as BIGINT out of range", v)));
            }
            Ok(ExprEvalResult::BigInt(v as i64))
          },
          Type::FLOAT => Ok(ExprEvalResult::Float(v as f32)),
          Type::DOUBLE => Ok(ExprEvalResult::Double(v)),
          Type::TEXT => Ok(ExprEvalResult::Text(v.to_string())),
          t => unreachable!("Cast: unexpected type combination Double({}) as {:?}", v, t),
        },
        ExprEvalResult::Text(v) => match tpe.as_ref() {
          // All TEXT narrowing casts parse at runtime; invalid strings are errors (§4.2).
          Type::INT => v.parse::<i32>()
            .map(ExprEvalResult::Int)
            .map_err(|_| Error::SQLExecutionError(format!("Cast \"{}\" as {} invalid", v, tpe))),
          Type::BIGINT => v.parse::<i64>()
            .map(ExprEvalResult::BigInt)
            .map_err(|_| Error::SQLExecutionError(format!("Cast \"{}\" as {} invalid", v, tpe))),
          Type::FLOAT => v.parse::<f32>()
            .map(ExprEvalResult::Float)
            .map_err(|_| Error::SQLExecutionError(format!("Cast \"{}\" as {} invalid", v, tpe))),
          Type::DOUBLE => v.parse::<f64>()
            .map(ExprEvalResult::Double)
            .map_err(|_| Error::SQLExecutionError(format!("Cast \"{}\" as {} invalid", v, tpe))),
          // Accepted case-insensitively per §4.2; anything else is a runtime error.
          Type::BOOL => match v.to_ascii_lowercase().as_str() {
            "true"  => Ok(ExprEvalResult::Bool(true)),
            "false" => Ok(ExprEvalResult::Bool(false)),
            _ => Err(Error::SQLExecutionError(format!("Cast \"{}\" as {} invalid", v, tpe))),
          },
          Type::TEXT => Ok(ExprEvalResult::Text(v)),
          t => unreachable!("Cast: unexpected type combination Text({}) as {}", v, t),
        },
      }
    },
    Expression::Concat(ref left, ref right) => {
      let lvalue = expr_eval(left, row)?;
      let rvalue = expr_eval(right, row)?;
      match (lvalue, rvalue) {
        (ExprEvalResult::Null, _) | (_, ExprEvalResult::Null) => Ok(ExprEvalResult::Null),
        (ExprEvalResult::Text(l), ExprEvalResult::Text(r)) => {
          Ok(ExprEvalResult::Text(format!("{}{}", l, r)))
        },
        (l, r) => unreachable!("Concat: unexpected type combination {:?} || {:?}", l, r),
      }
    },
    // Reads the column at `index` from the row. The static type comes from the
    // table schema rather than the value, so we always know which Row getter to call.
    Expression::ColumnRef(_, ref table_info, _, ref index) => {
      let idx = *index;
      if row.is_null(idx) {
        return Ok(ExprEvalResult::Null);
      }
      match table_info.relation_fields().get()[idx].data_type() {
        Type::BOOL => Ok(ExprEvalResult::Bool(row.get_bool(idx))),
        Type::INT => Ok(ExprEvalResult::Int(row.get_i32(idx))),
        Type::BIGINT => Ok(ExprEvalResult::BigInt(row.get_i64(idx))),
        Type::FLOAT => Ok(ExprEvalResult::Float(row.get_f32(idx))),
        Type::DOUBLE => Ok(ExprEvalResult::Double(row.get_f64(idx))),
        Type::TEXT => Ok(ExprEvalResult::Text(row.get_str(idx).to_string())),
        tpe => unreachable!("ColumnRef: unsupported column type {:?}", tpe),
      }
    },
    // Integer division truncates toward zero (§3.3). Division by zero and
    // MIN / -1 (which would overflow) are both runtime errors (§8.5).
    // Float / double division by zero is also a runtime error (§8.5) — IEEE 754
    // Inf is not produced.
    Expression::Divide(ref left, ref right) => {
      let lvalue = expr_eval(left, row)?;
      let rvalue = expr_eval(right, row)?;
      match (lvalue, rvalue) {
        (ExprEvalResult::Null, _) | (_, ExprEvalResult::Null) => Ok(ExprEvalResult::Null),
        (ExprEvalResult::Int(l), ExprEvalResult::Int(r)) => {
          match l.checked_div(r) {
            Some(value) => Ok(ExprEvalResult::Int(value)),
            None if r == 0 => Err(Error::SQLExecutionError("Division by zero".to_string())),
            None => Err(Error::SQLExecutionError(format!("Int ({} / {}) out of range", l, r))),
          }
        },
        (ExprEvalResult::BigInt(l), ExprEvalResult::BigInt(r)) => {
          match l.checked_div(r) {
            Some(value) => Ok(ExprEvalResult::BigInt(value)),
            None if r == 0 => Err(Error::SQLExecutionError("Division by zero".to_string())),
            None => Err(Error::SQLExecutionError(format!("BigInt ({} / {}) out of range", l, r))),
          }
        },
        (ExprEvalResult::Float(l), ExprEvalResult::Float(r)) => {
          if r == 0.0 { return Err(Error::SQLExecutionError("Division by zero".to_string())); }
          Ok(ExprEvalResult::Float(l / r))
        },
        (ExprEvalResult::Double(l), ExprEvalResult::Double(r)) => {
          if r == 0.0 { return Err(Error::SQLExecutionError("Division by zero".to_string())); }
          Ok(ExprEvalResult::Double(l / r))
        },
        (l, r) => unreachable!("Divide: unexpected type combination {:?} / {:?}", l, r),
      }
    },
    // NaN = NaN -> TRUE; NaN = x -> FALSE for all non-NaN x (§8.6).
    Expression::Equals(ref left, ref right) => {
      let lvalue = expr_eval(left, row)?;
      let rvalue = expr_eval(right, row)?;
      match (lvalue, rvalue) {
        (ExprEvalResult::Null, _) | (_, ExprEvalResult::Null) => Ok(ExprEvalResult::Null),
        (ExprEvalResult::Int(l), ExprEvalResult::Int(r)) => Ok(ExprEvalResult::Bool(l == r)),
        (ExprEvalResult::BigInt(l), ExprEvalResult::BigInt(r)) => Ok(ExprEvalResult::Bool(l == r)),
        (ExprEvalResult::Float(l), ExprEvalResult::Float(r)) => {
          Ok(ExprEvalResult::Bool(l.is_nan() && r.is_nan() || l == r))
        },
        (ExprEvalResult::Double(l), ExprEvalResult::Double(r)) => {
          Ok(ExprEvalResult::Bool(l.is_nan() && r.is_nan() || l == r))
        },
        (ExprEvalResult::Text(l), ExprEvalResult::Text(r)) => Ok(ExprEvalResult::Bool(l == r)),
        (ExprEvalResult::Bool(l), ExprEvalResult::Bool(r)) => Ok(ExprEvalResult::Bool(l == r)),
        (l, r) => unreachable!("Equals: unexpected type combination {:?} == {:?}", l, r),
      }
    },
    Expression::GreaterThan(ref left, ref right) => {
      let lvalue = expr_eval(left, row)?;
      let rvalue = expr_eval(right, row)?;
      match (lvalue, rvalue) {
        (ExprEvalResult::Null, _) | (_, ExprEvalResult::Null) => Ok(ExprEvalResult::Null),
        (ExprEvalResult::Int(l), ExprEvalResult::Int(r)) => Ok(ExprEvalResult::Bool(l > r)),
        (ExprEvalResult::BigInt(l), ExprEvalResult::BigInt(r)) => Ok(ExprEvalResult::Bool(l > r)),
        // NaN is considered the largest value (postgres sort semantics); NaN > NaN is false.
        (ExprEvalResult::Float(l), ExprEvalResult::Float(r)) => {
          Ok(ExprEvalResult::Bool(!r.is_nan() && (l.is_nan() || l > r)))
        },
        (ExprEvalResult::Double(l), ExprEvalResult::Double(r)) => {
          Ok(ExprEvalResult::Bool(!r.is_nan() && (l.is_nan() || l > r)))
        },
        (ExprEvalResult::Text(l), ExprEvalResult::Text(r)) => Ok(ExprEvalResult::Bool(l > r)),
        (ExprEvalResult::Bool(l), ExprEvalResult::Bool(r)) => Ok(ExprEvalResult::Bool(l > r)),
        (l, r) => unreachable!("GreaterThan: unexpected type combination {:?} > {:?}", l, r),
      }
    },
    Expression::GreaterThanEquals(ref left, ref right) => {
      let lvalue = expr_eval(left, row)?;
      let rvalue = expr_eval(right, row)?;
      match (lvalue, rvalue) {
        (ExprEvalResult::Null, _) | (_, ExprEvalResult::Null) => Ok(ExprEvalResult::Null),
        (ExprEvalResult::Int(l), ExprEvalResult::Int(r)) => Ok(ExprEvalResult::Bool(l >= r)),
        (ExprEvalResult::BigInt(l), ExprEvalResult::BigInt(r)) => Ok(ExprEvalResult::Bool(l >= r)),
        // NaN >= NaN is true (NaN equals itself); NaN >= x is true; x >= NaN is false.
        (ExprEvalResult::Float(l), ExprEvalResult::Float(r)) => {
          Ok(ExprEvalResult::Bool(l.is_nan() || (!r.is_nan() && l >= r)))
        },
        (ExprEvalResult::Double(l), ExprEvalResult::Double(r)) => {
          Ok(ExprEvalResult::Bool(l.is_nan() || (!r.is_nan() && l >= r)))
        },
        (ExprEvalResult::Text(l), ExprEvalResult::Text(r)) => Ok(ExprEvalResult::Bool(l >= r)),
        (ExprEvalResult::Bool(l), ExprEvalResult::Bool(r)) => Ok(ExprEvalResult::Bool(l >= r)),
        (l, r) => unreachable!("GreaterThanEquals: unexpected type combination {:?} >= {:?}", l, r),
      }
    },
    Expression::Identifier(parts, name) => {
      unreachable!("Identifier: unresolved expression for parts {:?} and name {}", parts, name)
    },
    // IS NULL / IS NOT NULL always return a non-nullable Bool, even when the
    // child is NULL — they are the only expressions that consume NULL without
    // propagating it (§2.4, §7).
    Expression::IsNull(ref child) => {
      Ok(ExprEvalResult::Bool(expr_eval(child, row)? == ExprEvalResult::Null))
    },
    Expression::IsNotNull(ref child) => {
      Ok(ExprEvalResult::Bool(expr_eval(child, row)? != ExprEvalResult::Null))
    },
    Expression::LessThan(ref left, ref right) => {
      let lvalue = expr_eval(left, row)?;
      let rvalue = expr_eval(right, row)?;
      match (lvalue, rvalue) {
        (ExprEvalResult::Null, _) | (_, ExprEvalResult::Null) => Ok(ExprEvalResult::Null),
        (ExprEvalResult::Int(l), ExprEvalResult::Int(r)) => Ok(ExprEvalResult::Bool(l < r)),
        (ExprEvalResult::BigInt(l), ExprEvalResult::BigInt(r)) => Ok(ExprEvalResult::Bool(l < r)),
        // NaN < NaN is false; NaN < x is false; x < NaN is true.
        (ExprEvalResult::Float(l), ExprEvalResult::Float(r)) => {
          Ok(ExprEvalResult::Bool(!l.is_nan() && (r.is_nan() || l < r)))
        },
        (ExprEvalResult::Double(l), ExprEvalResult::Double(r)) => {
          Ok(ExprEvalResult::Bool(!l.is_nan() && (r.is_nan() || l < r)))
        },
        (ExprEvalResult::Text(l), ExprEvalResult::Text(r)) => Ok(ExprEvalResult::Bool(l < r)),
        (ExprEvalResult::Bool(l), ExprEvalResult::Bool(r)) => Ok(ExprEvalResult::Bool(l < r)),
        (l, r) => unreachable!("LessThan: unexpected type combination {:?} < {:?}", l, r),
      }
    },
    Expression::LessThanEquals(ref left, ref right) => {
      let lvalue = expr_eval(left, row)?;
      let rvalue = expr_eval(right, row)?;
      match (lvalue, rvalue) {
        (ExprEvalResult::Null, _) | (_, ExprEvalResult::Null) => Ok(ExprEvalResult::Null),
        (ExprEvalResult::Int(l), ExprEvalResult::Int(r)) => Ok(ExprEvalResult::Bool(l <= r)),
        (ExprEvalResult::BigInt(l), ExprEvalResult::BigInt(r)) => Ok(ExprEvalResult::Bool(l <= r)),
        // NaN <= NaN is true; NaN <= x is false; x <= NaN is true.
        (ExprEvalResult::Float(l), ExprEvalResult::Float(r)) => {
          Ok(ExprEvalResult::Bool(r.is_nan() || (!l.is_nan() && l <= r)))
        },
        (ExprEvalResult::Double(l), ExprEvalResult::Double(r)) => {
          Ok(ExprEvalResult::Bool(r.is_nan() || (!l.is_nan() && l <= r)))
        },
        (ExprEvalResult::Text(l), ExprEvalResult::Text(r)) => Ok(ExprEvalResult::Bool(l <= r)),
        (ExprEvalResult::Bool(l), ExprEvalResult::Bool(r)) => Ok(ExprEvalResult::Bool(l <= r)),
        (l, r) => unreachable!("LessThanEquals: unexpected type combination {:?} <= {:?}", l, r),
      }
    },
    Expression::LiteralBool(value) => Ok(ExprEvalResult::Bool(*value)),
    Expression::LiteralInt(value) => Ok(ExprEvalResult::Int(*value)),
    Expression::LiteralBigInt(value) => Ok(ExprEvalResult::BigInt(*value)),
    Expression::LiteralFloat(value) => Ok(ExprEvalResult::Float(*value)),
    Expression::LiteralDouble(value) => Ok(ExprEvalResult::Double(*value)),
    Expression::LiteralString(value) => Ok(ExprEvalResult::Text(value.as_ref().clone())),
    Expression::Multiply(ref left, ref right) => {
      let lvalue = expr_eval(left, row)?;
      let rvalue = expr_eval(right, row)?;
      match (lvalue, rvalue) {
        (ExprEvalResult::Null, _) | (_, ExprEvalResult::Null) => Ok(ExprEvalResult::Null),
        (ExprEvalResult::Int(l), ExprEvalResult::Int(r)) => {
          match l.checked_mul(r) {
            Some(value) => Ok(ExprEvalResult::Int(value)),
            None => Err(Error::SQLExecutionError(format!("Int ({} * {}) out of range", l, r))),
          }
        },
        (ExprEvalResult::BigInt(l), ExprEvalResult::BigInt(r)) => {
          match l.checked_mul(r) {
            Some(value) => Ok(ExprEvalResult::BigInt(value)),
            None => Err(Error::SQLExecutionError(format!("BigInt ({} * {}) out of range", l, r))),
          }
        },
        (ExprEvalResult::Float(l), ExprEvalResult::Float(r)) => Ok(ExprEvalResult::Float(l * r)),
        (ExprEvalResult::Double(l), ExprEvalResult::Double(r)) => Ok(ExprEvalResult::Double(l * r)),
        (l, r) => unreachable!("Multiply: unexpected type combination {:?} * {:?}", l, r),
      }
    },
    Expression::Not(ref child) => {
      match expr_eval(child, row)? {
        ExprEvalResult::Null => Ok(ExprEvalResult::Null),
        ExprEvalResult::Bool(v) => Ok(ExprEvalResult::Bool(!v)),
        v => unreachable!("Not: unexpected type combination {:?}", v),
      }
    },
    Expression::NotEquals(ref left, ref right) => {
      let lvalue = expr_eval(left, row)?;
      let rvalue = expr_eval(right, row)?;
      match (lvalue, rvalue) {
        (ExprEvalResult::Null, _) | (_, ExprEvalResult::Null) => Ok(ExprEvalResult::Null),
        (ExprEvalResult::Int(l), ExprEvalResult::Int(r)) => Ok(ExprEvalResult::Bool(l != r)),
        (ExprEvalResult::BigInt(l), ExprEvalResult::BigInt(r)) => Ok(ExprEvalResult::Bool(l != r)),
        // NaN != NaN is false (NaN equals itself); NaN != x is true for all non-NaN x.
        (ExprEvalResult::Float(l), ExprEvalResult::Float(r)) => {
          Ok(ExprEvalResult::Bool(!(l.is_nan() && r.is_nan()) && l != r))
        },
        (ExprEvalResult::Double(l), ExprEvalResult::Double(r)) => {
          Ok(ExprEvalResult::Bool(!(l.is_nan() && r.is_nan()) && l != r))
        },
        (ExprEvalResult::Text(l), ExprEvalResult::Text(r)) => Ok(ExprEvalResult::Bool(l != r)),
        (ExprEvalResult::Bool(l), ExprEvalResult::Bool(r)) => Ok(ExprEvalResult::Bool(l != r)),
        (l, r) => unreachable!("NotEquals: unexpected type combination {:?} != {:?}", l, r),
      }
    },
    Expression::Null => Ok(ExprEvalResult::Null),
    Expression::Or(ref left, ref right) => {
      let lvalue = expr_eval(left, row)?;
      let rvalue = expr_eval(right, row)?;
      match (lvalue, rvalue) {
        // TRUE short-circuits: TRUE OR NULL = TRUE (§2.6).
        (ExprEvalResult::Bool(true), _) | (_, ExprEvalResult::Bool(true)) => {
          Ok(ExprEvalResult::Bool(true))
        },
        (ExprEvalResult::Null, _) | (_, ExprEvalResult::Null) => Ok(ExprEvalResult::Null),
        (ExprEvalResult::Bool(l), ExprEvalResult::Bool(r)) => Ok(ExprEvalResult::Bool(l || r)),
        (l, r) => unreachable!("Or: unexpected type combination {:?} OR {:?}", l, r),
      }
    },
    Expression::Star(ref parts) => {
      unreachable!("Star: unresolved expression for parts {:?}", parts)
    },
    Expression::Subtract(ref left, ref right) => {
      let lvalue = expr_eval(left, row)?;
      let rvalue = expr_eval(right, row)?;
      match (lvalue, rvalue) {
        (ExprEvalResult::Null, _) | (_, ExprEvalResult::Null) => Ok(ExprEvalResult::Null),
        (ExprEvalResult::Int(l), ExprEvalResult::Int(r)) => {
          match l.checked_sub(r) {
            Some(value) => Ok(ExprEvalResult::Int(value)),
            None => Err(Error::SQLExecutionError(format!("Int ({} - {}) out of range", l, r))),
          }
        },
        (ExprEvalResult::BigInt(l), ExprEvalResult::BigInt(r)) => {
          match l.checked_sub(r) {
            Some(value) => Ok(ExprEvalResult::BigInt(value)),
            None => Err(Error::SQLExecutionError(format!("BigInt ({} - {}) out of range", l, r))),
          }
        },
        (ExprEvalResult::Float(l), ExprEvalResult::Float(r)) => Ok(ExprEvalResult::Float(l - r)),
        (ExprEvalResult::Double(l), ExprEvalResult::Double(r)) => Ok(ExprEvalResult::Double(l - r)),
        (l, r) => unreachable!("Subtract: unexpected type combination {:?} - {:?}", l, r),
      }
    },
    Expression::UnaryPlus(ref child) => {
      match expr_eval(child, row)? {
        ExprEvalResult::Null => Ok(ExprEvalResult::Null),
        ExprEvalResult::Int(v) => Ok(ExprEvalResult::Int(v)),
        ExprEvalResult::BigInt(v) => Ok(ExprEvalResult::BigInt(v)),
        ExprEvalResult::Float(v) => Ok(ExprEvalResult::Float(v)),
        ExprEvalResult::Double(v) => Ok(ExprEvalResult::Double(v)),
        v => unreachable!("UnaryPlus: unexpected type combination {:?}", v),
      }
    },
    Expression::UnaryMinus(ref child) => {
      match expr_eval(child, row)? {
        ExprEvalResult::Null => Ok(ExprEvalResult::Null),
        ExprEvalResult::Int(v) => {
          match v.checked_neg() {
            Some(value) => Ok(ExprEvalResult::Int(value)),
            None => Err(Error::SQLExecutionError(format!("Int -({}) out of range", v))),
          }
        },
        ExprEvalResult::BigInt(v) => {
          match v.checked_neg() {
            Some(value) => Ok(ExprEvalResult::BigInt(value)),
            None => Err(Error::SQLExecutionError(format!("BigInt -({}) out of range", v))),
          }
        },
        ExprEvalResult::Float(v) => Ok(ExprEvalResult::Float(-v)),
        ExprEvalResult::Double(v) => Ok(ExprEvalResult::Double(-v)),
        v => unreachable!("UnaryMinus: unexpected type combination {:?}", v),
      }
    },
  }
}

pub enum RowIter {
  EmptyIter,
  FromVecIter { rows: Vec<Row> },
  FilterIter { is_stopped: bool, expr: Rc<Expression>, parent: Box<RowIter> },
  LimitIter { is_stopped: bool, limit: usize, parent: Box<RowIter> },
  ProjectIter { is_stopped: bool, exprs: Rc<Vec<Expression>>, parent: Box<RowIter> },
  ScanIter { num_fields: usize, iter: BTreeIter },
}

impl RowIter {
  // Returns an empty iterator.
  #[inline]
  fn empty() -> Self {
    Self::EmptyIter
  }

  // Returns an iterator from the vector of rows.
  #[inline]
  fn from_vec(mut rows: Vec<Row>) -> Self {
    rows.reverse();
    Self::FromVecIter { rows: rows }
  }

  // Returns an iterator that yields only rows for which `expr` evaluates to true.
  fn filter(expr: Rc<Expression>, plan: RowIter) -> Self {
    Self::FilterIter { is_stopped: false, expr, parent: Box::new(plan) }
  }

  // Returns an iterator that projects each row from `parent` through `exprs`.
  fn project(exprs: Rc<Vec<Expression>>, plan: RowIter) -> Self {
    Self::ProjectIter { is_stopped: false, exprs, parent: Box::new(plan) }
  }

  // Returns an iterator that is limited to `limit` rows from the `parent`.
  #[inline]
  fn limit(limit: usize, plan: RowIter) -> Self {
    Self::LimitIter { is_stopped: false, limit: limit, parent: Box::new(plan) }
  }
}

impl Iterator for RowIter {
  type Item = Res<Row>;

  fn next(&mut self) -> Option<Self::Item> {
    match self {
      RowIter::EmptyIter => None,
      RowIter::FromVecIter { rows } => rows.pop().map(Ok),
      RowIter::FilterIter { ref mut is_stopped, ref expr, parent } => {
        while !*is_stopped {
          match parent.next() {
            Some(Ok(row)) => {
              match expr_eval(expr.as_ref(), &row) {
                Ok(ExprEvalResult::Bool(true)) => {
                  return Some(Ok(row));
                },
                Ok(ExprEvalResult::Bool(false)) => {
                  continue;
                },
                Ok(res) => {
                  unreachable!("FilterIter: unexpected eval result {:?}", res)
                },
                Err(err) => {
                  *is_stopped = true;
                  return Some(Err(err));
                },
              }
            },
            Some(Err(err)) => {
              *is_stopped = true;
              return Some(Err(err));
            }
            None => {
              return None;
            }
          }
        }

        None
      },
      RowIter::LimitIter { ref mut is_stopped, ref mut limit, parent } => {
        if *limit > 0 && !*is_stopped {
          *limit -= 1;
          let row = parent.next();
          if let Some(Err(_)) = row {
            *is_stopped = true;
          }
          row
        } else {
          None
        }
      },
      RowIter::ProjectIter { ref mut is_stopped, ref exprs, parent } => {
        if *is_stopped {
          return None;
        }
        match parent.next() {
          Some(Ok(row)) => {
            let mut out = Row::new(exprs.len());
            for (i, expr) in exprs.iter().enumerate() {
              match expr_eval(expr, &row) {
                Ok(ExprEvalResult::Null) => out.set_null(i, true),
                Ok(ExprEvalResult::Bool(v)) => out.set_bool(i, v),
                Ok(ExprEvalResult::Int(v)) => out.set_i32(i, v),
                Ok(ExprEvalResult::BigInt(v)) => out.set_i64(i, v),
                Ok(ExprEvalResult::Float(v)) => out.set_f32(i, v),
                Ok(ExprEvalResult::Double(v)) => out.set_f64(i, v),
                Ok(ExprEvalResult::Text(v)) => out.set_str(i, &v),
                Err(err) => {
                  *is_stopped = true;
                  return Some(Err(err));
                },
              }
            }
            Some(Ok(out))
          },
          Some(Err(err)) => {
            *is_stopped = true;
            Some(Err(err))
          },
          None => None,
        }
      },
      RowIter::ScanIter { num_fields, iter } => {
        iter.next().map(|(_key, data)| Ok(Row::from_buf(*num_fields, data)))
      },
    }
  }
}

impl FusedIterator for RowIter {}

// Executes a system view scan and returns rows built from catalog metadata.
fn scan_system_view(txn: &TransactionRef, view_name: &str) -> Res<RowIter> {
  match view_name {
    INFORMATION_SCHEMA_SCHEMATA => {
      let rows = catalog::list_schemas(txn)?
        .map(|schema| {
          let mut row = Row::new(1);
          row.set_str(0, schema.schema_name());
          row
        })
        .collect();
      Ok(RowIter::from_vec(rows))
    },
    INFORMATION_SCHEMA_RELATIONS => {
      let mut rows = Vec::new();
      for schema in catalog::list_schemas(txn)? {
        let (_, relations) = catalog::list_relations(txn, schema.schema_name())?;
        for relation in relations {
          let mut row = Row::new(3);
          row.set_str(0, schema.schema_name());
          row.set_str(1, relation.relation_name());
          row.set_str(2, match relation.relation_type() {
            RelationType::TABLE => "TABLE",
            RelationType::SYSTEM_VIEW => "SYSTEM VIEW",
          });
          rows.push(row);
        }
      }
      Ok(RowIter::from_vec(rows))
    },
    INFORMATION_SCHEMA_COLUMNS => {
      let mut rows = Vec::new();
      for schema in catalog::list_schemas(txn)? {
        let (_, relations) = catalog::list_relations(txn, schema.schema_name())?;
        for relation in relations {
          for field in relation.relation_fields().get() {
            let mut row = Row::new(5);
            row.set_str(0, schema.schema_name());
            row.set_str(1, relation.relation_name());
            row.set_str(2, field.name());
            row.set_str(3, &field.data_type().to_string());
            row.set_str(4, if field.nullable() { "YES" } else { "NO" });
            rows.push(row);
          }
        }
      }
      Ok(RowIter::from_vec(rows))
    },
    name => unreachable!("Unknown system view: {}", name),
  }
}

// Executes a physical plan inside the given transaction and returns the result
// to the caller via the session.
pub fn execute(session: &Session, txn: &TransactionRef, plan: &PhysicalPlan) -> Res<RowIter> {
  match plan {
    PhysicalPlan::CreateSchema(ref schema_name) => {
      match catalog::create_schema(txn, schema_name.as_ref(), false) {
        Ok(()) => Ok(RowIter::empty()),
        Err(_) => unreachable!("Create schema {}: unexpected error", schema_name),
      }
    },
    PhysicalPlan::CreateTable(ref schema_name, ref table_name, ref fields) => {
      match catalog::create_relation(
        txn,
        schema_name.as_ref(),
        table_name.as_ref(),
        catalog::RelationType::TABLE,
        // TODO: remove clone.
        fields.as_ref().clone(),
        false
      ) {
        Ok(()) => Ok(RowIter::empty()),
        Err(_) => unreachable!("Create table {}: unexpected error", table_name),
      }
    },
    PhysicalPlan::DropSchema(ref schema_info, cascade) => {
      match catalog::drop_schema(txn, schema_info.schema_name(), *cascade, false) {
        Ok(()) => Ok(RowIter::empty()),
        Err(_) => unreachable!("Drop schema {}: unexpected error", schema_info.schema_name()),
      }
    },
    PhysicalPlan::DropTable(ref schema_info, ref table_info) => {
      let schema_name = schema_info.schema_name();
      let table_name = table_info.relation_name();
      match catalog::drop_relation(txn, schema_name, table_name, false) {
        Ok(()) => Ok(RowIter::empty()),
        Err(_) => unreachable!("Drop table {}: unexpected error", table_name),
      }
    },
    PhysicalPlan::Filter(ref expression, ref child) => {
      let child_iter = execute(session, txn, child)?;
      Ok(RowIter::filter(expression.clone(), child_iter))
    },
    PhysicalPlan::InsertInto(_, ref table_info, ref col_positions, ref query) => {
      let mut child_iter = execute(session, txn, query)?;
      let mut set = match catalog::get_relation_data(txn, table_info) {
        Some(set) => set,
        None => catalog::create_relation_data(txn, table_info)?,
      };
      let table_fields = table_info.relation_fields();
      let num_table_fields = table_fields.get().len();

      while let Some(result) = child_iter.next() {
        let src = result?;
        let mut dst = Row::new(num_table_fields);
        for (i, &pos) in col_positions.iter().enumerate() {
          if !src.is_null(i) {
            match table_fields.get()[pos].data_type() {
              Type::BOOL => dst.set_bool(pos, src.get_bool(i)),
              Type::INT => dst.set_i32(pos, src.get_i32(i)),
              Type::BIGINT => dst.set_i64(pos, src.get_i64(i)),
              Type::FLOAT => dst.set_f32(pos, src.get_f32(i)),
              Type::DOUBLE => dst.set_f64(pos, src.get_f64(i)),
              Type::TEXT => dst.set_str(pos, src.get_str(i)),
              Type::NULL => {},
              Type::STRUCT(_) => unreachable!("InsertInto: STRUCT fields are not supported"),
            }
          }
        }
        let key = u64_u8!(next_object_id(txn));
        set.put(&key, &dst.to_vec());
      }

      Ok(RowIter::empty())
    },
    PhysicalPlan::Limit(ref limit, ref child) => {
      let child_iter = execute(session, txn, child)?;
      Ok(RowIter::limit(*limit, child_iter))
    },
    PhysicalPlan::LocalRelation(ref expressions) => {
      let empty_row = Row::new(0);
      let mut rows = Vec::with_capacity(expressions.len());
      for row_exprs in expressions.as_ref() {
        let mut row = Row::new(row_exprs.len());
        for (i, expr) in row_exprs.iter().enumerate() {
          match expr_eval(expr, &empty_row)? {
            ExprEvalResult::Null => row.set_null(i, true),
            ExprEvalResult::Bool(v) => row.set_bool(i, v),
            ExprEvalResult::Int(v) => row.set_i32(i, v),
            ExprEvalResult::BigInt(v) => row.set_i64(i, v),
            ExprEvalResult::Float(v) => row.set_f32(i, v),
            ExprEvalResult::Double(v) => row.set_f64(i, v),
            ExprEvalResult::Text(v) => row.set_str(i, &v),
          }
        }
        rows.push(row);
      }
      Ok(RowIter::from_vec(rows))
    },
    PhysicalPlan::Project(ref expressions, ref child) => {
      let child_iter = execute(session, txn, child)?;
      Ok(RowIter::project(expressions.clone(), child_iter))
    },
    PhysicalPlan::SeqScan(ref _schema_info, ref table_info) => {
      match table_info.relation_type() {
        RelationType::SYSTEM_VIEW => scan_system_view(txn, table_info.relation_name()),
        RelationType::TABLE => match catalog::get_relation_data(&txn, table_info) {
          Some(mut set) => {
            let num_fields = table_info.relation_fields().len();
            let iter = set.list(None, None);
            Ok(RowIter::ScanIter { num_fields, iter })
          },
          None => Ok(RowIter::empty()),
        },
      }
    },
  }
}

#[cfg(test)]
mod tests {
  use std::rc::Rc;
  use super::{ExprEvalResult, RowIter, execute, expr_eval};
  use crate::common::error::Error;
  use crate::sql::catalog::{
    self,
    RelationInfo,
    RelationType,
    SchemaInfo,
    INFORMATION_SCHEMA,
    INFORMATION_SCHEMA_RELATIONS,
    INFORMATION_SCHEMA_SCHEMATA,
  };
  use crate::sql::plan::{Expression, PhysicalPlan, dsl::*};
  use crate::sql::row::Row;
  use crate::sql::session::Session;
  use crate::sql::types::{Field, Fields, Type};
  use crate::storage::db;

  // Convenience: evaluate a literal-only expression against an empty row.
  fn eval(expr: Expression) -> ExprEvalResult {
    expr_eval(&expr, &Row::new(0)).unwrap()
  }

  fn eval_err(expr: Expression) -> Error {
    expr_eval(&expr, &Row::new(0)).unwrap_err()
  }

  // Build a RelationInfo with the given fields for ColumnRef tests.
  fn make_table(fields: Vec<Field>) -> Rc<RelationInfo> {
    Rc::new(RelationInfo::new(0, 0, "t".to_string(), RelationType::TABLE, Fields::new(fields)))
  }

  fn col_ref(table: Rc<RelationInfo>, idx: usize) -> crate::sql::plan::Expression {
    let schema = Rc::new(SchemaInfo::new(0, "default".to_string()));
    Expression::ColumnRef(schema, table, Some(Rc::new("col".to_string())), idx)
  }

  //==========
  // Literals
  //==========

  #[test]
  fn test_literal_null() {
    assert_eq!(eval(null()), ExprEvalResult::Null);
  }

  #[test]
  fn test_literal_bool() {
    assert_eq!(eval(boolean(true)),  ExprEvalResult::Bool(true));
    assert_eq!(eval(boolean(false)), ExprEvalResult::Bool(false));
  }

  #[test]
  fn test_literal_int() {
    assert_eq!(eval(int(42)),  ExprEvalResult::Int(42));
    assert_eq!(eval(int(-1)), ExprEvalResult::Int(-1));
  }

  #[test]
  fn test_literal_bigint() {
    assert_eq!(eval(bigint(i64::MAX)), ExprEvalResult::BigInt(i64::MAX));
  }

  #[test]
  fn test_literal_float() {
    assert_eq!(eval(float(1.5)), ExprEvalResult::Float(1.5));
  }

  #[test]
  fn test_literal_double() {
    assert_eq!(eval(double(3.14)), ExprEvalResult::Double(3.14));
  }

  #[test]
  fn test_literal_string() {
    assert_eq!(eval(string("hello")), ExprEvalResult::Text("hello".to_string()));
  }

  //=======
  // Alias
  //=======

  #[test]
  fn test_alias_passthrough() {
    assert_eq!(eval(alias(int(7), "x")), ExprEvalResult::Int(7));
  }

  //===========
  // ColumnRef
  //===========

  #[test]
  fn test_column_ref_non_null() {
    let table = make_table(vec![
      Field::new("a".to_string(), Type::INT,    false),
      Field::new("b".to_string(), Type::TEXT,   false),
      Field::new("c".to_string(), Type::BIGINT, false),
      Field::new("d".to_string(), Type::BOOL,   false),
      Field::new("e".to_string(), Type::FLOAT,  false),
      Field::new("f".to_string(), Type::DOUBLE, false),
    ]);
    let mut row = Row::new(6);
    row.set_i32(0, 99);
    row.set_str(1, "hi");
    row.set_i64(2, 12345678901);
    row.set_bool(3, true);
    row.set_f32(4, 2.5);
    row.set_f64(5, 9.9);

    assert_eq!(expr_eval(&col_ref(table.clone(), 0), &row).unwrap(), ExprEvalResult::Int(99));
    assert_eq!(
      expr_eval(&col_ref(table.clone(), 1), &row).unwrap(),
      ExprEvalResult::Text("hi".to_string())
    );
    assert_eq!(
      expr_eval(&col_ref(table.clone(), 2), &row).unwrap(),
      ExprEvalResult::BigInt(12345678901)
    );
    assert_eq!(expr_eval(&col_ref(table.clone(), 3), &row).unwrap(), ExprEvalResult::Bool(true));
    assert_eq!(expr_eval(&col_ref(table.clone(), 4), &row).unwrap(), ExprEvalResult::Float(2.5));
    assert_eq!(expr_eval(&col_ref(table.clone(), 5), &row).unwrap(), ExprEvalResult::Double(9.9));
  }

  #[test]
  fn test_column_ref_null() {
    let table = make_table(vec![Field::new("a".to_string(), Type::INT, true)]);
    let mut row = Row::new(1);
    row.set_null(0, true);
    assert_eq!(expr_eval(&col_ref(table, 0), &row).unwrap(), ExprEvalResult::Null);
  }

  //============
  // Arithmetic
  //============

  #[test]
  fn test_add_int() {
    assert_eq!(eval(add(int(3), int(4))), ExprEvalResult::Int(7));
  }

  #[test]
  fn test_add_int_overflow() {
    let err = eval_err(add(int(i32::MAX), int(1)));
    assert!(matches!(err, Error::SQLExecutionError(_)));
  }

  #[test]
  fn test_add_null_propagation() {
    assert_eq!(eval(add(null(), int(1))), ExprEvalResult::Null);
    assert_eq!(eval(add(int(1), null())), ExprEvalResult::Null);
  }

  #[test]
  fn test_subtract_int() {
    assert_eq!(eval(subtract(int(10), int(3))), ExprEvalResult::Int(7));
  }

  #[test]
  fn test_subtract_int_overflow() {
    let err = eval_err(subtract(int(i32::MIN), int(1)));
    assert!(matches!(err, Error::SQLExecutionError(_)));
  }

  #[test]
  fn test_multiply_int() {
    assert_eq!(eval(multiply(int(6), int(7))), ExprEvalResult::Int(42));
  }

  #[test]
  fn test_multiply_int_overflow() {
    let err = eval_err(multiply(int(i32::MAX), int(2)));
    assert!(matches!(err, Error::SQLExecutionError(_)));
  }

  #[test]
  fn test_divide_int() {
    assert_eq!(eval(divide(int(7), int(2))), ExprEvalResult::Int(3));  // truncates
    assert_eq!(eval(divide(int(-7), int(2))), ExprEvalResult::Int(-3)); // toward zero
  }

  #[test]
  fn test_divide_int_by_zero() {
    let err = eval_err(divide(int(1), int(0)));
    assert!(matches!(err, Error::SQLExecutionError(_)));
  }

  #[test]
  fn test_divide_float_by_zero() {
    let err = eval_err(divide(float(1.0), float(0.0)));
    assert!(matches!(err, Error::SQLExecutionError(_)));
  }

  #[test]
  fn test_divide_double_by_zero() {
    let err = eval_err(divide(double(1.0), double(0.0)));
    assert!(matches!(err, Error::SQLExecutionError(_)));
  }

  #[test]
  fn test_unary_minus_int() {
    assert_eq!(eval(Expression::UnaryMinus(Rc::new(int(5)))), ExprEvalResult::Int(-5));
  }

  #[test]
  fn test_unary_minus_int_overflow() {
    let err = eval_err(Expression::UnaryMinus(Rc::new(int(i32::MIN))));
    assert!(matches!(err, Error::SQLExecutionError(_)));
  }

  //=============
  // Comparisons
  //=============

  #[test]
  fn test_equals_int() {
    assert_eq!(eval(equals(int(1), int(1))), ExprEvalResult::Bool(true));
    assert_eq!(eval(equals(int(1), int(2))), ExprEvalResult::Bool(false));
  }

  #[test]
  fn test_equals_null_propagation() {
    assert_eq!(eval(equals(null(), int(1))), ExprEvalResult::Null);
  }

  #[test]
  fn test_not_equals_int() {
    assert_eq!(eval(not_equals(int(1), int(2))), ExprEvalResult::Bool(true));
    assert_eq!(eval(not_equals(int(1), int(1))), ExprEvalResult::Bool(false));
  }

  #[test]
  fn test_less_than_int() {
    assert_eq!(eval(less_than(int(1), int(2))), ExprEvalResult::Bool(true));
    assert_eq!(eval(less_than(int(2), int(1))), ExprEvalResult::Bool(false));
    assert_eq!(eval(less_than(int(1), int(1))), ExprEvalResult::Bool(false));
  }

  #[test]
  fn test_less_than_equals_int() {
    assert_eq!(eval(less_than_equals(int(1), int(1))), ExprEvalResult::Bool(true));
    assert_eq!(eval(less_than_equals(int(2), int(1))), ExprEvalResult::Bool(false));
  }

  #[test]
  fn test_greater_than_int() {
    assert_eq!(eval(greater_than(int(2), int(1))), ExprEvalResult::Bool(true));
    assert_eq!(eval(greater_than(int(1), int(2))), ExprEvalResult::Bool(false));
  }

  #[test]
  fn test_greater_than_equals_int() {
    assert_eq!(eval(greater_than_equals(int(1), int(1))), ExprEvalResult::Bool(true));
    assert_eq!(eval(greater_than_equals(int(1), int(2))), ExprEvalResult::Bool(false));
  }

  // NaN semantics (PostgreSQL: NaN = NaN, NaN > all non-NaN)
  #[test]
  fn test_nan_equals_nan() {
    let nan = float(f32::NAN);
    assert_eq!(eval(equals(nan.clone(), nan.clone())), ExprEvalResult::Bool(true));
    assert_eq!(eval(not_equals(nan.clone(), nan.clone())), ExprEvalResult::Bool(false));
  }

  #[test]
  fn test_nan_greater_than_non_nan() {
    let nan = float(f32::NAN);
    assert_eq!(eval(greater_than(nan.clone(), float(1e30))), ExprEvalResult::Bool(true));
    assert_eq!(eval(less_than(float(1e30), nan.clone())), ExprEvalResult::Bool(true));
    assert_eq!(eval(greater_than(nan.clone(), nan.clone())), ExprEvalResult::Bool(false));
    assert_eq!(eval(greater_than_equals(nan.clone(), nan.clone())), ExprEvalResult::Bool(true));
  }

  //=========
  // Logical
  //=========

  #[test]
  fn test_and() {
    assert_eq!(eval(and(boolean(true),  boolean(true))),  ExprEvalResult::Bool(true));
    assert_eq!(eval(and(boolean(true),  boolean(false))), ExprEvalResult::Bool(false));
    assert_eq!(eval(and(boolean(false), boolean(true))),  ExprEvalResult::Bool(false));
    // FALSE AND NULL = FALSE (short-circuit)
    assert_eq!(eval(and(boolean(false), null())), ExprEvalResult::Bool(false));
    assert_eq!(eval(and(null(), boolean(false))), ExprEvalResult::Bool(false));
    // TRUE AND NULL = NULL
    assert_eq!(eval(and(boolean(true), null())), ExprEvalResult::Null);
  }

  #[test]
  fn test_or() {
    assert_eq!(eval(or(boolean(false), boolean(false))), ExprEvalResult::Bool(false));
    assert_eq!(eval(or(boolean(true),  boolean(false))), ExprEvalResult::Bool(true));
    // TRUE OR NULL = TRUE (short-circuit)
    assert_eq!(eval(or(boolean(true), null())), ExprEvalResult::Bool(true));
    assert_eq!(eval(or(null(), boolean(true))), ExprEvalResult::Bool(true));
    // FALSE OR NULL = NULL
    assert_eq!(eval(or(boolean(false), null())), ExprEvalResult::Null);
  }

  #[test]
  fn test_not() {
    assert_eq!(eval(not(boolean(true))),  ExprEvalResult::Bool(false));
    assert_eq!(eval(not(boolean(false))), ExprEvalResult::Bool(true));
    assert_eq!(eval(not(null())), ExprEvalResult::Null);
  }

  //=======================
  // IS NULL / IS NOT NULL
  //=======================

  #[test]
  fn test_is_null() {
    assert_eq!(eval(is_null(null())),    ExprEvalResult::Bool(true));
    assert_eq!(eval(is_null(int(1))),    ExprEvalResult::Bool(false));
    assert_eq!(eval(is_null(boolean(false))), ExprEvalResult::Bool(false));
  }

  #[test]
  fn test_is_not_null() {
    assert_eq!(eval(is_not_null(null())),  ExprEvalResult::Bool(false));
    assert_eq!(eval(is_not_null(int(1))),  ExprEvalResult::Bool(true));
  }

  //======================
  // String concatenation
  //======================

  #[test]
  fn test_concat() {
    assert_eq!(
      eval(concat(string("foo"), string("bar"))),
      ExprEvalResult::Text("foobar".to_string())
    );
  }

  #[test]
  fn test_concat_null_propagation() {
    assert_eq!(eval(concat(null(), string("x"))), ExprEvalResult::Null);
  }

  //======
  // Cast
  //======

  #[test]
  fn test_cast_int_to_bigint() {
    assert_eq!(eval(cast(int(42), Type::BIGINT)), ExprEvalResult::BigInt(42));
  }

  #[test]
  fn test_cast_bigint_to_int_ok() {
    assert_eq!(eval(cast(bigint(100), Type::INT)), ExprEvalResult::Int(100));
  }

  #[test]
  fn test_cast_bigint_to_int_overflow() {
    let err = eval_err(cast(bigint(i64::MAX), Type::INT));
    assert!(matches!(err, Error::SQLExecutionError(_)));
  }

  #[test]
  fn test_cast_int_to_text() {
    assert_eq!(eval(cast(int(7), Type::TEXT)), ExprEvalResult::Text("7".to_string()));
  }

  #[test]
  fn test_cast_bool_to_text() {
    assert_eq!(eval(cast(boolean(true), Type::TEXT)),  ExprEvalResult::Text("true".to_string()));
    assert_eq!(eval(cast(boolean(false), Type::TEXT)), ExprEvalResult::Text("false".to_string()));
  }

  #[test]
  fn test_cast_text_to_int_ok() {
    assert_eq!(eval(cast(string("42"), Type::INT)), ExprEvalResult::Int(42));
  }

  #[test]
  fn test_cast_text_to_int_invalid() {
    let err = eval_err(cast(string("abc"), Type::INT));
    assert!(matches!(err, Error::SQLExecutionError(_)));
  }

  #[test]
  fn test_cast_text_to_bool_ok() {
    assert_eq!(eval(cast(string("true"),  Type::BOOL)), ExprEvalResult::Bool(true));
    assert_eq!(eval(cast(string("false"), Type::BOOL)), ExprEvalResult::Bool(false));
    // case-insensitive
    assert_eq!(eval(cast(string("TRUE"),  Type::BOOL)), ExprEvalResult::Bool(true));
    assert_eq!(eval(cast(string("FaLsE"),  Type::BOOL)), ExprEvalResult::Bool(false));
  }

  #[test]
  fn test_cast_text_to_bool_invalid() {
    let err = eval_err(cast(string("yes"), Type::BOOL));
    assert!(matches!(err, Error::SQLExecutionError(_)));
  }

  #[test]
  fn test_cast_float_to_int_out_of_range() {
    let err = eval_err(cast(float(f32::INFINITY), Type::INT));
    assert!(matches!(err, Error::SQLExecutionError(_)));
  }

  #[test]
  fn test_cast_null_passthrough() {
    assert_eq!(eval(cast(null(), Type::INT)),  ExprEvalResult::Null);
    assert_eq!(eval(cast(null(), Type::TEXT)), ExprEvalResult::Null);
  }

  //=========
  // RowIter
  //=========

  fn int_row(value: i32) -> Row {
    let mut row = Row::new(1);
    row.set_i32(0, value);
    row
  }

  fn row_val(result: Option<Result<Row, Error>>) -> i32 {
    result.unwrap().unwrap().get_i32(0)
  }

  // An iterator that yields one error (division by zero on the first row).
  fn error_iter() -> RowIter {
    RowIter::filter(
      Rc::new(divide(int(1), int(0))),
      RowIter::from_vec(vec![int_row(1)]),
    )
  }

  #[test]
  fn test_row_iter_empty() {
    let mut iter = RowIter::empty();
    assert!(iter.next().is_none());
    assert!(iter.next().is_none()); // stays None (fused)
  }

  #[test]
  fn test_row_iter_from_vec_empty() {
    let mut iter = RowIter::from_vec(vec![]);
    assert!(iter.next().is_none());
  }

  #[test]
  fn test_row_iter_from_vec_preserves_order() {
    let mut iter = RowIter::from_vec(vec![int_row(1), int_row(2), int_row(3)]);
    assert_eq!(row_val(iter.next()), 1);
    assert_eq!(row_val(iter.next()), 2);
    assert_eq!(row_val(iter.next()), 3);
    assert!(iter.next().is_none());
  }

  #[test]
  fn test_row_iter_filter_all_pass() {
    let mut iter = RowIter::filter(
      Rc::new(boolean(true)),
      RowIter::from_vec(vec![int_row(1), int_row(2)]),
    );
    assert_eq!(row_val(iter.next()), 1);
    assert_eq!(row_val(iter.next()), 2);
    assert!(iter.next().is_none());
  }

  #[test]
  fn test_row_iter_filter_none_pass() {
    let mut iter = RowIter::filter(
      Rc::new(boolean(false)),
      RowIter::from_vec(vec![int_row(1), int_row(2)]),
    );
    assert!(iter.next().is_none());
  }

  #[test]
  fn test_row_iter_filter_partial() {
    let table = make_table(vec![Field::new("a".to_string(), Type::INT, false)]);
    let expr = equals(col_ref(table, 0), int(2));
    let mut iter = RowIter::filter(
      Rc::new(expr),
      RowIter::from_vec(vec![int_row(1), int_row(2), int_row(3)]),
    );
    assert_eq!(row_val(iter.next()), 2);
    assert!(iter.next().is_none());
  }

  #[test]
  fn test_row_iter_filter_stops_after_error() {
    let mut iter = RowIter::filter(
      Rc::new(divide(int(1), int(0))),
      RowIter::from_vec(vec![int_row(1), int_row(2)]),
    );
    assert!(matches!(iter.next(), Some(Err(Error::SQLExecutionError(_)))));
    assert!(iter.next().is_none());
  }

  #[test]
  fn test_row_iter_filter_propagates_parent_error() {
    let mut iter = RowIter::filter(Rc::new(boolean(true)), error_iter());
    assert!(matches!(iter.next(), Some(Err(Error::SQLExecutionError(_)))));
    assert!(iter.next().is_none());
  }

  #[test]
  fn test_row_iter_limit_basic() {
    let mut iter = RowIter::limit(2, RowIter::from_vec(vec![int_row(1), int_row(2), int_row(3)]));
    assert_eq!(row_val(iter.next()), 1);
    assert_eq!(row_val(iter.next()), 2);
    assert!(iter.next().is_none());
  }

  #[test]
  fn test_row_iter_limit_zero() {
    let mut iter = RowIter::limit(0, RowIter::from_vec(vec![int_row(1)]));
    assert!(iter.next().is_none());
  }

  #[test]
  fn test_row_iter_limit_exceeds_rows() {
    let mut iter = RowIter::limit(10, RowIter::from_vec(vec![int_row(1), int_row(2)]));
    assert_eq!(row_val(iter.next()), 1);
    assert_eq!(row_val(iter.next()), 2);
    assert!(iter.next().is_none());
  }

  #[test]
  fn test_row_iter_limit_stops_after_error() {
    let mut iter = RowIter::limit(5, error_iter());
    assert!(matches!(iter.next(), Some(Err(Error::SQLExecutionError(_)))));
    assert!(iter.next().is_none());
  }

  //=========
  // execute
  //=========

  fn init_db() -> db::DB {
    let mut dbc = db::open(None).try_build().unwrap();
    dbc.with_txn(true, |txn| {
      catalog::init_catalog(&txn).unwrap();
      catalog::create_schema(&txn, "default", false).unwrap();
    });
    dbc
  }

  fn setup_table(dbc: &mut db::DB, table: &str, cols: &[(&str, Type)]) {
    let fields = Fields::new(
      cols.iter().map(|(name, tpe)| Field::new(name.to_string(), tpe.clone(), true)).collect()
    );
    dbc.with_txn(true, |txn| {
      catalog::create_relation(&txn, "default", table, RelationType::TABLE, fields.clone(), false)
        .unwrap();
    });
  }

  fn collect_rows(iter: RowIter) -> Vec<Row> {
    iter.map(|r| r.unwrap()).collect()
  }

  #[test]
  fn test_exec_create_schema() {
    let mut dbc = init_db();
    dbc.with_txn(true, |txn| {
      let plan = PhysicalPlan::CreateSchema(Rc::new("s".to_string()));
      let rows = collect_rows(execute(&Session::builder().build(), &txn, &plan).unwrap());
      assert!(rows.is_empty());
      assert!(catalog::get_schema(&txn, "s").is_ok());
    });
  }

  #[test]
  fn test_exec_create_table() {
    let mut dbc = init_db();
    dbc.with_txn(true, |txn| {
      let fields = Rc::new(Fields::new(vec![Field::new("a".to_string(), Type::INT, true)]));
      let plan = PhysicalPlan::CreateTable(
        Rc::new("default".to_string()), Rc::new("t".to_string()), fields
      );
      let rows = collect_rows(execute(&Session::builder().build(), &txn, &plan).unwrap());
      assert!(rows.is_empty());
      assert!(catalog::get_relation(&txn, "default", "t").is_ok());
    });
  }

  #[test]
  fn test_exec_drop_schema() {
    let mut dbc = init_db();
    dbc.with_txn(true, |txn| {
      catalog::create_schema(&txn, "todelete", false).unwrap();
    });
    dbc.with_txn(true, |txn| {
      let schema_info = Rc::new(catalog::get_schema(&txn, "todelete").unwrap());
      let plan = PhysicalPlan::DropSchema(schema_info, false);
      let rows = collect_rows(execute(&Session::builder().build(), &txn, &plan).unwrap());
      assert!(rows.is_empty());
      assert!(catalog::get_schema(&txn, "todelete").is_err());
    });
  }

  #[test]
  fn test_exec_drop_table() {
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT)]);
    dbc.with_txn(true, |txn| {
      let (schema_info, table_info) = catalog::get_relation(&txn, "default", "t").unwrap();
      let plan = PhysicalPlan::DropTable(Rc::new(schema_info), Rc::new(table_info));
      let rows = collect_rows(execute(&Session::builder().build(), &txn, &plan).unwrap());
      assert!(rows.is_empty());
      assert!(catalog::get_relation(&txn, "default", "t").is_err());
    });
  }

  #[test]
  fn test_exec_local_relation() {
    let mut dbc = init_db();
    let rows = dbc.with_txn(false, |txn| {
      let plan = PhysicalPlan::LocalRelation(Rc::new(vec![
        vec![int(1), string("hello")],
        vec![int(2), string("world")],
      ]));
      collect_rows(execute(&Session::builder().build(), &txn, &plan).unwrap())
    });
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[0].get_i32(0), 1);
    assert_eq!(rows[0].get_str(1), "hello");
    assert_eq!(rows[1].get_i32(0), 2);
    assert_eq!(rows[1].get_str(1), "world");
  }

  #[test]
  fn test_exec_local_relation_empty() {
    let mut dbc = init_db();
    let rows = dbc.with_txn(false, |txn| {
      collect_rows(
        execute(
          &Session::builder().build(),
          &txn,
          &PhysicalPlan::LocalRelation(Rc::new(vec![]))
        ).unwrap()
      )
    });
    assert!(rows.is_empty());
  }

  #[test]
  fn test_exec_filter_passes_all() {
    let mut dbc = init_db();
    let rows = dbc.with_txn(false, |txn| {
      let source = PhysicalPlan::LocalRelation(Rc::new(vec![vec![int(1)], vec![int(2)]]));
      let plan = PhysicalPlan::Filter(Rc::new(boolean(true)), Rc::new(source));
      collect_rows(execute(&Session::builder().build(), &txn, &plan).unwrap())
    });
    assert_eq!(rows.len(), 2);
  }

  #[test]
  fn test_exec_filter_blocks_all() {
    let mut dbc = init_db();
    let rows = dbc.with_txn(false, |txn| {
      let source = PhysicalPlan::LocalRelation(Rc::new(vec![vec![int(1)], vec![int(2)]]));
      let plan = PhysicalPlan::Filter(Rc::new(boolean(false)), Rc::new(source));
      collect_rows(execute(&Session::builder().build(), &txn, &plan).unwrap())
    });
    assert!(rows.is_empty());
  }

  #[test]
  fn test_exec_filter_by_column_value() {
    let mut dbc = init_db();
    let table = make_table(vec![Field::new("a".to_string(), Type::INT, false)]);
    let rows = dbc.with_txn(false, |txn| {
      let source = PhysicalPlan::LocalRelation(Rc::new(vec![
        vec![int(1)], vec![int(2)], vec![int(3)],
      ]));
      let plan = PhysicalPlan::Filter(
        Rc::new(equals(col_ref(table.clone(), 0), int(2))),
        Rc::new(source),
      );
      collect_rows(execute(&Session::builder().build(), &txn, &plan).unwrap())
    });
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].get_i32(0), 2);
  }

  #[test]
  fn test_exec_limit() {
    let mut dbc = init_db();
    let rows = dbc.with_txn(false, |txn| {
      let source = PhysicalPlan::LocalRelation(Rc::new(vec![
        vec![int(1)], vec![int(2)], vec![int(3)],
      ]));
      let plan = PhysicalPlan::Limit(2, Rc::new(source));
      collect_rows(execute(&Session::builder().build(), &txn, &plan).unwrap())
    });
    assert_eq!(rows.len(), 2);
  }

  #[test]
  fn test_exec_limit_zero() {
    let mut dbc = init_db();
    let rows = dbc.with_txn(false, |txn| {
      let source = PhysicalPlan::LocalRelation(Rc::new(vec![vec![int(1)]]));
      let plan = PhysicalPlan::Limit(0, Rc::new(source));
      collect_rows(execute(&Session::builder().build(), &txn, &plan).unwrap())
    });
    assert!(rows.is_empty());
  }

  #[test]
  fn test_exec_project() {
    let mut dbc = init_db();
    let table = make_table(vec![
      Field::new("a".to_string(), Type::INT, false),
      Field::new("b".to_string(), Type::INT, false),
    ]);
    let rows = dbc.with_txn(false, |txn| {
      // Source rows have 2 columns; project swaps their order.
      let source = PhysicalPlan::LocalRelation(Rc::new(vec![vec![int(1), int(2)]]));
      let plan = PhysicalPlan::Project(
        Rc::new(vec![col_ref(table.clone(), 1), col_ref(table.clone(), 0)]),
        Rc::new(source),
      );
      collect_rows(execute(&Session::builder().build(), &txn, &plan).unwrap())
    });
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].get_i32(0), 2); // col 1 is now at position 0
    assert_eq!(rows[0].get_i32(1), 1); // col 0 is now at position 1
  }

  #[test]
  fn test_exec_seq_scan_empty_table() {
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT)]);
    let rows = dbc.with_txn(false, |txn| {
      let (schema_info, table_info) = catalog::get_relation(&txn, "default", "t").unwrap();
      let plan = PhysicalPlan::SeqScan(Rc::new(schema_info), Rc::new(table_info));
      collect_rows(execute(&Session::builder().build(), &txn, &plan).unwrap())
    });
    assert!(rows.is_empty());
  }

  #[test]
  fn test_exec_insert_into_and_seq_scan() {
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT), ("b", Type::TEXT)]);

    dbc.with_txn(true, |txn| {
      let (schema_info, table_info) = catalog::get_relation(&txn, "default", "t").unwrap();
      let plan = PhysicalPlan::InsertInto(
        Rc::new(schema_info),
        Rc::new(table_info),
        Rc::new(vec![0, 1]),
        Rc::new(PhysicalPlan::LocalRelation(Rc::new(vec![
          vec![int(1), string("hello")],
          vec![int(2), string("world")],
        ]))),
      );
      assert!(collect_rows(execute(&Session::builder().build(), &txn, &plan).unwrap()).is_empty());
    });

    let mut rows = dbc.with_txn(false, |txn| {
      let (schema_info, table_info) = catalog::get_relation(&txn, "default", "t").unwrap();
      let plan = PhysicalPlan::SeqScan(Rc::new(schema_info), Rc::new(table_info));
      collect_rows(execute(&Session::builder().build(), &txn, &plan).unwrap())
    });
    assert_eq!(rows.len(), 2);
    rows.sort_by_key(|r| r.get_i32(0));
    assert_eq!(rows[0].get_i32(0), 1);
    assert_eq!(rows[0].get_str(1), "hello");
    assert_eq!(rows[1].get_i32(0), 2);
    assert_eq!(rows[1].get_str(1), "world");
  }

  #[test]
  fn test_exec_insert_into_with_explicit_col_positions() {
    // Insert into (b, a) order — positions [1, 0] map query col 0 -> table col 1,
    // query col 1 -> table col 0.
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT), ("b", Type::TEXT)]);

    dbc.with_txn(true, |txn| {
      let (schema_info, table_info) = catalog::get_relation(&txn, "default", "t").unwrap();
      let plan = PhysicalPlan::InsertInto(
        Rc::new(schema_info),
        Rc::new(table_info),
        Rc::new(vec![1, 0]), // b first, then a
        Rc::new(PhysicalPlan::LocalRelation(Rc::new(vec![
          vec![string("hello"), int(42)],
        ]))),
      );
      execute(&Session::builder().build(), &txn, &plan).unwrap();
    });

    let rows = dbc.with_txn(false, |txn| {
      let (schema_info, table_info) = catalog::get_relation(&txn, "default", "t").unwrap();
      let plan = PhysicalPlan::SeqScan(Rc::new(schema_info), Rc::new(table_info));
      collect_rows(execute(&Session::builder().build(), &txn, &plan).unwrap())
    });
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].get_i32(0), 42);   // a (table col 0)
    assert_eq!(rows[0].get_str(1), "hello"); // b (table col 1)
  }

  #[test]
  fn test_exec_scan_system_view_schemata() {
    let mut dbc = init_db();
    dbc.with_txn(true, |txn| {
      catalog::create_schema(&txn, "myschema", false).unwrap();
    });
    let rows = dbc.with_txn(false, |txn| {
      let (schema_info, table_info) = catalog::get_relation(
        &txn, INFORMATION_SCHEMA, INFORMATION_SCHEMA_SCHEMATA
      ).unwrap();
      let plan = PhysicalPlan::SeqScan(Rc::new(schema_info), Rc::new(table_info));
      collect_rows(execute(&Session::builder().build(), &txn, &plan).unwrap())
    });
    let names: Vec<&str> = rows.iter().map(|r| r.get_str(0)).collect();
    assert!(names.contains(&INFORMATION_SCHEMA));
    assert!(names.contains(&"default"));
    assert!(names.contains(&"myschema"));
  }

  #[test]
  fn test_exec_scan_system_view_relations() {
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT)]);
    let rows = dbc.with_txn(false, |txn| {
      let (schema_info, table_info) = catalog::get_relation(
        &txn, INFORMATION_SCHEMA, INFORMATION_SCHEMA_RELATIONS
      ).unwrap();
      let plan = PhysicalPlan::SeqScan(Rc::new(schema_info), Rc::new(table_info));
      collect_rows(execute(&Session::builder().build(), &txn, &plan).unwrap())
    });
    // information_schema system views and the user table should all appear.
    let names: Vec<(&str, &str)> = rows.iter().map(|r| (r.get_str(0), r.get_str(1))).collect();
    assert!(names.contains(&(INFORMATION_SCHEMA, INFORMATION_SCHEMA_SCHEMATA)));
    assert!(names.contains(&(INFORMATION_SCHEMA, INFORMATION_SCHEMA_RELATIONS)));
    assert!(names.contains(&("default", "t")));
  }
}
