use std::convert::TryFrom;
use crate::common::error::{Error, Res};
use crate::sql::plan::{Expression, PhysicalPlan};
use crate::sql::row::Row;
use crate::sql::session::Session;
use crate::sql::types::Type;
use crate::storage::txn::TransactionRef;

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
    // NaN = NaN → TRUE; NaN = x → FALSE for all non-NaN x (§8.6).
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

// Executes a physical plan inside the given transaction and returns the result
// to the caller via the session.
pub fn execute(session: &Session, txn: &TransactionRef, plan: PhysicalPlan) -> Res<()> {
  todo!()
}

#[cfg(test)]
mod tests {
  use std::rc::Rc;
  use super::{ExprEvalResult, expr_eval};
  use crate::common::error::Error;
  use crate::sql::catalog::{RelationInfo, RelationType, SchemaInfo};
  use crate::sql::plan::{Expression, dsl::*};
  use crate::sql::row::Row;
  use crate::sql::types::{Field, Fields, Type};

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
}
