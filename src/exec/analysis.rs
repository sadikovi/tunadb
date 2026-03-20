use std::collections::HashSet;
use std::rc::Rc;
use crate::common::error::{Error, Res};
use crate::exec::catalog;
use crate::exec::plan::{
  DEFAULT_SUBQUERY_NAME,
  Expression,
  ExpressionContext,
  LogicalPlan,
  can_cast,
  can_numeric_and_null_upcast,
  promote_arithmetic_type,
};
use crate::exec::session::Session;
use crate::exec::trees;
use crate::exec::types::{Fields, Type};
use crate::storage::txn::TransactionRef;

// Returns the current schema from the schema name or default session schema.
#[inline]
fn current_schema<'a>(session: &'a Session, schema_name: &'a Option<Rc<String>>) -> &'a str {
  schema_name.as_ref().map_or(session.current_schema(), |x| x.as_str())
}

// Asserts if the schema contains only unique column names.
// Recursive and works for structs.
fn assert_unique_fields(fields: &Fields) -> Res<()> {
  let mut set = HashSet::new();

  for field in fields.get() {
    if !set.insert(field.name()) {
      return Err(Error::SQLAnalysisDuplicateField(field.name().to_string()));
    }

    match field.data_type() {
      Type::STRUCT(ref inner_fields) => assert_unique_fields(inner_fields)?,
      _ => {}, // Do nothing.
    }
  }

  Ok(())
}

// Asserts if the field with the provided name exists in the schema.
fn assert_field_exists(fields: &Fields, field_name: &str) -> Res<()> {
  match fields.get_field(field_name) {
    Some(_) => Ok(()),
    None => Err(
      Error::SQLAnalysisUnknownField(
        format!("Unknown field {} in the destination table", field_name)
      )
    ),
  }
}

// Resolves types for a binary comparison by casting one operand to match the other when possible.
fn resolve_types_for_binary_comparison<F>(
  left: &Rc<Expression>,
  right: &Rc<Expression>,
  make: F,
) -> Res<Option<Expression>>
where
  F: FnOnce(Rc<Expression>, Rc<Expression>) -> Expression,
{
  let left_tpe = left.data_type()?;
  let right_tpe = right.data_type()?;

  if left_tpe == right_tpe {
    Ok(None)
  } else if can_numeric_and_null_upcast(&left_tpe, &right_tpe) {
    Ok(
      Some(
        make(
          Rc::new(Expression::Cast(left.clone(), Rc::new(right_tpe))),
          right.clone(),
        )
      )
    )
  } else if can_numeric_and_null_upcast(&right_tpe, &left_tpe) {
    Ok(
      Some(
        make(
          left.clone(),
          Rc::new(Expression::Cast(right.clone(), Rc::new(left_tpe))),
        )
      )
    )
  } else {
    Err(
      Error::SQLAnalysisExpressionDataType(
        format!(
          "Incompatible comparison types {} != {} between {} and {}",
          left_tpe,
          right_tpe,
          trees::plan_output(left.as_ref()),
          trees::plan_output(right.as_ref())
        )
      )
    )
  }
}

// Resolves types for binary arithmetic by casting operands to the promoted type when needed.
fn resolve_types_for_binary_arithmetic<F>(
  left: &Rc<Expression>,
  right: &Rc<Expression>,
  make: F,
) -> Res<Option<Expression>>
where
  F: FnOnce(Rc<Expression>, Rc<Expression>) -> Expression,
{
  let ltpe = left.data_type()?;
  let rtpe = right.data_type()?;

  let result_tpe = match promote_arithmetic_type(&ltpe, &rtpe) {
    Ok(result_tpe) => result_tpe,
    Err(_) => {
      return Err(
        Error::SQLAnalysisExpressionDataType(
          format!(
            "Incompatible arithmetic types {} != {} between {} and {}",
            ltpe,
            rtpe,
            trees::plan_output(left.as_ref()),
            trees::plan_output(right.as_ref())
          )
        )
      )
    },
  };

  if ltpe == result_tpe && rtpe == result_tpe {
    return Ok(None);
  }

  let new_left = if ltpe == result_tpe {
    left.clone()
  } else if ltpe != result_tpe && can_numeric_and_null_upcast(&ltpe, &result_tpe) {
    Rc::new(Expression::Cast(left.clone(), Rc::new(result_tpe.clone())))
  } else {
    return Err(
      Error::SQLAnalysisExpressionDataType(
        format!(
          "Cannot cast {} to {} for {}",
          ltpe,
          result_tpe,
          trees::plan_output(left.as_ref()),
        )
      )
    )
  };

  let new_right = if rtpe == result_tpe {
    right.clone()
  } else if rtpe != result_tpe && can_numeric_and_null_upcast(&rtpe, &result_tpe) {
    Rc::new(Expression::Cast(right.clone(), Rc::new(result_tpe)))
  } else {
    return Err(
      Error::SQLAnalysisExpressionDataType(
        format!(
          "Cannot cast {} to {} for {}",
          rtpe,
          result_tpe,
          trees::plan_output(right.as_ref()),
        )
      )
    )
  };

  Ok(Some(make(new_left, new_right)))
}

//=======================
// Expression resolution
//=======================

enum ExpressionRule<'a> {
  ResolveIdentifiers(&'a [(Rc<ExpressionContext>, Expression)]),
  ResolveTypes,
}

impl<'a> trees::Rule<Expression> for ExpressionRule<'a> {
  fn apply(&self, expr: &Expression) -> Res<Option<Expression>> {
    match self {
      ExpressionRule::ResolveIdentifiers(ref input) => {
        match expr {
          Expression::Identifier(ref parts, _) => {
            let mut identifier_matches = Vec::new();
            for (ctx, input_expr) in *input {
              if ctx.matches_suffix(parts) && input_expr.name() == expr.name() {
                identifier_matches.push(input_expr);
              }
            }

            if identifier_matches.len() == 0 {
              // We could not resolve the identifier.
              Err(
                Error::SQLAnalysisUnresolvedExpression(
                  format!("Unknown expressions found: {:?}", expr)
                )
              )
            } else if identifier_matches.len() == 1 {
              Ok(identifier_matches.pop().cloned())
            } else {
              Err(
                Error::SQLAnalysisUnresolvedExpression(
                  format!("Duplicate expressions found: {:?}", identifier_matches)
                )
              )
            }
          },
          _ => Ok(None),
        }
      },
      ExpressionRule::ResolveTypes => {
        match expr {
          Expression::Add(ref left, ref right) => {
            resolve_types_for_binary_arithmetic(left, right, Expression::Add)
          },
          Expression::Alias(_, _) => Ok(None),
          Expression::And(ref left, ref right) => {
            let left_tpe = left.data_type()?;
            let right_tpe = right.data_type()?;
            if left_tpe != Type::BOOL || right_tpe != Type::BOOL {
              Err(
                Error::SQLAnalysisExpressionDataType(
                  format!("And requires BOOL operands, got {} and {}", left_tpe, right_tpe)
                )
              )
            } else {
              Ok(None)
            }
          },
          Expression::Cast(ref child, ref tpe) => {
            let from_tpe = child.data_type()?;
            if !can_cast(&from_tpe, tpe) {
              Err(
                Error::SQLAnalysisExpressionDataType(
                  format!("Cannot cast {} to {}", from_tpe, tpe)
                )
              )
            } else {
              Ok(None)
            }
          },
          Expression::Concat(ref left, ref right) => {
            let left_tpe = left.data_type()?;
            let right_tpe = right.data_type()?;
            if left_tpe != Type::TEXT || right_tpe != Type::TEXT {
              Err(
                Error::SQLAnalysisExpressionDataType(
                  format!("Concat requires TEXT operands, got {} and {}", left_tpe, right_tpe)
                )
              )
            } else {
              Ok(None)
            }
          },
          Expression::ColumnRef(_, _, _, _) => Ok(None),
          Expression::Divide(ref left, ref right) => {
            resolve_types_for_binary_arithmetic(left, right, Expression::Divide)
          }
          Expression::Equals(ref left, ref right) => {
            resolve_types_for_binary_comparison(left, right, Expression::Equals)
          },
          Expression::GreaterThan(ref left, ref right) => {
            resolve_types_for_binary_comparison(left, right, Expression::GreaterThan)
          },
          Expression::GreaterThanEquals(ref left, ref right) => {
            resolve_types_for_binary_comparison(left, right, Expression::GreaterThanEquals)
          }
          Expression::Identifier(_, _) => {
            // Should never happen, all identifiers must be resolved before this step runs.
            Err(Error::SQLAnalysisExpressionDataType(format!("Identifier is unresolved")))
          },
          Expression::IsNull(_) => Ok(None),
          Expression::IsNotNull(_) => Ok(None),
          Expression::LessThan(ref left, ref right) => {
            resolve_types_for_binary_comparison(left, right, Expression::LessThan)
          }
          Expression::LessThanEquals(ref left, ref right) => {
            resolve_types_for_binary_comparison(left, right, Expression::LessThanEquals)
          }
          Expression::LiteralBool(_) => Ok(None),
          Expression::LiteralInt(_) => Ok(None),
          Expression::LiteralBigInt(_) => Ok(None),
          Expression::LiteralFloat(_) => Ok(None),
          Expression::LiteralDouble(_) => Ok(None),
          Expression::LiteralString(_) => Ok(None),
          Expression::Multiply(ref left, ref right) => {
            resolve_types_for_binary_arithmetic(left, right, Expression::Multiply)
          }
          Expression::Not(ref child) => {
            let tpe = child.data_type()?;
            if tpe != Type::BOOL {
              Err(
                Error::SQLAnalysisExpressionDataType(
                  format!(
                    "{} must have BOOL data type, got {}",
                    trees::plan_output(child.as_ref()),
                    tpe
                  )
                )
              )
            } else {
              Ok(None)
            }
          },
          Expression::NotEquals(ref left, ref right) => {
            resolve_types_for_binary_comparison(left, right, Expression::NotEquals)
          }
          Expression::Null => Ok(None),
          Expression::Or(ref left, ref right) => {
            let left_tpe = left.data_type()?;
            let right_tpe = right.data_type()?;
            if left_tpe != Type::BOOL || right_tpe != Type::BOOL {
              Err(
                Error::SQLAnalysisExpressionDataType(
                  format!("Or requires BOOL operands, got {} and {}", left_tpe, right_tpe)
                )
              )
            } else {
              Ok(None)
            }
          },
          Expression::Star(_) => {
            // Should never happen, all stars must be resolved before this step runs.
            Err(Error::SQLAnalysisExpressionDataType(format!("Star is unresolved")))
          },
          Expression::Subtract(ref left, ref right) => {
            resolve_types_for_binary_arithmetic(left, right, Expression::Subtract)
          }
          Expression::UnaryPlus(ref child) |
          Expression::UnaryMinus(ref child) => {
            let tpe = child.data_type()?;
            if !tpe.is_numeric() && !tpe.is_null() {
              Err(
                Error::SQLAnalysisExpressionDataType(
                  format!(
                    "{} must have numeric data type, got {}",
                    trees::plan_output(child.as_ref()),
                    tpe
                  )
                )
              )
            } else {
              Ok(None)
            }
          },
        }
      },
    }
  }
}

// Resolves expression 1-to-1.
fn resolve_expression(
  expr: &Expression,
  input: &[(Rc<ExpressionContext>, Expression)]
) -> Res<Expression> {
  trees::transform_up(expr, &ExpressionRule::ResolveIdentifiers(input))
}

// Resolves single expression into one or more expressions provided the input.
// Expressions like `Star` could result in more than one expression.
fn resolve_expressions(
  expressions: &[Expression],
  input: &[(Rc<ExpressionContext>, Expression)]
) -> Res<Vec<Expression>> {
  let mut resolved_expressions = Vec::new();

  for expr in expressions {
    match expr {
      Expression::Star(ref parts) => {
        for (ctx, input_expr) in input {
          if ctx.matches_suffix(parts) {
            resolved_expressions.push(input_expr.clone());
          }
        }
      },
      _ => resolved_expressions.push(resolve_expression(expr, input)?),
    }
  }

  Ok(resolved_expressions)
}

fn resolve_expression_type(expr: &Expression) -> Res<Expression> {
  trees::transform_up(expr, &ExpressionRule::ResolveTypes)
}

#[cfg(test)]
mod tests {
  use std::rc::Rc;
  use super::*;
  use crate::exec::plan::dsl::*;
  use crate::exec::types::Type;

  // Convenience: resolve types and unwrap.
  fn resolve(expr: Expression) -> Res<Expression> {
    resolve_expression_type(&expr)
  }

  //=====================================
  // resolve_types_for_binary_arithmetic
  //=====================================

  #[test]
  fn test_resolve_types_arithmetic_same_type() {
    // Same type on both sides: no rewrite.
    assert_eq!(resolve(add(int(1), int(2))), Ok(add(int(1), int(2))));
    assert_eq!(resolve(subtract(double(1.0), double(2.0))), Ok(subtract(double(1.0), double(2.0))));
  }

  #[test]
  fn test_resolve_types_arithmetic_left_widened() {
    // Left is narrower: left gets Cast.
    assert_eq!(
      resolve(add(int(1), bigint(2))),
      Ok(add(cast(int(1), Type::BIGINT), bigint(2)))
    );
    assert_eq!(
      resolve(multiply(float(1.0), double(2.0))),
      Ok(multiply(cast(float(1.0), Type::DOUBLE), double(2.0)))
    );
  }

  #[test]
  fn test_resolve_types_arithmetic_right_widened() {
    // Right is narrower: right gets Cast.
    assert_eq!(
      resolve(add(bigint(1), int(2))),
      Ok(add(bigint(1), cast(int(2), Type::BIGINT)))
    );
    assert_eq!(
      resolve(subtract(double(1.0), float(2.0))),
      Ok(subtract(double(1.0), cast(float(2.0), Type::DOUBLE)))
    );
  }

  #[test]
  fn test_resolve_types_arithmetic_incompatible() {
    // TEXT / BOOL in arithmetic: error.
    assert!(resolve(add(double(1.0), string("x"))).is_err());
    assert!(resolve(multiply(float(1.0), boolean(true))).is_err());
    assert!(resolve(divide(string("a"), int(1))).is_err());
  }

  //=====================================
  // resolve_types_for_binary_comparison
  //=====================================

  #[test]
  fn test_resolve_types_comparison_same_type() {
    // Same type: no rewrite.
    assert_eq!(resolve(equals(int(1), int(2))), Ok(equals(int(1), int(2))));
    assert_eq!(resolve(less_than(string("a"), string("b"))), Ok(less_than(string("a"), string("b"))));
    assert_eq!(resolve(equals(boolean(true), boolean(false))), Ok(equals(boolean(true), boolean(false))));
  }

  #[test]
  fn test_resolve_types_comparison_left_widened() {
    // Left is narrower: left gets Cast to right's type.
    assert_eq!(
      resolve(equals(int(1), bigint(2))),
      Ok(equals(cast(int(1), Type::BIGINT), bigint(2)))
    );
    assert_eq!(
      resolve(less_than(float(1.0), double(2.0))),
      Ok(less_than(cast(float(1.0), Type::DOUBLE), double(2.0)))
    );
  }

  #[test]
  fn test_resolve_types_comparison_right_widened() {
    // Right is narrower: right gets Cast to left's type.
    assert_eq!(
      resolve(equals(bigint(1), int(2))),
      Ok(equals(bigint(1), cast(int(2), Type::BIGINT)))
    );
  }

  #[test]
  fn test_resolve_types_comparison_incompatible() {
    // TEXT vs INT, BOOL vs INT: error.
    assert!(resolve(equals(string("a"), int(1))).is_err());
    assert!(resolve(less_than(boolean(true), int(1))).is_err());
  }

  //==========
  // And / Or
  //==========

  #[test]
  fn test_resolve_types_and_valid() {
    assert_eq!(resolve(and(boolean(true), boolean(false))), Ok(and(boolean(true), boolean(false))));
  }

  #[test]
  fn test_resolve_types_and_invalid() {
    assert!(resolve(and(int(1), boolean(true))).is_err());
    assert!(resolve(and(boolean(true), int(1))).is_err());
  }

  #[test]
  fn test_resolve_types_or_valid() {
    assert_eq!(resolve(or(boolean(true), boolean(false))), Ok(or(boolean(true), boolean(false))));
  }

  #[test]
  fn test_resolve_types_or_invalid() {
    assert!(resolve(or(int(1), boolean(true))).is_err());
    assert!(resolve(or(boolean(false), string("x"))).is_err());
  }

  //=====
  // Not
  //=====

  #[test]
  fn test_resolve_types_not_valid() {
    assert_eq!(resolve(not(boolean(true))), Ok(not(boolean(true))));
  }

  #[test]
  fn test_resolve_types_not_invalid() {
    assert!(resolve(not(int(1))).is_err());
    assert!(resolve(not(string("x"))).is_err());
  }

  //========
  // Concat
  //========

  #[test]
  fn test_resolve_types_concat_valid() {
    assert_eq!(resolve(concat(string("a"), string("b"))), Ok(concat(string("a"), string("b"))));
  }

  #[test]
  fn test_resolve_types_concat_invalid() {
    assert!(resolve(concat(int(1), string("b"))).is_err());
    assert!(resolve(concat(string("a"), int(1))).is_err());
  }

  //======
  // Cast
  //======

  #[test]
  fn test_resolve_types_cast_valid() {
    // Widening.
    assert_eq!(resolve(cast(int(1), Type::BIGINT)), Ok(cast(int(1), Type::BIGINT)));
    assert_eq!(resolve(cast(int(1), Type::TEXT)), Ok(cast(int(1), Type::TEXT)));
    assert_eq!(resolve(cast(boolean(true), Type::TEXT)), Ok(cast(boolean(true), Type::TEXT)));
    // Narrowing.
    assert_eq!(resolve(cast(bigint(1), Type::INT)), Ok(cast(bigint(1), Type::INT)));
    assert_eq!(resolve(cast(string("1"), Type::INT)), Ok(cast(string("1"), Type::INT)));
    // Identity.
    assert_eq!(resolve(cast(int(1), Type::INT)), Ok(cast(int(1), Type::INT)));
  }

  #[test]
  fn test_resolve_types_cast_invalid() {
    assert!(resolve(cast(boolean(true), Type::INT)).is_err());
    assert!(resolve(cast(int(1), Type::BOOL)).is_err());
  }

  //========================
  // UnaryPlus / UnaryMinus
  //========================

  #[test]
  fn test_resolve_types_unary_valid() {
    assert_eq!(resolve(_plus(int(1))), Ok(_plus(int(1))));
    assert_eq!(resolve(_minus(double(1.0))), Ok(_minus(double(1.0))));
    assert_eq!(resolve(_minus(null())), Ok(_minus(null())));
  }

  #[test]
  fn test_resolve_types_unary_invalid() {
    assert!(resolve(_plus(string("x"))).is_err());
    assert!(resolve(_minus(boolean(true))).is_err());
  }
}
