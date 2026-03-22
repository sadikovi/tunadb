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

enum AnalysisRule<'a> {
  ResolveNodes(&'a Session, &'a TransactionRef),
  ResolveTypes(&'a Session, &'a TransactionRef),
}

impl<'a> AnalysisRule<'a> {
}

impl<'a> trees::Rule<LogicalPlan> for AnalysisRule<'a> {
  fn apply(&self, plan: &LogicalPlan) -> Res<Option<LogicalPlan>> {
    match self {
      AnalysisRule::ResolveNodes(ref session, ref txn) => {
        analysis_resolve_nodes(session, txn, plan)
      },
      AnalysisRule::ResolveTypes(ref session, ref txn) => {
        analysis_resolve_types(session, txn, plan)
      },
    }
  }
}

fn analysis_resolve_nodes(
  session: &Session,
  txn: &TransactionRef,
  plan: &LogicalPlan
) -> Res<Option<LogicalPlan>> {
  match plan {
    LogicalPlan::UnresolvedCreateSchema(ref schema_name) => {
      match catalog::get_schema(txn, schema_name) {
        Ok(info) => Err(Error::SQLAnalysisSchemaAlreadyExists(info.into_schema_name())),
        Err(Error::SchemaDoesNotExist(_)) => {
          Ok(Some(LogicalPlan::CreateSchema(schema_name.clone())))
        },
        Err(err) => Err(err),
      }
    },
    LogicalPlan::UnresolvedCreateTable(ref schema_name, ref table_name, ref fields) => {
      match catalog::get_relation(txn, current_schema(session, schema_name), table_name) {
        Ok((schema_info, table_info)) => {
          Err(
            Error::SQLAnalysisTableAlreadyExists(
              schema_info.into_schema_name(),
              table_info.into_relation_name()
            )
          )
        },
        Err(Error::SchemaDoesNotExist(schema_name)) => {
          Err(Error::SQLAnalysisSchemaDoesNotExist(schema_name))
        },
        Err(Error::RelationDoesNotExist(ref schema_name, ref table_name)) => {
          // Validate fields to make sure there are no duplicates.
          assert_unique_fields(fields)?;
          Ok(
            Some(
              LogicalPlan::CreateTable(
                Rc::new(schema_name.to_string()),
                Rc::new(table_name.to_string()),
                fields.clone()
              )
            )
          )
        },
        Err(err) => Err(err),
      }
    },
    LogicalPlan::UnresolvedDropSchema(ref schema_name, cascade) => {
      match catalog::get_schema(txn, schema_name) {
        Ok(info) => {
          Ok(Some(LogicalPlan::DropSchema(Rc::new(info), *cascade)))
        },
        Err(Error::SchemaDoesNotExist(schema_name)) => {
          Err(Error::SQLAnalysisSchemaDoesNotExist(schema_name))
        },
        Err(err) => Err(err),
      }
    },
    LogicalPlan::UnresolvedDropTable(ref schema_name, ref table_name) => {
      match catalog::get_relation(txn, current_schema(session, schema_name), table_name) {
        Ok((schema_info, table_info)) => {
          Ok(Some(LogicalPlan::DropTable(Rc::new(schema_info), Rc::new(table_info))))
        },
        Err(Error::SchemaDoesNotExist(schema_name)) => {
          Err(Error::SQLAnalysisSchemaDoesNotExist(schema_name))
        },
        Err(Error::RelationDoesNotExist(schema_name, table_name)) => {
          Err(Error::SQLAnalysisTableDoesNotExist(schema_name, table_name))
        },
        Err(err) => Err(err),
      }
    },
    LogicalPlan::UnresolvedFilter(ref expression, ref child) => {
      let output = resolve_expression(expression, &child.output()?)?;
      Ok(Some(LogicalPlan::Filter(Rc::new(output), child.clone())))
    },
    LogicalPlan::UnresolvedInsertInto(ref schema_name, ref table_name, ref columns, ref query) => {
      match catalog::get_relation(txn, current_schema(session, schema_name), table_name) {
        Ok((schema_info, table_info)) => {
          // Insert is always positional, not based on column names.
          // We only check top-level fields.
          let query_cols = query.output()?;

          if !columns.is_empty() {
            let mut set = HashSet::new();

            for col in columns.as_slice() {
              if !set.insert(col) {
                return Err(
                  Error::SQLAnalysisUnresolvedPlan(
                    format!("Duplicate column {} in Insert", col)
                  )
                );
              }
            }

            for col in columns.as_slice() {
              if table_info.relation_fields().get_field(col).is_none() {
                return Err(
                  Error::SQLAnalysisUnresolvedPlan(
                    format!(
                      "Column {} does not exist in the table {} schema",
                      col,
                      table_info.relation_name()
                    )
                  )
                );
              }
            }
          }

          let expected_col_len = if !columns.is_empty() {
            columns.len()
          } else {
            table_info.relation_fields().len()
          };

          // populate columns from the table.
          if expected_col_len != query_cols.len() {
            return Err(
              Error::SQLAnalysisUnresolvedPlan(
                format!(
                  "Input columns match for Insert, expected {} columns, found {}",
                  expected_col_len,
                  query_cols.len()
                )
              )
            );
          }

          Ok(
            Some(
              LogicalPlan::InsertInto(
                Rc::new(schema_info),
                Rc::new(table_info),
                columns.clone(), // empty means all table columns in definition order
                query.clone()
              )
            )
          )
        },
        Err(Error::SchemaDoesNotExist(schema_name)) => {
          Err(Error::SQLAnalysisSchemaDoesNotExist(schema_name))
        },
        Err(Error::RelationDoesNotExist(schema_name, table_name)) => {
          Err(Error::SQLAnalysisTableDoesNotExist(schema_name, table_name))
        },
        Err(err) => Err(err),
      }
    },
    LogicalPlan::UnresolvedLimit(ref limit, ref child) => {
      Ok(Some(LogicalPlan::Limit(*limit, child.clone())))
    },
    LogicalPlan::UnresolvedLocalRelation(ref expressions) => {
      let mut output = Vec::new();
      for expr_row in expressions.as_slice() {
        let output_row = resolve_expressions(expr_row, &[])?;
        output.push(output_row);
      }
      Ok(Some(LogicalPlan::LocalRelation(Rc::new(output))))
    },
    LogicalPlan::UnresolvedProject(ref expressions, ref child) => {
      let output = resolve_expressions(expressions, &child.output()?)?;
      Ok(Some(LogicalPlan::Project(Rc::new(output), child.clone())))
    },
    LogicalPlan::UnresolvedSubquery(ref alias, ref child) => {
      let resolved_alias = alias.clone().unwrap_or(Rc::new(DEFAULT_SUBQUERY_NAME.to_string()));
      Ok(Some(LogicalPlan::Subquery(resolved_alias, child.clone())))
    },
    LogicalPlan::UnresolvedTableScan(ref schema_name, ref table_name, ref alias) => {
      match catalog::get_relation(txn, current_schema(session, schema_name), table_name) {
        Ok((schema_info, table_info)) => {
          Ok(
            Some(
              LogicalPlan::TableScan(
                Rc::new(schema_info),
                Rc::new(table_info),
                alias.clone()
              )
            )
          )
        },
        Err(Error::SchemaDoesNotExist(schema_name)) => {
          Err(Error::SQLAnalysisSchemaDoesNotExist(schema_name))
        },
        Err(Error::RelationDoesNotExist(schema_name, table_name)) => {
          Err(Error::SQLAnalysisTableDoesNotExist(schema_name, table_name))
        },
        Err(err) => Err(err),
      }
    },
    _ => Ok(None),
  }
}

fn analysis_resolve_types(
  _session: &Session,
  _txn: &TransactionRef,
  plan: &LogicalPlan,
) -> Res<Option<LogicalPlan>> {
  match plan {
    // LogicalPlan::Filter(ref expression, ref child) => {
    //   let resolved = resolve_expression_type(expression.as_ref())?;
    //   if resolved.data_type()? != &Type::BOOL {
    //     return Err(
    //       Error::SQLAnalysisExpressionDataType(
    //         format!("Filter expression {} must be of type BOOL", trees::tree_output(&resolved))
    //       )
    //     );
    //   }
    //   Ok(Some(LogicalPlan::Filter(Rc::new(resolved), child.clone())))
    // },
    // LogicalPlan::InsertInto(ref _schema_info, ref table_info, ref cols, ref query) => {
    //   let output = query.output()?;
    //   let table_fields = table_info.relation_fields();
    //   if output.len() != cols.len() {
    //     return Err(
    //       Error::SQLAnalysisExpressionDataType(
    //         format!(
    //           "INSERT column count mismatch: query has {} columns, {} column names given",
    //           output.len(),
    //           cols.len()
    //         )
    //       )
    //     );
    //   }
    //   for (i, col_name) in cols.iter().enumerate() {
    //     let table_field = table_fields
    //       .get_field(col_name)
    //       .ok_or_else(|| {
    //         Error::SQLAnalysisUnknownField(
    //           format!("Unknown field {} in destination table", col_name)
    //         )
    //       })?;
    //     let expr_tpe = output[i].1.data_type()?;
    //     let target_tpe = table_field.data_type();
    //     if expr_tpe != target_tpe && !can_cast(target_tpe, expr_tpe) {
    //       return Err(
    //         Error::SQLAnalysisExpressionDataType(
    //           format!(
    //             "Column {} type mismatch: expression has type {}, table expects {}",
    //             col_name,
    //             expr_tpe,
    //             target_tpe
    //           )
    //         )
    //       );
    //     }
    //   }
    //   Ok(None)
    // },
    // LogicalPlan::LocalRelation(ref expressions) => {
    //   if expressions.is_empty() {
    //     return Ok(None);
    //   }
    //   let row_len = expressions[0].len();
    //   for (row_idx, row) in expressions.iter().enumerate() {
    //     if row.len() != row_len {
    //       return Err(
    //         Error::SQLAnalysisExpressionDataType(
    //           format!(
    //             "LocalRelation row {} has {} expressions, expected {}",
    //             row_idx,
    //             row.len(),
    //             row_len
    //           )
    //         )
    //       );
    //     }
    //     for (col_idx, expr) in row.iter().enumerate() {
    //       expr.data_type().map_err(|e| {
    //         Error::SQLAnalysisExpressionDataType(
    //           format!("LocalRelation row {} column {}: {:?}", row_idx, col_idx, e)
    //         )
    //       })?;
    //     }
    //   }
    //   Ok(None)
    // },
    // LogicalPlan::Project(ref expressions, ref child) => {
    //   let mut resolved_exprs: Vec<Expression> = Vec::with_capacity(expressions.len());
    //   let mut changed = false;
    //   for expr in expressions.as_ref() {
    //     let resolved = resolve_expression_type(expr)?;
    //     if &resolved != expr {
    //       changed = true;
    //     }
    //     resolved.data_type()?;
    //     resolved_exprs.push(resolved);
    //   }
    //   if changed {
    //     Ok(Some(LogicalPlan::Project(Rc::new(resolved_exprs), child.clone())))
    //   } else {
    //     Ok(None)
    //   }
    // },
    _ => Ok(None),
  }
}

// Analyses the plan and returns fully resolved and analysed plan.
// If it is not possible, returns an error.
pub fn analyse(session: &Session, txn: &TransactionRef, plan: LogicalPlan) -> Res<LogicalPlan> {
  let rules = vec![
    AnalysisRule::ResolveNodes(session, txn),
    AnalysisRule::ResolveTypes(session, txn),
  ];

  let mut curr_plan: LogicalPlan = plan;

  for rule in rules {
    let tmp = trees::transform_up(&curr_plan, &rule)?;
    curr_plan = tmp;
  }

  Ok(curr_plan)
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
