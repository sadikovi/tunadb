use std::collections::HashSet;
use std::rc::Rc;
use crate::common::error::{Error, Res};
use crate::sql::catalog;
use crate::sql::plan::{
  DEFAULT_SUBQUERY_NAME,
  Expression,
  ExpressionContext,
  LogicalPlan,
  can_cast,
  can_numeric_and_null_upcast,
  promote_arithmetic_type,
};
use crate::sql::session::Session;
use crate::sql::trees;
use crate::sql::types::{Fields, Type};
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
      return Err(
        Error::SQLAnalysisExpressionError(format!("Duplicate column name {}", field.name()))
      );
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
      Error::SQLAnalysisExpressionError(
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
        Error::SQLAnalysisExpressionError(
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

  // promote_arithmetic_type already validated that a promotion path exists, so casting
  // unconditionally here is safe: if the operand type already matches result_tpe we skip it,
  // otherwise the cast is guaranteed to be a valid numeric widening or NULL conversion.
  let new_left = if ltpe == result_tpe {
    left.clone()
  } else {
    Rc::new(Expression::Cast(left.clone(), Rc::new(result_tpe.clone())))
  };

  let new_right = if rtpe == result_tpe {
    right.clone()
  } else {
    Rc::new(Expression::Cast(right.clone(), Rc::new(result_tpe)))
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

            if identifier_matches.is_empty() {
              // We could not resolve the identifier.
              Err(
                Error::SQLAnalysisExpressionError(
                  format!("Unknown expressions found: {:?}", expr)
                )
              )
            } else if identifier_matches.len() == 1 {
              Ok(identifier_matches.pop().cloned())
            } else {
              Err(
                Error::SQLAnalysisExpressionError(
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
                Error::SQLAnalysisExpressionError(
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
                Error::SQLAnalysisExpressionError(
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
                Error::SQLAnalysisExpressionError(
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
            Err(Error::SQLAnalysisExpressionError(format!("Identifier is unresolved")))
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
                Error::SQLAnalysisExpressionError(
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
                Error::SQLAnalysisExpressionError(
                  format!("Or requires BOOL operands, got {} and {}", left_tpe, right_tpe)
                )
              )
            } else {
              Ok(None)
            }
          },
          Expression::Star(_) => {
            // Should never happen, all stars must be resolved before this step runs.
            Err(Error::SQLAnalysisExpressionError(format!("Star is unresolved")))
          },
          Expression::Subtract(ref left, ref right) => {
            resolve_types_for_binary_arithmetic(left, right, Expression::Subtract)
          }
          Expression::UnaryPlus(ref child) |
          Expression::UnaryMinus(ref child) => {
            let tpe = child.data_type()?;
            if !tpe.is_numeric() && !tpe.is_null() {
              Err(
                Error::SQLAnalysisExpressionError(
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
  ExpandCommands(&'a Session),
  ResolveNodes(&'a Session, &'a TransactionRef),
  ResolveTypes,
}

impl<'a> trees::Rule<LogicalPlan> for AnalysisRule<'a> {
  fn apply(&self, plan: &LogicalPlan) -> Res<Option<LogicalPlan>> {
    match self {
      AnalysisRule::ExpandCommands(session) => {
        analysis_expand_commands(session, plan)
      },
      AnalysisRule::ResolveNodes(ref session, ref txn) => {
        analysis_resolve_nodes(session, txn, plan)
      },
      AnalysisRule::ResolveTypes => {
        analysis_resolve_types(plan)
      },
    }
  }
}

fn analysis_expand_commands(session: &Session, plan: &LogicalPlan) -> Res<Option<LogicalPlan>> {
  let info_schema = Some(Rc::new(catalog::INFORMATION_SCHEMA.to_string()));
  let star = Rc::new(vec![Expression::Star(Rc::new(Vec::new()))]);

  match plan {
    LogicalPlan::UnresolvedShowSchemas => {
      let scan = Rc::new(LogicalPlan::UnresolvedTableScan(
        info_schema,
        Rc::new(catalog::INFORMATION_SCHEMA_SCHEMATA.to_string()),
        None,
      ));
      Ok(Some(LogicalPlan::UnresolvedProject(star, scan)))
    },
    LogicalPlan::UnresolvedShowTables => {
      let scan = Rc::new(LogicalPlan::UnresolvedTableScan(
        info_schema,
        Rc::new(catalog::INFORMATION_SCHEMA_RELATIONS.to_string()),
        None,
      ));
      let filter_expr = Rc::new(Expression::Equals(
        Rc::new(Expression::Identifier(
          Rc::new(Vec::new()),
          Rc::new(catalog::INFORMATION_SCHEMA_RELATIONS_RELATION_SCHEMA.to_string()),
        )),
        Rc::new(Expression::LiteralString(Rc::new(session.current_schema().to_string()))),
      ));
      let filter = Rc::new(LogicalPlan::UnresolvedFilter(filter_expr, scan));
      Ok(Some(LogicalPlan::UnresolvedProject(star, filter)))
    },
    _ => Ok(None),
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
        Ok(info) => Err(
          Error::SQLAnalysisError(format!("Schema {} already exists", info.into_schema_name()))
        ),
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
            Error::SQLAnalysisError(
              format!(
                "Table {}.{} already exists",
                schema_info.into_schema_name(),
                table_info.into_relation_name()
              )
            )
          )
        },
        Err(Error::SchemaDoesNotExist(schema_name)) => {
          Err(Error::SQLAnalysisError(format!("Schema {} does not exist", schema_name)))
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
          Err(Error::SQLAnalysisError(format!("Schema {} does not exist", schema_name)))
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
          Err(Error::SQLAnalysisError(format!("Schema {} does not exist", schema_name)))
        },
        Err(Error::RelationDoesNotExist(schema_name, table_name)) => {
          Err(Error::SQLAnalysisError(
            format!("Table {}.{} does not exist", schema_name, table_name)
          ))
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
          // Column positions are at most length of table fields.
          let mut col_positions = Vec::with_capacity(table_info.relation_fields().len());

          if !columns.is_empty() {
            let mut set = HashSet::new();

            for col in columns.as_slice() {
              if !set.insert(col) {
                return Err(
                  Error::SQLAnalysisError(
                    format!("Duplicate column {} in Insert", col)
                  )
                );
              }
            }

            for col in columns.as_slice() {
              match table_info.relation_fields().get_field_pos(col) {
                Some(pos) => col_positions.push(pos),
                None => {
                  return Err(
                    Error::SQLAnalysisError(
                      format!(
                        "Column {} does not exist in the table {} schema",
                        col,
                        table_info.relation_name()
                      )
                    )
                  );
                },
              }
            }
          } else {
            for i in 0..table_info.relation_fields().len() {
              col_positions.push(i);
            }
          }

          // populate columns from the table.
          if col_positions.len() != query_cols.len() {
            return Err(
              Error::SQLAnalysisError(
                format!(
                  "Input columns match for Insert, expected {} columns, found {}",
                  col_positions.len(),
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
                Rc::new(col_positions),
                query.clone()
              )
            )
          )
        },
        Err(Error::SchemaDoesNotExist(schema_name)) => {
          Err(Error::SQLAnalysisError(format!("Schema {} does not exist", schema_name)))
        },
        Err(Error::RelationDoesNotExist(schema_name, table_name)) => {
          Err(Error::SQLAnalysisError(
            format!("Table {}.{} does not exist", schema_name, table_name)
          ))
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
          Err(Error::SQLAnalysisError(format!("Schema {} does not exist", schema_name)))
        },
        Err(Error::RelationDoesNotExist(schema_name, table_name)) => {
          Err(Error::SQLAnalysisError(
            format!("Table {}.{} does not exist", schema_name, table_name)
          ))
        },
        Err(err) => Err(err),
      }
    },
    _ => Ok(None),
  }
}

fn analysis_resolve_types(plan: &LogicalPlan) -> Res<Option<LogicalPlan>> {
  match plan {
    LogicalPlan::Filter(ref expression, ref child) => {
      let resolved = resolve_expression_type(expression.as_ref())?;
      if resolved.data_type()? != Type::BOOL {
        return Err(
          Error::SQLAnalysisError(
            format!("Filter expression {} must be BOOL", trees::plan_output(&resolved))
          )
        );
      }
      if &resolved != expression.as_ref() {
        Ok(Some(LogicalPlan::Filter(Rc::new(resolved), child.clone())))
      } else {
        Ok(None)
      }
    },
    LogicalPlan::InsertInto(ref schema_info, ref table_info, ref col_pos, ref query) => {
      let table_fields = table_info.relation_fields().get();
      let output = query.output()?;
      // This should have been already verified in ResolveNodes.
      assert_eq!(col_pos.len(), output.len());

      let mut requires_projection = false;
      let mut projection = Vec::with_capacity(col_pos.len());

      for (query_pos, (_ctx, out_expr)) in output.into_iter().enumerate() {
        let in_field = &table_fields[col_pos[query_pos]];
        let in_field_tpe = in_field.data_type();
        let out_expr_tpe = out_expr.data_type()?;

        if *in_field_tpe == out_expr_tpe {
          projection.push(out_expr);
        } else if can_numeric_and_null_upcast(&out_expr_tpe, &in_field_tpe) {
          projection.push(Expression::Cast(Rc::new(out_expr), Rc::new(in_field_tpe.clone())));
          requires_projection = true;
        } else {
          return Err(
            Error::SQLAnalysisError(
              format!(
                "Expected {} type for expression {} but received {} in Insert",
                in_field_tpe,
                out_expr_tpe,
                trees::plan_output(&out_expr)
              )
            )
          );
        }
      }

      if requires_projection {
        Ok(
          Some(
            LogicalPlan::InsertInto(
              schema_info.clone(),
              table_info.clone(),
              col_pos.clone(),
              Rc::new(
                LogicalPlan::Project(
                  Rc::new(projection),
                  query.clone()
                )
              )
            )
          )
        )
      } else {
        Ok(None)
      }
    },
    LogicalPlan::LocalRelation(ref expressions) => {
      let mut resolved_exprs: Vec<Vec<Expression>> = Vec::with_capacity(expressions.len());
      let mut changed = false;

      for row in expressions.iter() {
        let mut row_buf = Vec::with_capacity(row.len());
        for expr in row.iter() {
          let resolved = resolve_expression_type(expr)?;
          if &resolved != expr {
            changed = true;
          }
          resolved.data_type()?;
          row_buf.push(resolved);
        }
        resolved_exprs.push(row_buf);
      }

      if changed {
        Ok(Some(LogicalPlan::LocalRelation(Rc::new(resolved_exprs))))
      } else {
        Ok(None)
      }
    },
    LogicalPlan::Project(ref expressions, ref child) => {
      let mut resolved_exprs: Vec<Expression> = Vec::with_capacity(expressions.len());
      let mut changed = false;

      for expr in expressions.as_ref() {
        let resolved = resolve_expression_type(expr)?;
        if &resolved != expr {
          changed = true;
        }
        resolved.data_type()?;
        resolved_exprs.push(resolved);
      }

      if changed {
        Ok(Some(LogicalPlan::Project(Rc::new(resolved_exprs), child.clone())))
      } else {
        Ok(None)
      }
    },
    _ => Ok(None),
  }
}

// Analyses the plan and returns fully resolved and analysed plan.
// If it is not possible, returns an error.
pub fn analyse(session: &Session, txn: &TransactionRef, plan: LogicalPlan) -> Res<LogicalPlan> {
  let rules = vec![
    AnalysisRule::ExpandCommands(session),
    AnalysisRule::ResolveNodes(session, txn),
    AnalysisRule::ResolveTypes,
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
  use crate::sql::catalog::{self, RelationType};
  use crate::sql::plan::dsl::*;
  use crate::sql::session::Session;
  use crate::sql::types::{Field, Fields, Type};
  use crate::storage::db;

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

  #[test]
  fn test_resolve_types_arithmetic_null() {
    // NULL op T: NULL is cast to T (§3.2).
    assert_eq!(resolve(add(null(), int(1))), Ok(add(cast(null(), Type::INT), int(1))));
    assert_eq!(
      resolve(multiply(bigint(1), null())),
      Ok(multiply(bigint(1), cast(null(), Type::BIGINT)))
    );
    assert_eq!(
      resolve(subtract(null(), double(1.0))),
      Ok(subtract(cast(null(), Type::DOUBLE), double(1.0)))
    );
    // NULL op NULL: both sides stay NULL, no cast needed (result type is NULL).
    assert_eq!(resolve(add(null(), null())), Ok(add(null(), null())));
  }

  //=====================================
  // resolve_types_for_binary_comparison
  //=====================================

  #[test]
  fn test_resolve_types_comparison_same_type() {
    // Same type: no rewrite.
    assert_eq!(resolve(equals(int(1), int(2))), Ok(equals(int(1), int(2))));
    assert_eq!(
      resolve(less_than(string("a"), string("b"))),
      Ok(less_than(string("a"), string("b")))
    );
    assert_eq!(
      resolve(equals(boolean(true), boolean(false))),
      Ok(equals(boolean(true), boolean(false)))
    );
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

  //===========================================================
  // analysis_resolve_types — plan level (no catalog required)
  //===========================================================

  #[test]
  fn test_analysis_resolve_types_filter_bool_no_change() {
    let child = Rc::new(LogicalPlan::LocalRelation(Rc::new(vec![vec![]])));
    let plan = LogicalPlan::Filter(Rc::new(boolean(true)), child);
    assert_eq!(analysis_resolve_types(&plan), Ok(None));
  }

  #[test]
  fn test_analysis_resolve_types_filter_widened() {
    // Comparison of INT < BIGINT: INT operand gets a Cast node inserted.
    let child = Rc::new(LogicalPlan::LocalRelation(Rc::new(vec![vec![]])));
    let plan = LogicalPlan::Filter(Rc::new(less_than(int(1), bigint(2))), child.clone());
    assert_eq!(
      analysis_resolve_types(&plan),
      Ok(Some(LogicalPlan::Filter(
        Rc::new(less_than(cast(int(1), Type::BIGINT), bigint(2))),
        child,
      )))
    );
  }

  #[test]
  fn test_analysis_resolve_types_filter_non_bool_error() {
    let child = Rc::new(LogicalPlan::LocalRelation(Rc::new(vec![vec![]])));
    let plan = LogicalPlan::Filter(Rc::new(int(1)), child);
    assert!(analysis_resolve_types(&plan).is_err());
  }

  #[test]
  fn test_analysis_resolve_types_local_relation_no_change() {
    let plan = LogicalPlan::LocalRelation(Rc::new(vec![vec![int(1), boolean(true)]]));
    assert_eq!(analysis_resolve_types(&plan), Ok(None));
  }

  #[test]
  fn test_analysis_resolve_types_local_relation_widened() {
    let plan = LogicalPlan::LocalRelation(Rc::new(vec![vec![add(int(1), bigint(2))]]));
    assert_eq!(
      analysis_resolve_types(&plan),
      Ok(Some(LogicalPlan::LocalRelation(
        Rc::new(vec![vec![add(cast(int(1), Type::BIGINT), bigint(2))]])
      )))
    );
  }

  #[test]
  fn test_analysis_resolve_types_project_no_change() {
    let child = Rc::new(LogicalPlan::LocalRelation(Rc::new(vec![vec![]])));
    let plan = LogicalPlan::Project(Rc::new(vec![int(1), boolean(true)]), child);
    assert_eq!(analysis_resolve_types(&plan), Ok(None));
  }

  #[test]
  fn test_analysis_resolve_types_project_widened() {
    let child = Rc::new(LogicalPlan::LocalRelation(Rc::new(vec![vec![]])));
    let plan = LogicalPlan::Project(Rc::new(vec![add(int(1), bigint(2))]), child.clone());
    assert_eq!(
      analysis_resolve_types(&plan),
      Ok(Some(LogicalPlan::Project(
        Rc::new(vec![add(cast(int(1), Type::BIGINT), bigint(2))]),
        child,
      )))
    );
  }

  //=========================================
  // analyse — end-to-end (catalog required)
  //=========================================

  fn init_db() -> db::DB {
    let mut dbc = db::open(None).try_build().unwrap();
    dbc.with_txn(true, |txn| {
      catalog::init_catalog(&txn).unwrap();
      catalog::create_schema(&txn, "default", false).unwrap();
    });
    dbc
  }

  // Creates a table in the "default" schema.
  fn setup_table(dbc: &mut db::DB, table: &str, cols: &[(&str, Type)]) {
    let fields = Fields::new(
      cols.iter().map(|(name, tpe)| Field::new(name.to_string(), tpe.clone(), true)).collect()
    );
    dbc.with_txn(true, |txn| {
      catalog::create_relation(
        &txn, "default", table, RelationType::TABLE, fields.clone(), false
      ).unwrap();
    });
  }

  #[test]
  fn test_analyse_create_table() {
    let mut dbc = init_db();
    let fields = Fields::new(vec![Field::new("a".to_string(), Type::INT, false)]);
    let result = dbc.with_txn(false, |txn| {
      analyse(&Session::builder().build(), &txn, create_table(None, "t", fields.clone()))
    });
    assert!(matches!(result, Ok(LogicalPlan::CreateTable(_, _, _))));
  }

  #[test]
  fn test_analyse_create_table_already_exists_error() {
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT)]);
    let fields = Fields::new(vec![Field::new("a".to_string(), Type::INT, false)]);
    let result = dbc.with_txn(false, |txn| {
      analyse(&Session::builder().build(), &txn, create_table(None, "t", fields.clone()))
    });
    assert!(result.is_err());
  }

  #[test]
  fn test_analyse_drop_table() {
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT)]);
    let result = dbc.with_txn(false, |txn| {
      analyse(&Session::builder().build(), &txn, drop_table(None, "t"))
    });
    assert!(matches!(result, Ok(LogicalPlan::DropTable(_, _))));
  }

  #[test]
  fn test_analyse_drop_table_not_exists_error() {
    let mut dbc = init_db();
    let result = dbc.with_txn(false, |txn| {
      analyse(&Session::builder().build(), &txn, drop_table(None, "t"))
    });
    assert!(result.is_err());
  }

  #[test]
  fn test_analyse_table_scan() {
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT)]);
    let result = dbc.with_txn(false, |txn| {
      analyse(&Session::builder().build(), &txn, from(None, "t", None))
    });
    assert!(matches!(result, Ok(LogicalPlan::TableScan(_, _, _))));
  }

  #[test]
  fn test_analyse_table_scan_not_exists_error() {
    let mut dbc = init_db();
    let result = dbc.with_txn(false, |txn| {
      analyse(&Session::builder().build(), &txn, from(None, "t", None))
    });
    assert!(result.is_err());
  }

  #[test]
  fn test_analyse_insert_all_cols() {
    // INSERT INTO t VALUES (1, 'x') — no column list, all columns in definition order.
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT), ("b", Type::TEXT)]);
    let result = dbc.with_txn(false, |txn| {
      let plan = insert_into_values(None, "t", vec![], vec![vec![int(1), string("x")]]);
      analyse(&Session::builder().build(), &txn, plan)
    });
    match result.unwrap() {
      LogicalPlan::InsertInto(_, _, col_pos, _) => {
        assert_eq!(col_pos.as_ref(), &vec![0, 1]);
      },
      other => panic!("expected InsertInto, got {:?}", other),
    }
  }

  #[test]
  fn test_analyse_insert_explicit_cols() {
    // INSERT INTO t (b, a) VALUES ('x', 1) — explicit reverse order, positions must reflect it.
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT), ("b", Type::TEXT)]);
    let result = dbc.with_txn(false, |txn| {
      let plan = insert_into_values(
        None, "t",
        vec!["b".to_string(), "a".to_string()],
        vec![vec![string("x"), int(1)]]
      );
      analyse(&Session::builder().build(), &txn, plan)
    });
    match result.unwrap() {
      LogicalPlan::InsertInto(_, _, col_pos, _) => {
        assert_eq!(col_pos.as_ref(), &vec![1, 0]);
      },
      other => panic!("expected InsertInto, got {:?}", other),
    }
  }

  #[test]
  fn test_analyse_insert_duplicate_col_error() {
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT), ("b", Type::INT)]);
    let result = dbc.with_txn(false, |txn| {
      let plan = insert_into_values(
        None, "t",
        vec!["a".to_string(), "a".to_string()],
        vec![vec![int(1), int(2)]]
      );
      analyse(&Session::builder().build(), &txn, plan)
    });
    assert!(result.is_err());
  }

  #[test]
  fn test_analyse_insert_unknown_col_error() {
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT)]);
    let result = dbc.with_txn(false, |txn| {
      let plan = insert_into_values(
        None, "t",
        vec!["z".to_string()],
        vec![vec![int(1)]]
      );
      analyse(&Session::builder().build(), &txn, plan)
    });
    assert!(result.is_err());
  }

  #[test]
  fn test_analyse_insert_count_mismatch_error() {
    // Table has 2 columns but only 1 value is provided.
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT), ("b", Type::INT)]);
    let result = dbc.with_txn(false, |txn| {
      let plan = insert_into_values(None, "t", vec![], vec![vec![int(1)]]);
      analyse(&Session::builder().build(), &txn, plan)
    });
    assert!(result.is_err());
  }

  #[test]
  fn test_analyse_insert_type_widening() {
    // INT value into BIGINT column — analysis wraps the query in a Project with Cast.
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::BIGINT)]);
    let result = dbc.with_txn(false, |txn| {
      let plan = insert_into_values(None, "t", vec![], vec![vec![int(1)]]);
      analyse(&Session::builder().build(), &txn, plan)
    });
    match result.unwrap() {
      LogicalPlan::InsertInto(_, _, _, query) => {
        match query.as_ref() {
          LogicalPlan::Project(exprs, _) => {
            assert_eq!(&exprs[0], &cast(int(1), Type::BIGINT));
          },
          other => panic!("expected Project wrapping the query, got {:?}", other),
        }
      },
      other => panic!("expected InsertInto, got {:?}", other),
    }
  }

  #[test]
  fn test_analyse_insert_incompatible_type_error() {
    // TEXT into INT column is incompatible — no implicit cast exists.
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT)]);
    let result = dbc.with_txn(false, |txn| {
      let plan = insert_into_values(None, "t", vec![], vec![vec![string("hello")]]);
      analyse(&Session::builder().build(), &txn, plan)
    });
    assert!(result.is_err());
  }

  #[test]
  fn test_analyse_filter() {
    let mut dbc = init_db();
    let result = dbc.with_txn(false, |txn| {
      analyse(&Session::builder().build(), &txn, filter(boolean(true), empty()))
    });
    assert!(matches!(result, Ok(LogicalPlan::Filter(_, _))));
  }

  #[test]
  fn test_analyse_project() {
    // Projection with implicit widening: INT + BIGINT becomes Cast(INT, BIGINT) + BIGINT.
    let mut dbc = init_db();
    let result = dbc.with_txn(false, |txn| {
      analyse(&Session::builder().build(), &txn, project(vec![add(int(1), bigint(2))], empty()))
    });
    match result.unwrap() {
      LogicalPlan::Project(exprs, _) => {
        assert_eq!(&exprs[0], &add(cast(int(1), Type::BIGINT), bigint(2)));
      },
      other => panic!("expected Project, got {:?}", other),
    }
  }

  #[test]
  fn test_analyse_local_relation() {
    let mut dbc = init_db();
    let result = dbc.with_txn(false, |txn| {
      analyse(&Session::builder().build(), &txn, local(vec![int(1), string("hello")]))
    });
    match result.unwrap() {
      LogicalPlan::LocalRelation(rows) => {
        assert_eq!(rows[0], vec![int(1), string("hello")]);
      },
      other => panic!("expected LocalRelation, got {:?}", other),
    }
  }

  #[test]
  fn test_analyse_subquery_with_alias() {
    let mut dbc = init_db();
    let result = dbc.with_txn(false, |txn| {
      analyse(&Session::builder().build(), &txn, subquery(empty(), Some("sq")))
    });
    match result.unwrap() {
      LogicalPlan::Subquery(alias, _) => assert_eq!(alias.as_str(), "sq"),
      other => panic!("expected Subquery, got {:?}", other),
    }
  }

  #[test]
  fn test_analyse_subquery_no_alias() {
    // A subquery without an alias gets the default alias (§14.1).
    let mut dbc = init_db();
    let result = dbc.with_txn(false, |txn| {
      analyse(&Session::builder().build(), &txn, subquery(empty(), None))
    });
    match result.unwrap() {
      LogicalPlan::Subquery(alias, _) => assert_eq!(alias.as_str(), DEFAULT_SUBQUERY_NAME),
      other => panic!("expected Subquery, got {:?}", other),
    }
  }

  #[test]
  fn test_analyse_limit() {
    let mut dbc = init_db();
    let result = dbc.with_txn(false, |txn| {
      analyse(&Session::builder().build(), &txn, limit(10, empty()))
    });
    assert!(matches!(result, Ok(LogicalPlan::Limit(10, _))));
  }

  //==========================
  // analysis_expand_commands
  //==========================

  #[test]
  fn test_expand_commands_show_schemas() {
    let session = Session::builder().build();
    let result = analysis_expand_commands(&session, &LogicalPlan::UnresolvedShowSchemas).unwrap();
    match result {
      Some(LogicalPlan::UnresolvedProject(exprs, scan)) => {
        assert!(matches!(exprs[0], Expression::Star(_)));
        match scan.as_ref() {
          LogicalPlan::UnresolvedTableScan(schema, name, None) => {
            assert_eq!(schema.as_deref().map(|s| s.as_str()), Some(catalog::INFORMATION_SCHEMA));
            assert_eq!(name.as_str(), catalog::INFORMATION_SCHEMA_SCHEMATA);
          },
          other => panic!("expected UnresolvedTableScan, got {:?}", other),
        }
      },
      other => panic!("expected UnresolvedProject, got {:?}", other),
    }
  }

  #[test]
  fn test_expand_commands_show_tables() {
    let session = Session::builder().build();
    let result = analysis_expand_commands(&session, &LogicalPlan::UnresolvedShowTables).unwrap();
    match result {
      Some(LogicalPlan::UnresolvedProject(exprs, filter)) => {
        assert!(matches!(exprs[0], Expression::Star(_)));
        match filter.as_ref() {
          LogicalPlan::UnresolvedFilter(filter_expr, scan) => {
            // Filter is on relation_schema = current_schema.
            match filter_expr.as_ref() {
              Expression::Equals(left, right) => {
                assert!(
                  matches!(
                    left.as_ref(),
                    Expression::Identifier(_, name) if name.as_str() ==
                      catalog::INFORMATION_SCHEMA_RELATIONS_RELATION_SCHEMA
                  )
                );
                assert!(
                  matches!(
                    right.as_ref(),
                    Expression::LiteralString(s) if s.as_str() == session.current_schema()
                  )
                );
              },
              other => panic!("expected Equals filter, got {:?}", other),
            }
            match scan.as_ref() {
              LogicalPlan::UnresolvedTableScan(schema, name, None) => {
                assert_eq!(
                  schema.as_deref().map(|s| s.as_str()),
                  Some(catalog::INFORMATION_SCHEMA)
                );
                assert_eq!(name.as_str(), catalog::INFORMATION_SCHEMA_RELATIONS);
              },
              other => panic!("expected UnresolvedTableScan, got {:?}", other),
            }
          },
          other => panic!("expected UnresolvedFilter, got {:?}", other),
        }
      },
      other => panic!("expected UnresolvedProject, got {:?}", other),
    }
  }

  #[test]
  fn test_expand_commands_other_unchanged() {
    let session = Session::builder().build();
    // Non-SHOW plan nodes return None (no expansion).
    let result = analysis_expand_commands(&session, &empty()).unwrap();
    assert!(result.is_none());
  }

  #[test]
  fn test_analyse_show_schemas() {
    // Full analyse() of UnresolvedShowSchemas resolves to Project(TableScan).
    let mut dbc = init_db();
    let result = dbc.with_txn(false, |txn| {
      analyse(&Session::builder().build(), &txn, LogicalPlan::UnresolvedShowSchemas)
    });
    assert!(matches!(result, Ok(LogicalPlan::Project(_, _))));
    match result.unwrap() {
      LogicalPlan::Project(_, child) => {
        assert!(matches!(child.as_ref(), LogicalPlan::TableScan(_, _, _)))
      },
      _ => unreachable!(),
    }
  }

  #[test]
  fn test_analyse_show_tables() {
    // Full analyse() of UnresolvedShowTables resolves to Project(Filter(TableScan)).
    let mut dbc = init_db();
    let result = dbc.with_txn(false, |txn| {
      analyse(&Session::builder().build(), &txn, LogicalPlan::UnresolvedShowTables)
    });
    assert!(matches!(result, Ok(LogicalPlan::Project(_, _))));
    match result.unwrap() {
      LogicalPlan::Project(_, child) => {
        match child.as_ref() {
          LogicalPlan::Filter(_, scan) => {
            assert!(matches!(scan.as_ref(), LogicalPlan::TableScan(_, _, _)))
          },
          other => panic!("expected Filter, got {:?}", other),
        }
      },
      _ => unreachable!(),
    }
  }
}
