use std::rc::Rc;
use crate::common::error::Res;
use crate::sql::plan::{LogicalPlan, PhysicalPlan};
use crate::sql::types::Fields;
// Converts a resolved LogicalPlan into a (Fields, PhysicalPlan) pair.
// Fields describes the schema of the rows produced by the plan.
// The input must be fully resolved — no Unresolved* variants should be present.
pub fn plan(logical: &LogicalPlan) -> Res<(Fields, PhysicalPlan)> {
  let physical = plan_node(logical)?;
  let fields = physical.schema()?;
  Ok((fields, physical))
}

// Recursively converts a LogicalPlan node into a PhysicalPlan node.
fn plan_node(logical: &LogicalPlan) -> Res<PhysicalPlan> {
  match logical {
    LogicalPlan::CreateSchema(ref name) => {
      Ok(PhysicalPlan::CreateSchema(name.clone()))
    },
    LogicalPlan::CreateTable(ref schema_name, ref table_name, ref fields) => {
      Ok(PhysicalPlan::CreateTable(schema_name.clone(), table_name.clone(), fields.clone()))
    },
    LogicalPlan::DropSchema(ref schema_info, cascade) => {
      Ok(PhysicalPlan::DropSchema(schema_info.clone(), *cascade))
    },
    LogicalPlan::DropTable(ref schema_info, ref table_info) => {
      Ok(PhysicalPlan::DropTable(schema_info.clone(), table_info.clone()))
    },
    LogicalPlan::Explain(extended, ref unresolved_snapshot, ref resolved_snapshot) => {
      Ok(PhysicalPlan::Explain(
        *extended,
        unresolved_snapshot.clone(),
        resolved_snapshot.clone(),
        Rc::new(plan_node(resolved_snapshot)?)
      ))
    },
    LogicalPlan::Filter(ref expr, ref child) => {
      Ok(PhysicalPlan::Filter(expr.clone(), Rc::new(plan_node(child)?)))
    },
    LogicalPlan::InsertInto(ref schema_info, ref table_info, ref col_positions, ref query) => {
      Ok(PhysicalPlan::InsertInto(
        schema_info.clone(),
        table_info.clone(),
        col_positions.clone(),
        Rc::new(plan_node(query)?),
      ))
    },
    LogicalPlan::Limit(limit, ref child) => {
      Ok(PhysicalPlan::Limit(*limit, Rc::new(plan_node(child)?)))
    },
    LogicalPlan::LocalRelation(ref expressions) => {
      Ok(PhysicalPlan::LocalRelation(expressions.clone()))
    },
    LogicalPlan::Project(ref expressions, ref child) => {
      Ok(PhysicalPlan::Project(expressions.clone(), Rc::new(plan_node(child)?)))
    },
    LogicalPlan::Subquery(_, ref child) => {
      // Subquery is a logical-only construct used to introduce an alias scope during analysis.
      // It allows expressions in the parent plan to reference columns via the subquery alias
      // (e.g. SELECT sq.id FROM (SELECT id FROM t) AS sq). By the time planning runs, all
      // identifiers have been resolved to ColumnRef nodes with concrete column indices, so
      // the alias is no longer needed. We convert the child directly and discard the wrapper.
      plan_node(child)
    },
    LogicalPlan::TableScan(ref schema_info, ref table_info, _) => {
      // Alias is only needed for name resolution during analysis, drop it.
      Ok(PhysicalPlan::SeqScan(schema_info.clone(), table_info.clone()))
    },
    node => unreachable!("Unresolved plan node reached physical planner: {:?}", node),
  }
}

#[cfg(test)]
mod tests {
  use std::rc::Rc;
  use super::*;
  use crate::sql::catalog::{self, RelationType};
  use crate::sql::plan::{LogicalPlan, PhysicalPlan};
  use crate::sql::plan::dsl::*;
  use crate::sql::types::{Field, Fields, Type};
  use crate::storage::db;

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
      catalog::create_relation(
        &txn, "default", table, RelationType::TABLE, fields.clone(), false
      ).unwrap();
    });
  }

  #[test]
  fn test_plan_create_schema() {
    let logical = LogicalPlan::CreateSchema(Rc::new("s".to_string()));
    let (schema, physical) = plan(&logical).unwrap();
    assert_eq!(physical, PhysicalPlan::CreateSchema(Rc::new("s".to_string())));
    assert!(schema.get().is_empty());
  }

  #[test]
  fn test_plan_create_table() {
    let f = Rc::new(Fields::new(vec![Field::new("a".to_string(), Type::INT, false)]));
    let logical = LogicalPlan::CreateTable(
      Rc::new("s".to_string()), Rc::new("t".to_string()), f.clone()
    );
    let (schema, physical) = plan(&logical).unwrap();
    assert_eq!(
      physical,
      PhysicalPlan::CreateTable(Rc::new("s".to_string()), Rc::new("t".to_string()), f)
    );
    assert!(schema.get().is_empty());
  }

  #[test]
  fn test_plan_local_relation() {
    let exprs = Rc::new(vec![vec![int(1), string("x")]]);
    let logical = LogicalPlan::LocalRelation(exprs.clone());
    let (_, physical) = plan(&logical).unwrap();
    assert_eq!(physical, PhysicalPlan::LocalRelation(exprs));
  }

  #[test]
  fn test_plan_filter() {
    let exprs = Rc::new(vec![vec![int(1)]]);
    let child = Rc::new(LogicalPlan::LocalRelation(exprs.clone()));
    let expr = Rc::new(boolean(true));
    let logical = LogicalPlan::Filter(expr.clone(), child);
    let (_, physical) = plan(&logical).unwrap();
    assert_eq!(
      physical,
      PhysicalPlan::Filter(expr, Rc::new(PhysicalPlan::LocalRelation(exprs)))
    );
  }

  #[test]
  fn test_plan_project() {
    let exprs = Rc::new(vec![vec![int(1)]]);
    let child = Rc::new(LogicalPlan::LocalRelation(exprs.clone()));
    let projections = Rc::new(vec![int(1), string("x")]);
    let logical = LogicalPlan::Project(projections.clone(), child);
    let (_, physical) = plan(&logical).unwrap();
    assert_eq!(
      physical,
      PhysicalPlan::Project(projections, Rc::new(PhysicalPlan::LocalRelation(exprs)))
    );
  }

  #[test]
  fn test_plan_limit() {
    let exprs = Rc::new(vec![vec![int(1)]]);
    let child = Rc::new(LogicalPlan::LocalRelation(exprs.clone()));
    let logical = LogicalPlan::Limit(10, child);
    let (_, physical) = plan(&logical).unwrap();
    assert_eq!(physical, PhysicalPlan::Limit(10, Rc::new(PhysicalPlan::LocalRelation(exprs))));
  }

  #[test]
  fn test_plan_subquery_unwrapped() {
    // Subquery is a logical-only alias scope — the physical plan is just the child.
    let exprs = Rc::new(vec![vec![int(1)]]);
    let child = Rc::new(LogicalPlan::LocalRelation(exprs.clone()));
    let logical = LogicalPlan::Subquery(Rc::new("sq".to_string()), child);
    let (_, physical) = plan(&logical).unwrap();
    assert_eq!(physical, PhysicalPlan::LocalRelation(exprs));
  }

  #[test]
  fn test_plan_drop_schema() {
    let mut dbc = init_db();
    dbc.with_txn(false, |txn| {
      let schema_info = Rc::new(catalog::get_schema(&txn, "default").unwrap());
      let logical = LogicalPlan::DropSchema(schema_info.clone(), false);
      let (schema, physical) = plan(&logical).unwrap();
      assert_eq!(physical, PhysicalPlan::DropSchema(schema_info, false));
      assert!(schema.get().is_empty());
    });
  }

  #[test]
  fn test_plan_drop_table() {
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT)]);
    dbc.with_txn(false, |txn| {
      let (schema_info, table_info) = catalog::get_relation(&txn, "default", "t").unwrap();
      let schema_info = Rc::new(schema_info);
      let table_info = Rc::new(table_info);
      let logical = LogicalPlan::DropTable(schema_info.clone(), table_info.clone());
      let (schema, physical) = plan(&logical).unwrap();
      assert_eq!(physical, PhysicalPlan::DropTable(schema_info, table_info));
      assert!(schema.get().is_empty());
    });
  }

  #[test]
  fn test_plan_seq_scan_drops_alias() {
    // TableScan carries an alias used only for name resolution — SeqScan drops it.
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT)]);
    dbc.with_txn(false, |txn| {
      let (schema_info, table_info) = catalog::get_relation(&txn, "default", "t").unwrap();
      let schema_info = Rc::new(schema_info);
      let table_info = Rc::new(table_info);

      let without_alias = LogicalPlan::TableScan(schema_info.clone(), table_info.clone(), None);
      let (_, physical) = plan(&without_alias).unwrap();
      assert_eq!(physical, PhysicalPlan::SeqScan(schema_info.clone(), table_info.clone()));

      let with_alias = LogicalPlan::TableScan(
        schema_info.clone(), table_info.clone(), Some(Rc::new("alias".to_string()))
      );
      let (_, physical) = plan(&with_alias).unwrap();
      assert_eq!(physical, PhysicalPlan::SeqScan(schema_info, table_info));
    });
  }

  #[test]
  fn test_plan_seq_scan_plan_schema() {
    // Fields from a TableScan match the table schema with correct names, types, and nullability.
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT), ("b", Type::TEXT)]);
    dbc.with_txn(false, |txn| {
      let (schema_info, table_info) = catalog::get_relation(&txn, "default", "t").unwrap();
      let logical = LogicalPlan::TableScan(Rc::new(schema_info), Rc::new(table_info), None);
      let (schema, _) = plan(&logical).unwrap();
      assert_eq!(schema.get().len(), 2);
      assert_eq!(schema.get()[0].name(), "a");
      assert_eq!(schema.get()[0].data_type(), &Type::INT);
      assert_eq!(schema.get()[1].name(), "b");
      assert_eq!(schema.get()[1].data_type(), &Type::TEXT);
    });
  }

  #[test]
  fn test_plan_insert_into() {
    let mut dbc = init_db();
    setup_table(&mut dbc, "t", &[("a", Type::INT), ("b", Type::TEXT)]);
    dbc.with_txn(false, |txn| {
      let (schema_info, table_info) = catalog::get_relation(&txn, "default", "t").unwrap();
      let schema_info = Rc::new(schema_info);
      let table_info = Rc::new(table_info);
      let col_positions = Rc::new(vec![0usize, 1usize]);
      let source_exprs = Rc::new(vec![vec![int(1), string("x")]]);
      let source = Rc::new(LogicalPlan::LocalRelation(source_exprs.clone()));

      let logical = LogicalPlan::InsertInto(
        schema_info.clone(), table_info.clone(), col_positions.clone(), source
      );
      let (schema, physical) = plan(&logical).unwrap();
      assert_eq!(
        physical,
        PhysicalPlan::InsertInto(
          schema_info,
          table_info,
          col_positions,
          Rc::new(PhysicalPlan::LocalRelation(source_exprs)),
        )
      );
      assert!(schema.get().is_empty());
    });
  }
}
