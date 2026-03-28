use tunadb::api::Database;
use tunadb::sql::row::Row;

//===========
// Harness
//===========

fn setup() -> Database {
  Database::open(None).unwrap()
}

// Executes a single SQL statement and returns the result rows.
fn query(db: &mut Database, sql: &str) -> Vec<Row> {
  db.with_transaction(|txn| {
    let result = txn.execute(sql)?;
    Ok(result.rows.map(|r| r.unwrap()).collect())
  }).unwrap()
}

// Executes a single SQL statement and asserts that it returns an error
// containing the expected substring.
fn query_err(db: &mut Database, sql: &str, expected: &str) {
  let result = db.with_transaction(|txn| {
    let result = txn.execute(sql)?;
    Ok(result.rows.map(|r| r.unwrap()).collect::<Vec<_>>())
  });
  let err = result.expect_err(&format!("expected error for: {}", sql));
  let msg = err.to_string();
  assert!(msg.contains(expected), "error message {:?} does not contain {:?}", msg, expected);
}

// Executes multiple SQL statements in the same transaction and returns
// the rows from the last one.
fn query_txn(db: &mut Database, stmts: &[&str]) -> Vec<Row> {
  db.with_transaction(|txn| {
    let mut rows = Vec::new();
    for (i, sql) in stmts.iter().enumerate() {
      let result = txn.execute(sql)?;
      if i == stmts.len() - 1 {
        rows = result.rows.map(|r| r.unwrap()).collect();
      }
    }
    Ok(rows)
  }).unwrap()
}

//==========
// Expected
//==========

// Represents an expected column value in assert_rows.
#[derive(Debug, PartialEq)]
#[allow(dead_code)]
enum Val<'a> {
  Null,
  Bool(bool),
  Int(i32),
  BigInt(i64),
  Float(f32),
  Double(f64),
  Text(&'a str),
}

// Asserts that `rows` matches `expected` exactly, row by row and column by column.
// Val variants drive which getter is called, so they must match the actual column types.
fn assert_rows(rows: &[Row], expected: &[&[Val]]) {
  assert_eq!(rows.len(), expected.len(),
    "expected {} row(s), got {}", expected.len(), rows.len());
  for (i, (row, exp)) in rows.iter().zip(expected.iter()).enumerate() {
    assert_eq!(row.num_fields(), exp.len(),
      "row {}: expected {} column(s), got {}", i, exp.len(), row.num_fields());
    for (j, val) in exp.iter().enumerate() {
      match val {
        Val::Null => assert!(row.is_null(j),
          "row {}, col {}: expected NULL, got a value", i, j),
        Val::Bool(v) => {
          assert!(!row.is_null(j), "row {}, col {}: unexpected NULL", i, j);
          assert_eq!(row.get_bool(j), *v, "row {}, col {}", i, j);
        },
        Val::Int(v) => {
          assert!(!row.is_null(j), "row {}, col {}: unexpected NULL", i, j);
          assert_eq!(row.get_i32(j), *v, "row {}, col {}", i, j);
        },
        Val::BigInt(v) => {
          assert!(!row.is_null(j), "row {}, col {}: unexpected NULL", i, j);
          assert_eq!(row.get_i64(j), *v, "row {}, col {}", i, j);
        },
        Val::Float(v) => {
          assert!(!row.is_null(j), "row {}, col {}: unexpected NULL", i, j);
          assert_eq!(row.get_f32(j), *v, "row {}, col {}", i, j);
        },
        Val::Double(v) => {
          assert!(!row.is_null(j), "row {}, col {}: unexpected NULL", i, j);
          assert_eq!(row.get_f64(j), *v, "row {}, col {}", i, j);
        },
        Val::Text(v) => {
          assert!(!row.is_null(j), "row {}, col {}: unexpected NULL", i, j);
          assert_eq!(row.get_str(j), *v, "row {}, col {}", i, j);
        },
      }
    }
  }
}

//=======
// Tests
//=======

#[test]
fn test_select_literal() {
  let mut db = setup();
  let rows = query(&mut db, "SELECT 1, 'hello'");
  assert_rows(&rows, &[&[Val::Int(1), Val::Text("hello")]]);
}

#[test]
fn test_select_literal_null() {
  let mut db = setup();
  let rows = query(&mut db, "SELECT NULL");
  assert_rows(&rows, &[&[Val::Null]]);
}

#[test]
fn test_select_arithmetic() {
  let mut db = setup();
  let rows = query(&mut db, "SELECT 1 + 2");
  assert_rows(&rows, &[&[Val::Int(3)]]);
}

#[test]
fn test_create_table() {
  let mut db = setup();
  let rows = query(&mut db, "CREATE TABLE t (a INT, b TEXT)");
  assert_rows(&rows, &[]);
}

#[test]
fn test_insert_and_select() {
  let mut db = setup();
  let mut rows = query_txn(&mut db, &[
    "CREATE TABLE t (a INT, b TEXT)",
    "INSERT INTO t VALUES (1, 'hello')",
    "INSERT INTO t VALUES (2, 'world')",
    "SELECT a, b FROM t",
  ]);
  rows.sort_by_key(|r| r.get_i32(0));
  assert_rows(&rows, &[
    &[Val::Int(1), Val::Text("hello")],
    &[Val::Int(2), Val::Text("world")],
  ]);
}

#[test]
fn test_select_empty_table() {
  let mut db = setup();
  query(&mut db, "CREATE TABLE t (a INT)");
  let rows = query(&mut db, "SELECT a FROM t");
  assert_rows(&rows, &[]);
}

#[test]
fn test_select_with_where() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE TABLE t (a INT)",
    "INSERT INTO t VALUES (1)",
    "INSERT INTO t VALUES (2)",
    "INSERT INTO t VALUES (3)",
  ]);
  let rows = query(&mut db, "SELECT a FROM t WHERE a = 2");
  assert_rows(&rows, &[&[Val::Int(2)]]);
}

#[test]
fn test_select_with_limit() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE TABLE t (a INT)",
    "INSERT INTO t VALUES (1)",
    "INSERT INTO t VALUES (2)",
    "INSERT INTO t VALUES (3)",
  ]);
  let rows = query(&mut db, "SELECT a FROM t LIMIT 2");
  assert_eq!(rows.len(), 2);
}

#[test]
fn test_select_expression_on_column() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE TABLE t (a INT)",
    "INSERT INTO t VALUES (3)",
  ]);
  let rows = query(&mut db, "SELECT a + 1 FROM t");
  assert_rows(&rows, &[&[Val::Int(4)]]);
}

#[test]
fn test_select_null_column() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE TABLE t (a INT NULL)",
    "INSERT INTO t (a) VALUES (NULL)",
  ]);
  let rows = query(&mut db, "SELECT a FROM t");
  assert_rows(&rows, &[&[Val::Null]]);
}

#[test]
fn test_insert_explicit_columns() {
  // Insert with explicit column list in reverse order.
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE TABLE t (a INT, b TEXT)",
    "INSERT INTO t (b, a) VALUES ('hello', 42)",
  ]);
  let rows = query(&mut db, "SELECT a, b FROM t");
  assert_rows(&rows, &[&[Val::Int(42), Val::Text("hello")]]);
}

#[test]
fn test_insert_multiple_rows() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE TABLE t (a INT)",
    "INSERT INTO t VALUES (1), (2), (3)",
  ]);
  let mut rows = query(&mut db, "SELECT a FROM t");
  rows.sort_by_key(|r| r.get_i32(0));
  assert_rows(&rows, &[&[Val::Int(1)], &[Val::Int(2)], &[Val::Int(3)]]);
}

#[test]
fn test_insert_returns_rows_affected() {
  let mut db = setup();
  query(&mut db, "CREATE TABLE t (a INT)");
  let rows = query(&mut db, "INSERT INTO t VALUES (1)");
  assert_rows(&rows, &[&[Val::BigInt(1)]]);
}

#[test]
fn test_insert_multiple_rows_returns_count() {
  let mut db = setup();
  query(&mut db, "CREATE TABLE t (a INT)");
  let rows = query(&mut db, "INSERT INTO t VALUES (1), (2), (3)");
  assert_rows(&rows, &[&[Val::BigInt(3)]]);
}

#[test]
fn test_rollback() {
  let mut db = setup();
  query(&mut db, "CREATE TABLE t (a INT)");
  // Explicit rollback — insert should not be visible afterwards.
  db.with_transaction(|txn| -> tunadb::common::error::Res<()> {
    txn.execute("INSERT INTO t VALUES (1)")?;
    txn.rollback();
    Ok(())
  }).unwrap();
  let rows = query(&mut db, "SELECT a FROM t");
  assert_rows(&rows, &[]);
}

#[test]
fn test_show_schemas() {
  let mut db = setup();
  query(&mut db, "CREATE SCHEMA s1");
  query(&mut db, "CREATE SCHEMA s2");
  let rows = query(&mut db, "SHOW SCHEMAS");
  let names: Vec<&str> = rows.iter().map(|r| r.get_str(0)).collect();
  assert!(names.contains(&"s1"));
  assert!(names.contains(&"s2"));
  assert!(names.contains(&"default"));
  assert!(names.contains(&"information_schema"));
}

#[test]
fn test_show_tables() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE TABLE t1 (a INT)",
    "CREATE TABLE t2 (b TEXT)",
  ]);
  let rows = query(&mut db, "SHOW TABLES");
  let names: Vec<&str> = rows.iter().map(|r| r.get_str(1)).collect();
  assert!(names.contains(&"t1"));
  assert!(names.contains(&"t2"));
}

#[test]
fn test_information_schema_schemata() {
  let mut db = setup();
  query(&mut db, "CREATE SCHEMA s1");
  query(&mut db, "CREATE SCHEMA s2");
  let mut rows = query(&mut db, "SELECT schema_name FROM information_schema.schemata");
  rows.sort_by_key(|r| r.get_str(0).to_string());
  let names: Vec<&str> = rows.iter().map(|r| r.get_str(0)).collect();
  assert!(names.contains(&"s1"));
  assert!(names.contains(&"s2"));
  assert!(names.contains(&"default"));
  assert!(names.contains(&"information_schema"));
}

#[test]
fn test_information_schema_relations() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE TABLE t1 (a INT)",
    "CREATE TABLE t2 (b TEXT)",
  ]);
  let sql = "SELECT relation_schema, relation_name FROM information_schema.relations \
    WHERE relation_schema = 'default'";
  let rows = query(&mut db, sql);
  let names: Vec<(&str, &str)> = rows.iter().map(|r| (r.get_str(0), r.get_str(1))).collect();
  assert!(names.contains(&("default", "t1")));
  assert!(names.contains(&("default", "t2")));
}

#[test]
fn test_select_all_types() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE TABLE t (a INT, b BIGINT, c FLOAT, d DOUBLE, e BOOL, f TEXT)",
    "INSERT INTO t VALUES (1, 2, CAST(1.5 AS FLOAT), 2.5, TRUE, 'hello')",
  ]);
  let rows = query(&mut db, "SELECT a, b, c, d, e, f FROM t");
  assert_rows(&rows, &[&[
    Val::Int(1),
    Val::BigInt(2),
    Val::Float(1.5),
    Val::Double(2.5),
    Val::Bool(true),
    Val::Text("hello"),
  ]]);
}

#[test]
fn test_create_schema() {
  let mut db = setup();
  query(&mut db, "CREATE SCHEMA myschema");
  let rows = query(&mut db, "SHOW SCHEMAS");
  let names: Vec<&str> = rows.iter().map(|r| r.get_str(0)).collect();
  assert!(names.contains(&"myschema"));
}

#[test]
fn test_create_schema_duplicate_error() {
  let mut db = setup();
  query(&mut db, "CREATE SCHEMA s");
  query_err(&mut db, "CREATE SCHEMA s", "already exists");
}

#[test]
fn test_drop_schema() {
  let mut db = setup();
  query(&mut db, "CREATE SCHEMA s");
  query(&mut db, "DROP SCHEMA s");
  let rows = query(&mut db, "SHOW SCHEMAS");
  let names: Vec<&str> = rows.iter().map(|r| r.get_str(0)).collect();
  assert!(!names.contains(&"s"));
}

#[test]
fn test_drop_schema_cascade_drops_tables() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE SCHEMA s",
    "CREATE TABLE s.t (a INT)",
  ]);
  query(&mut db, "DROP SCHEMA s CASCADE");
  // Schema is gone.
  let schemas = query(&mut db, "SHOW SCHEMAS");
  let schema_names: Vec<&str> = schemas.iter().map(|r| r.get_str(0)).collect();
  assert!(!schema_names.contains(&"s"));
  // Table is also gone from the catalog.
  let sql = "SELECT relation_name FROM information_schema.relations \
    WHERE relation_schema = 's'";
  let rows = query(&mut db, sql);
  assert_rows(&rows, &[]);
}

#[test]
fn test_drop_schema_not_exists_error() {
  let mut db = setup();
  query_err(&mut db, "DROP SCHEMA nonexistent", "does not exist");
}

#[test]
fn test_create_table_duplicate_error() {
  let mut db = setup();
  query(&mut db, "CREATE TABLE t (a INT)");
  query_err(&mut db, "CREATE TABLE t (a INT)", "already exists");
}

#[test]
fn test_drop_table() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE TABLE t (a INT)",
    "INSERT INTO t VALUES (1)",
  ]);
  query(&mut db, "DROP TABLE t");
  // Table no longer appears in the catalog.
  let sql = "SELECT relation_name FROM information_schema.relations \
    WHERE relation_schema = 'default'";
  let rows = query(&mut db, sql);
  let names: Vec<&str> = rows.iter().map(|r| r.get_str(0)).collect();
  assert!(!names.contains(&"t"));
}

#[test]
fn test_drop_table_not_exists_error() {
  let mut db = setup();
  query_err(&mut db, "DROP TABLE nonexistent", "does not exist");
}

#[test]
fn test_show_schemas_after_drop() {
  let mut db = setup();
  query(&mut db, "CREATE SCHEMA s");
  query(&mut db, "DROP SCHEMA s");
  let rows = query(&mut db, "SHOW SCHEMAS");
  let names: Vec<&str> = rows.iter().map(|r| r.get_str(0)).collect();
  assert!(!names.contains(&"s"));
  // Built-in schemas still present.
  assert!(names.contains(&"default"));
  assert!(names.contains(&"information_schema"));
}

#[test]
fn test_show_tables_after_drop() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE TABLE t1 (a INT)",
    "CREATE TABLE t2 (b TEXT)",
  ]);
  query(&mut db, "DROP TABLE t1");
  let rows = query(&mut db, "SHOW TABLES");
  let names: Vec<&str> = rows.iter().map(|r| r.get_str(1)).collect();
  assert!(!names.contains(&"t1"));
  assert!(names.contains(&"t2"));
}

#[test]
fn test_describe_table() {
  let mut db = setup();
  query(&mut db, "CREATE TABLE t (id INT, name TEXT NOT NULL, score DOUBLE)");
  let rows = query(&mut db, "DESCRIBE t");
  // Returns one row per column: (table_schema, table_name, column_name, data_type, is_nullable, is_internal).
  // _rowid_ is an internal pseudo-column appended at the end.
  assert_rows(&rows, &[
    &[Val::Text("default"), Val::Text("t"), Val::Text("id"),       Val::Text("INT"),    Val::Text("YES"), Val::Text("NO")],
    &[Val::Text("default"), Val::Text("t"), Val::Text("name"),     Val::Text("TEXT"),   Val::Text("NO"),  Val::Text("NO")],
    &[Val::Text("default"), Val::Text("t"), Val::Text("score"),    Val::Text("DOUBLE"), Val::Text("YES"), Val::Text("NO")],
    &[Val::Text("default"), Val::Text("t"), Val::Text("_rowid_"),  Val::Text("BIGINT"), Val::Text("NO"),  Val::Text("YES")],
  ]);
}

#[test]
fn test_describe_table_schema_qualified() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE SCHEMA s",
    "CREATE TABLE s.t (x BIGINT NOT NULL)",
  ]);
  let rows = query(&mut db, "DESCRIBE s.t");
  assert_rows(&rows, &[
    &[Val::Text("s"), Val::Text("t"), Val::Text("x"),        Val::Text("BIGINT"), Val::Text("NO"), Val::Text("NO")],
    &[Val::Text("s"), Val::Text("t"), Val::Text("_rowid_"),  Val::Text("BIGINT"), Val::Text("NO"), Val::Text("YES")],
  ]);
}

#[test]
fn test_describe_table_not_found_error() {
  let mut db = setup();
  query_err(&mut db, "DESCRIBE nonexistent", "does not exist");
}

#[test]
fn test_describe_table_schema_not_found_error() {
  let mut db = setup();
  query_err(&mut db, "DESCRIBE nonexistent.t", "does not exist");
}

#[test]
fn test_show_tables_in_schema() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE SCHEMA s",
    "CREATE TABLE s.t1 (a INT)",
    "CREATE TABLE t2 (b TEXT)",
  ]);
  let rows = query(&mut db, "SHOW TABLES IN s");
  let names: Vec<&str> = rows.iter().map(|r| r.get_str(1)).collect();
  assert!(names.contains(&"t1"));
  assert!(!names.contains(&"t2"));
}

#[test]
fn test_show_tables_in_schema_not_found_error() {
  let mut db = setup();
  query_err(&mut db, "SHOW TABLES IN nonexistent", "does not exist");
}

#[test]
fn test_information_schema_columns() {
  let mut db = setup();
  query(&mut db, "CREATE TABLE t (a INT, b TEXT NOT NULL)");
  let sql = "SELECT column_name, data_type, is_nullable \
    FROM information_schema.columns \
    WHERE table_schema = 'default' AND table_name = 't'";
  let rows = query(&mut db, sql);
  assert_rows(&rows, &[
    &[Val::Text("a"),        Val::Text("INT"),    Val::Text("YES")],
    &[Val::Text("b"),        Val::Text("TEXT"),   Val::Text("NO")],
    &[Val::Text("_rowid_"),  Val::Text("BIGINT"), Val::Text("NO")],
  ]);
}

#[test]
fn test_insert_not_null_violation_error() {
  let mut db = setup();
  query(&mut db, "CREATE TABLE t (a INT NOT NULL, b TEXT)");
  query_err(&mut db, "INSERT INTO t VALUES (NULL, 'hello')", "NOT NULL constraint");
}

#[test]
fn test_insert_not_null_violation_explicit_columns_error() {
  let mut db = setup();
  query(&mut db, "CREATE TABLE t (a INT NOT NULL, b TEXT)");
  query_err(&mut db, "INSERT INTO t (a) VALUES (NULL)", "NOT NULL constraint");
}

#[test]
fn test_insert_nullable_column_allows_null() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE TABLE t (a INT NOT NULL, b TEXT)",
    "INSERT INTO t VALUES (1, NULL)",
  ]);
  let rows = query(&mut db, "SELECT a, b FROM t");
  assert_rows(&rows, &[&[Val::Int(1), Val::Null]]);
}

#[test]
fn test_insert_not_null_omitted_column_allows_null() {
  // Omitting a nullable column from the explicit list inserts NULL — allowed.
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE TABLE t (a INT NOT NULL, b TEXT)",
    "INSERT INTO t (a) VALUES (42)",
  ]);
  let rows = query(&mut db, "SELECT a, b FROM t");
  assert_rows(&rows, &[&[Val::Int(42), Val::Null]]);
}

#[test]
fn test_insert_not_null_omitted_column_error() {
  // Omitting a NOT NULL column from the explicit list should fail.
  let mut db = setup();
  query(&mut db, "CREATE TABLE t (a INT, b TEXT NOT NULL)");
  query_err(&mut db, "INSERT INTO t (a) VALUES (1)", "NOT NULL constraint");
}

#[test]
fn test_explain_returns_plan_column() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE TABLE t (a INT, b TEXT)",
    "INSERT INTO t VALUES (1, 'x')",
  ]);
  let rows = query(&mut db, "EXPLAIN SELECT a FROM t WHERE a = 1");
  assert!(!rows.is_empty());
  // All rows have exactly one TEXT column.
  for row in &rows {
    assert_eq!(row.num_fields(), 1);
  }
  let plan: Vec<&str> = rows.iter().map(|r| r.get_str(0)).collect();
  let joined = plan.join("\n");
  assert!(joined.contains("Project"), "expected Project in plan: {}", joined);
  assert!(joined.contains("Filter"), "expected Filter in plan: {}", joined);
  assert!(joined.contains("SeqScan"), "expected SeqScan in plan: {}", joined);
}

#[test]
fn test_explain_extended_contains_all_sections() {
  let mut db = setup();
  query(&mut db, "CREATE TABLE t (a INT)");
  let rows = query(&mut db, "EXPLAIN EXTENDED SELECT a FROM t");
  let plan: Vec<&str> = rows.iter().map(|r| r.get_str(0)).collect();
  let joined = plan.join("\n");
  assert!(joined.contains("== Unresolved Plan =="), "missing unresolved section: {}", joined);
  assert!(joined.contains("== Resolved Plan =="), "missing resolved section: {}", joined);
  assert!(joined.contains("== Physical Plan =="), "missing physical section: {}", joined);
}

#[test]
fn test_explain_extended_unresolved_has_unresolved_nodes() {
  let mut db = setup();
  query(&mut db, "CREATE TABLE t (a INT)");
  let rows = query(&mut db, "EXPLAIN EXTENDED SELECT a FROM t");
  let plan: Vec<&str> = rows.iter().map(|r| r.get_str(0)).collect();
  let joined = plan.join("\n");
  // Unresolved section uses Unresolved* node names.
  let unresolved_section = joined.split("== Resolved Plan ==").next().unwrap();
  assert!(unresolved_section.contains("Unresolved"), "expected Unresolved nodes: {}", unresolved_section);
  // Physical section uses physical node names (no Unresolved prefix).
  let physical_section = joined.split("== Physical Plan ==").nth(1).unwrap();
  assert!(!physical_section.contains("Unresolved"), "unexpected Unresolved in physical: {}", physical_section);
  assert!(physical_section.contains("SeqScan"), "expected SeqScan in physical: {}", physical_section);
}

#[test]
fn test_explain_show_tables() {
  // EXPLAIN works on non-SELECT statements too.
  let mut db = setup();
  let rows = query(&mut db, "EXPLAIN SHOW TABLES");
  assert!(!rows.is_empty());
  let joined: Vec<&str> = rows.iter().map(|r| r.get_str(0)).collect();
  let plan = joined.join("\n");
  assert!(joined.iter().any(|l| !l.is_empty()), "plan should not be empty: {}", plan);
}

//===========
// _rowid_
//===========

#[test]
fn test_rowid_explicit_select() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE TABLE t (a INT)",
    "INSERT INTO t VALUES (42)",
  ]);
  // _rowid_ can be selected explicitly and returns a non-null BIGINT value.
  let rows = query(&mut db, "SELECT _rowid_ FROM t");
  assert_eq!(rows.len(), 1);
  assert!(!rows[0].is_null(0));
}

#[test]
fn test_rowid_not_in_star() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE TABLE t (a INT)",
    "INSERT INTO t VALUES (1)",
  ]);
  // SELECT * must not include _rowid_.
  let rows = query(&mut db, "SELECT * FROM t");
  assert_eq!(rows.len(), 1);
  assert_eq!(rows[0].num_fields(), 1);
  assert_eq!(rows[0].get_i32(0), 1);
}

#[test]
fn test_rowid_unique_per_row() {
  let mut db = setup();
  query_txn(&mut db, &[
    "CREATE TABLE t (a INT)",
    "INSERT INTO t VALUES (1)",
    "INSERT INTO t VALUES (2)",
  ]);
  let rows = query(&mut db, "SELECT _rowid_ FROM t");
  assert_eq!(rows.len(), 2);
  // Each row must have a distinct rowid.
  let id0 = rows[0].get_i64(0);
  let id1 = rows[1].get_i64(0);
  assert_ne!(id0, id1);
}

#[test]
fn test_rowid_reserved_name_error() {
  let mut db = setup();
  query_err(&mut db, "CREATE TABLE t (_rowid_ INT)", "reserved");
}
