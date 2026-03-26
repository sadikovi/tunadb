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
  let rows = query(&mut db, "SELECT relation_schema, relation_name FROM information_schema.relations WHERE relation_schema = 'default'");
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
