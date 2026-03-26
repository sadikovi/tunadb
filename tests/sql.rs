use tunadb::sql::{analysis, exec, parser, planning};
use tunadb::sql::catalog;
use tunadb::sql::row::Row;
use tunadb::sql::session::Session;
use tunadb::storage::db;
use tunadb::storage::txn::TransactionRef;

//===========
// Harness
//===========

fn setup() -> db::DB {
  let mut dbc = db::open(None).try_build().unwrap();
  dbc.with_txn(true, |txn| {
    catalog::init_catalog(&txn).unwrap();
    catalog::create_schema(&txn, "default", false).unwrap();
  });
  dbc
}

// Runs a closure with a transaction. Multiple queries can be issued against
// the same txn. Pass auto_commit=true to persist changes after the closure.
fn with_txn<F: Fn(&TransactionRef)>(db: &mut db::DB, auto_commit: bool, f: F) {
  db.with_txn(auto_commit, |txn| f(&txn));
}

// Executes a single SQL statement and returns the result rows.
fn query(txn: &TransactionRef, sql: &str) -> Vec<Row> {
  let session = Session::new();
  let mut plans = parser::parse(sql).expect("parse failed");
  assert_eq!(plans.len(), 1, "query() expects a single statement, got {}", plans.len());
  let logical = analysis::analyse(&session, txn, plans.remove(0)).expect("analysis failed");
  let physical = planning::plan(&logical).expect("planning failed");
  exec::execute(&session, txn, &physical)
    .expect("execution failed")
    .map(|r| r.expect("row error"))
    .collect()
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
      "row {i}: expected {} column(s), got {}", exp.len(), row.num_fields());
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
  with_txn(&mut db, false, |txn| {
    let rows = query(txn, "SELECT 1, 'hello'");
    assert_rows(&rows, &[&[Val::Int(1), Val::Text("hello")]]);
  });
}

#[test]
fn test_select_literal_null() {
  let mut db = setup();
  with_txn(&mut db, false, |txn| {
    let rows = query(txn, "SELECT NULL");
    assert_rows(&rows, &[&[Val::Null]]);
  });
}

#[test]
fn test_select_arithmetic() {
  let mut db = setup();
  with_txn(&mut db, false, |txn| {
    let rows = query(txn, "SELECT 1 + 2");
    assert_rows(&rows, &[&[Val::Int(3)]]);
  });
}

#[test]
fn test_create_table() {
  let mut db = setup();
  with_txn(&mut db, true, |txn| {
    let rows = query(txn, "CREATE TABLE t (a INT, b TEXT)");
    assert_rows(&rows, &[]);
  });
}

#[test]
fn test_insert_and_select() {
  let mut db = setup();
  with_txn(&mut db, true, |txn| {
    query(txn, "CREATE TABLE t (a INT, b TEXT)");
    query(txn, "INSERT INTO t VALUES (1, 'hello')");
    query(txn, "INSERT INTO t VALUES (2, 'world')");
  });
  with_txn(&mut db, false, |txn| {
    let mut rows = query(txn, "SELECT a, b FROM t");
    rows.sort_by_key(|r| r.get_i32(0));
    assert_rows(&rows, &[
      &[Val::Int(1), Val::Text("hello")],
      &[Val::Int(2), Val::Text("world")],
    ]);
  });
}

#[test]
fn test_select_empty_table() {
  let mut db = setup();
  with_txn(&mut db, true, |txn| {
    query(txn, "CREATE TABLE t (a INT)");
  });
  with_txn(&mut db, false, |txn| {
    let rows = query(txn, "SELECT a FROM t");
    assert_rows(&rows, &[]);
  });
}

#[test]
fn test_select_with_where() {
  let mut db = setup();
  with_txn(&mut db, true, |txn| {
    query(txn, "CREATE TABLE t (a INT)");
    query(txn, "INSERT INTO t VALUES (1)");
    query(txn, "INSERT INTO t VALUES (2)");
    query(txn, "INSERT INTO t VALUES (3)");
  });
  with_txn(&mut db, false, |txn| {
    let rows = query(txn, "SELECT a FROM t WHERE a = 2");
    assert_rows(&rows, &[&[Val::Int(2)]]);
  });
}

#[test]
fn test_select_with_limit() {
  let mut db = setup();
  with_txn(&mut db, true, |txn| {
    query(txn, "CREATE TABLE t (a INT)");
    query(txn, "INSERT INTO t VALUES (1)");
    query(txn, "INSERT INTO t VALUES (2)");
    query(txn, "INSERT INTO t VALUES (3)");
  });
  with_txn(&mut db, false, |txn| {
    let rows = query(txn, "SELECT a FROM t LIMIT 2");
    assert_eq!(rows.len(), 2);
  });
}

#[test]
fn test_select_expression_on_column() {
  let mut db = setup();
  with_txn(&mut db, true, |txn| {
    query(txn, "CREATE TABLE t (a INT)");
    query(txn, "INSERT INTO t VALUES (3)");
  });
  with_txn(&mut db, false, |txn| {
    let rows = query(txn, "SELECT a + 1 FROM t");
    assert_rows(&rows, &[&[Val::Int(4)]]);
  });
}

#[test]
fn test_select_null_column() {
  let mut db = setup();
  with_txn(&mut db, true, |txn| {
    query(txn, "CREATE TABLE t (a INT NULL)");
    query(txn, "INSERT INTO t (a) VALUES (NULL)");
  });
  with_txn(&mut db, false, |txn| {
    let rows = query(txn, "SELECT a FROM t");
    assert_rows(&rows, &[&[Val::Null]]);
  });
}

#[test]
fn test_insert_explicit_columns() {
  // Insert with explicit column list in reverse order.
  let mut db = setup();
  with_txn(&mut db, true, |txn| {
    query(txn, "CREATE TABLE t (a INT, b TEXT)");
    query(txn, "INSERT INTO t (b, a) VALUES ('hello', 42)");
  });
  with_txn(&mut db, false, |txn| {
    let rows = query(txn, "SELECT a, b FROM t");
    assert_rows(&rows, &[&[Val::Int(42), Val::Text("hello")]]);
  });
}

#[test]
fn test_insert_multiple_rows() {
  let mut db = setup();
  with_txn(&mut db, true, |txn| {
    query(txn, "CREATE TABLE t (a INT)");
    query(txn, "INSERT INTO t VALUES (1), (2), (3)");
  });
  with_txn(&mut db, false, |txn| {
    let mut rows = query(txn, "SELECT a FROM t");
    rows.sort_by_key(|r| r.get_i32(0));
    assert_rows(&rows, &[&[Val::Int(1)], &[Val::Int(2)], &[Val::Int(3)]]);
  });
}

#[test]
fn test_rollback() {
  let mut db = setup();
  with_txn(&mut db, true, |txn| {
    query(txn, "CREATE TABLE t (a INT)");
  });
  // auto_commit=false means rollback.
  with_txn(&mut db, false, |txn| {
    query(txn, "INSERT INTO t VALUES (1)");
  });
  with_txn(&mut db, false, |txn| {
    let rows = query(txn, "SELECT a FROM t");
    assert_rows(&rows, &[]);
  });
}

#[test]
fn test_select_all_types() {
  let mut db = setup();
  with_txn(&mut db, true, |txn| {
    query(txn, "CREATE TABLE t (a INT, b BIGINT, c FLOAT, d DOUBLE, e BOOL, f TEXT)");
    query(txn, "INSERT INTO t VALUES (1, 2, CAST(1.5 AS FLOAT), 2.5, TRUE, 'hello')");
  });
  with_txn(&mut db, false, |txn| {
    let rows = query(txn, "SELECT a, b, c, d, e, f FROM t");
    assert_rows(&rows, &[&[
      Val::Int(1),
      Val::BigInt(2),
      Val::Float(1.5),
      Val::Double(2.5),
      Val::Bool(true),
      Val::Text("hello"),
    ]]);
  });
}
