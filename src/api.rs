//! High-level public API for tunadb.
//!
//! ## Basic usage
//!
//! ```no_run
//! use tunadb::api::Database;
//!
//! let mut db = Database::open(None).unwrap();
//! db.with_transaction(|txn| {
//!   txn.execute("CREATE TABLE t (id INT, name TEXT)")?;
//!   txn.execute("INSERT INTO t VALUES (1, 'alice')")?;
//!   let result = txn.execute("SELECT id, name FROM t")?;
//!   Ok(result)
//! }).unwrap();
//! ```
//!
//! ## Explicit rollback
//!
//! Call `txn.rollback()` to discard changes and return `Ok` from the closure.
//! The transaction is already finalised, so `with_transaction` will not commit.
//!
//! ```no_run
//! use tunadb::api::Database;
//!
//! let mut db = Database::open(None).unwrap();
//! db.with_transaction(|txn| {
//!   txn.execute("INSERT INTO t VALUES (1)")?;
//!   txn.rollback(); // discard the insert
//!   Ok(())
//! }).unwrap();
//! ```
//!
//! Returning `Err` from the closure also triggers a rollback automatically.

use std::cell::RefCell;
use crate::common::error::Res;
use crate::sql::{analysis, catalog, exec, parser, planning};
use crate::sql::exec::RowIter;
use crate::sql::session::Session;
use crate::sql::types::Fields;
use crate::storage::db;
use crate::storage::txn::TransactionRef;

/// The result of executing a SQL statement.
/// `fields` describes the output schema; `rows` is the row iterator.
pub struct QueryResult {
  pub fields: Fields,
  pub rows: RowIter,
}

/// A transaction handle valid for the duration of a `with_transaction` closure.
pub struct Txn {
  txn: TransactionRef,
  session: Session,
}

impl Txn {
  /// Executes a single SQL statement and returns the result.
  pub fn execute(&self, sql: &str) -> Res<QueryResult> {
    let mut plans = parser::parse(sql)?;
    if plans.len() != 1 {
      return Err(crate::common::error::Error::SQLAnalysisError(
        format!("execute() expects a single statement, got {}", plans.len())
      ));
    }
    let logical = analysis::analyse(&self.session, &self.txn, plans.remove(0))?;
    let (fields, physical) = planning::plan(&logical)?;
    let rows = exec::execute(&self.session, &self.txn, &physical)?;
    Ok(QueryResult { fields, rows })
  }

  /// Explicitly rolls back the transaction.
  /// See the [module-level documentation](crate::api) for usage examples.
  pub fn rollback(&self) {
    self.txn.borrow_mut().rollback();
  }
}

/// A tunadb database handle.
pub struct Database {
  db: db::DB,
}

impl Database {
  /// Opens a database at the given path, or an in-memory database if `path` is `None`.
  /// Always initialises the catalog and ensures the `default` schema exists.
  pub fn open(path: Option<&str>) -> Res<Self> {
    let mut db = db::open(path).try_build()?;
    db.with_txn(true, |txn| {
      if !catalog::catalog_exists(&txn).unwrap() {
        catalog::init_catalog(&txn).unwrap();
      }
      catalog::create_schema(&txn, "default", true).unwrap();
    });
    Ok(Self { db })
  }

  /// Runs `f` inside a transaction. Commits on `Ok`, rolls back on `Err`.
  /// Explicit rollback is also possible via `Txn::rollback`.
  pub fn with_transaction<F, T>(&mut self, f: F) -> Res<T>
    where F: Fn(&Txn) -> Res<T>
  {
    let outcome: RefCell<Option<Res<T>>> = RefCell::new(None);
    self.db.with_txn(false, |txn_ref| {
      let txn = Txn { txn: txn_ref.clone(), session: Session::builder().build() };
      let res = f(&txn);
      if res.is_ok() && !txn_ref.borrow().is_finalised() {
        txn_ref.borrow_mut().commit();
      }
      *outcome.borrow_mut() = Some(res);
    });
    outcome.into_inner().expect("with_transaction closure was not called")
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::sql::plan::DEFAULT_EXPRESSION_NAME;

  fn setup() -> Database {
    Database::open(None).unwrap()
  }

  #[test]
  fn test_database_open() {
    // Opening an in-memory database should work and allow table creation immediately.
    let mut db = setup();
    db.with_transaction(|txn| {
      txn.execute("CREATE TABLE t (a INT)")
    }).unwrap();
  }

  #[test]
  fn test_txn_commit_persists() {
    let mut db = setup();
    db.with_transaction(|txn| {
      txn.execute("CREATE TABLE t (a INT)")?;
      txn.execute("INSERT INTO t VALUES (1)")
    }).unwrap();

    let rows = db.with_transaction(|txn| {
      let result = txn.execute("SELECT a FROM t")?;
      Ok(result.rows.map(|r| r.unwrap()).collect::<Vec<_>>())
    }).unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].get_i32(0), 1);
  }

  #[test]
  fn test_txn_error_rolls_back() {
    let mut db = setup();
    db.with_transaction(|txn| {
      txn.execute("CREATE TABLE t (a INT)")
    }).unwrap();

    // Return Err to trigger rollback.
    let _ = db.with_transaction(|txn| -> Res<()> {
      txn.execute("INSERT INTO t VALUES (1)")?;
      Err(crate::common::error::Error::SQLAnalysisError("forced rollback".to_string()))
    });

    let rows = db.with_transaction(|txn| {
      let result = txn.execute("SELECT a FROM t")?;
      Ok(result.rows.map(|r| r.unwrap()).collect::<Vec<_>>())
    }).unwrap();
    assert!(rows.is_empty());
  }

  #[test]
  fn test_txn_explicit_rollback() {
    let mut db = setup();
    db.with_transaction(|txn| {
      txn.execute("CREATE TABLE t (a INT)")
    }).unwrap();

    db.with_transaction(|txn| -> Res<()> {
      txn.execute("INSERT INTO t VALUES (1)")?;
      txn.rollback();
      Ok(())
    }).unwrap();

    let rows = db.with_transaction(|txn| {
      let result = txn.execute("SELECT a FROM t")?;
      Ok(result.rows.map(|r| r.unwrap()).collect::<Vec<_>>())
    }).unwrap();
    assert!(rows.is_empty());
  }

  #[test]
  fn test_query_result_fields_for_table_scan() {
    let mut db = setup();
    db.with_transaction(|txn| txn.execute("CREATE TABLE t (a INT, b TEXT)")).unwrap();
    let fields = db.with_transaction(|txn| {
      Ok(txn.execute("SELECT a, b FROM t")?.fields)
    }).unwrap();
    assert_eq!(fields.get().len(), 2);
    assert_eq!(fields.get()[0].name(), "a");
    assert_eq!(fields.get()[1].name(), "b");
  }

  #[test]
  fn test_query_result_fields_for_literals() {
    let mut db = setup();
    let fields = db.with_transaction(|txn| {
      Ok(txn.execute("SELECT 1, 'hello'")?.fields)
    }).unwrap();
    assert_eq!(fields.get().len(), 2);
    assert_eq!(fields.get()[0].name(), DEFAULT_EXPRESSION_NAME);
    assert_eq!(fields.get()[1].name(), DEFAULT_EXPRESSION_NAME);
  }

  #[test]
  fn test_query_result_fields_for_alias() {
    let mut db = setup();
    let fields = db.with_transaction(|txn| {
      Ok(txn.execute("SELECT 1 + 2 AS total")?.fields)
    }).unwrap();
    assert_eq!(fields.get().len(), 1);
    assert_eq!(fields.get()[0].name(), "total");
  }

  #[test]
  fn test_execute_rejects_multiple_statements() {
    let mut db = setup();
    let err = db.with_transaction(|txn| txn.execute("SELECT 1; SELECT 2"));
    assert!(err.is_err());
  }
}
