//! Module for various errors used in the project

// Internal type for the Result.
pub type Res<T> = Result<T, Error>;

// List of errors available in the project.
#[derive(Clone, Debug, PartialEq)]
pub enum Error {
  // SQL parser errors.
  SQLParseError(String /* error message */),

  // SQL analysis errors.
  SQLAnalysisError(String /* error message */),
  SQLAnalysisExpressionError(String /* error message */),

  SQLExecutionError(String /* error message */),

  // SQL catalog errors.
  OperationIsNotAllowed(String /* error message */),
  SchemaAlreadyExists(String /* schema */),
  SchemaDoesNotExist(String /* schema */),
  SchemaIsNotEmpty(String /* schema */),
  RelationAlreadyExists(String /* schema name */, String /* table name */),
  RelationDoesNotExist(String /* schema name */, String /* relation name */),
  RelationInvalidSchema(String /* error message */),

  // Internal errors.

  // Internal error for an object that already exists.
  InternalAlreadyExists(String /* msg */),
  // One of the IO, Lock, or UTF8 errors, not user-facing.
  InternalError(String /* msg */),
}

impl std::fmt::Display for Error {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Error::SQLParseError(msg) => write!(f, "Parse error: {}", msg),
      Error::SQLAnalysisError(msg) => write!(f, "Analysis error: {}", msg),
      Error::SQLAnalysisExpressionError(msg) => write!(f, "Analysis error: {}", msg),
      Error::SQLExecutionError(msg) => write!(f, "Execution error: {}", msg),
      Error::OperationIsNotAllowed(msg) => write!(f, "Operation not allowed: {}", msg),
      Error::SchemaAlreadyExists(s) => write!(f, "Schema already exists: {}", s),
      Error::SchemaDoesNotExist(s) => write!(f, "Schema does not exist: {}", s),
      Error::SchemaIsNotEmpty(s) => write!(f, "Schema is not empty: {}", s),
      Error::RelationAlreadyExists(s, t) => write!(f, "Relation already exists: {}.{}", s, t),
      Error::RelationDoesNotExist(s, t) => write!(f, "Relation does not exist: {}.{}", s, t),
      Error::RelationInvalidSchema(msg) => write!(f, "Invalid schema: {}", msg),
      Error::InternalAlreadyExists(msg) => write!(f, "Internal error (already exists): {}", msg),
      Error::InternalError(msg) => write!(f, "Internal error: {}", msg),
    }
  }
}

// Creates an internal error with the provided message.
impl From<String> for Error {
  fn from(msg: String) -> Self {
    Error::InternalError(msg)
  }
}

// Creates an internal error with the provided message.
impl From<&str> for Error {
  fn from(msg: &str) -> Self {
    Error::InternalError(msg.to_string())
  }
}

impl From<std::io::Error> for Error {
  fn from(err: std::io::Error) -> Self {
    Error::InternalError(format!("IO Error: {}", err.to_string()))
  }
}

impl<T> From<std::sync::PoisonError<T>> for Error {
  fn from(err: std::sync::PoisonError<T>) -> Self {
    Error::InternalError(format!("Lock Error: {}", err.to_string()))
  }
}

impl From<std::string::FromUtf8Error> for Error {
  fn from(err: std::string::FromUtf8Error) -> Self {
    Error::InternalError(format!("UTF8 Conversion Error: {}", err.to_string()))
  }
}

impl From<std::str::Utf8Error> for Error {
  fn from(err: std::str::Utf8Error) -> Self {
    Error::InternalError(format!("UTF8 Conversion Error: {}", err.to_string()))
  }
}
