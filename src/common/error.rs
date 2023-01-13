//! Module for various errors used in the project

// Internal type for the Result.
pub type Res<T> = Result<T, Error>;

// List of errors available in the project.
#[derive(Clone, Debug, PartialEq)]
pub enum Error {
  // SQL errors.
  InvalidIdentifier(String /* msg */),
  DuplicateFieldName(String /* field name */),
  SchemaAlreadyExists(String /* schema */),
  SchemaDoesNotExist(String /* schema */),
  SchemaIsNotEmpty(String /* schema */),
  TableAlreadyExists(String /* schema */, String /* table */),
  TableDoesNotExist(String /* schema */, String /* table */),
  TableInvalidSchema(String /* msg */),
  OperationIsNotAllowed(String /* msg */),

  // Internal errors.

  // Internal error for an object that already exists.
  InternalAlreadyExists(String /* msg */),
  // One of the IO, Lock, or UTF8 errors, not user-facing.
  InternalError(String /* msg */),
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
