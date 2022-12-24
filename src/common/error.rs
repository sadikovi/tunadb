//! Module for various errors used in the project

// Internal type for the Result.
pub type Res<T> = Result<T, Error>;

// List of errors available in the project.
#[derive(Clone, Debug, PartialEq)]
pub enum Error {
  InvalidIdentifier(String /* msg */),
  SchemaAlreadyExists(String /* schema */),
  SchemaDoesNotExist(String /* schema */),
  TableAlreadyExists(String /* schema */, String /* table */),
  TableDoesNotExist(String /* schema */, String /* table */),
  // Internal error for an object that already exists.
  InternalAlreadyExists(String /* msg */),
  // One of the IO, Lock, or UTF8 errors, not user-facing.
  InternalError(String /* msg */),
}

// TODO: remove this.
impl Error {
  pub fn msg(&self) -> &str {
    match self {
      Error::InvalidIdentifier(msg) => msg.as_ref(),
      Error::SchemaAlreadyExists(schema) => schema.as_ref(),
      Error::SchemaDoesNotExist(schema) => schema.as_ref(),
      Error::TableAlreadyExists(_schema, table) => table.as_ref(),
      Error::TableDoesNotExist(_schema, table) => table.as_ref(),
      Error::InternalAlreadyExists(msg) => msg.as_ref(),
      Error::InternalError(msg) => msg.as_ref(),
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
    Error::InternalError(msg.to_owned())
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
