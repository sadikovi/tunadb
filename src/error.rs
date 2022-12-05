//! Module for various errors used in the project

// List of errors available in the project.
#[derive(Clone, Debug, PartialEq)]
pub enum Error {
  // Generic error for an object that already exists.
  InternalAlreadyExists(String),
  // One of the IO, Lock, or UTF8 errors, not user-facing.
  InternalError(String),
}

impl Error {
  pub fn msg(&self) -> &str {
    match self {
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

macro_rules! internal_err {
  ($fmt:expr) =>
    (crate::error::Error::InternalError($fmt.to_owned()));
  ($fmt:expr, $($args:expr),*) =>
    (crate::error::Error::InternalError(format!($fmt, $($args),*)));
}

macro_rules! already_exists_err {
  ($fmt:expr) =>
    (crate::error::Error::InternalAlreadyExists($fmt.to_owned()));
  ($fmt:expr, $($args:expr),*) =>
    (crate::error::Error::InternalAlreadyExists(format!($fmt, $($args),*)));
}

// Internal type for the Result.
pub type Res<T> = Result<T, Error>;

macro_rules! res {
  ($e:expr) => ($e.unwrap());
  ($e:expr, $fmt:expr) => ($e.expect(&format!($fmt)));
  ($e:expr, $fmt:expr, $($args:expr),*) => ($e.expect(&format!($fmt, $($args),*)));
}
