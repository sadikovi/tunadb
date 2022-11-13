//! Module for various errors used in the project

// Generic error for the crate.
#[derive(Clone, Debug, PartialEq)]
pub struct Error {
  msg: String
}

impl Error {
  pub fn msg(&self) -> &str {
    self.msg.as_ref()
  }
}

impl From<String> for Error {
  fn from(msg: String) -> Self {
    Self { msg }
  }
}

impl From<&str> for Error {
  fn from(msg: &str) -> Self {
    Self { msg: msg.to_owned() }
  }
}

impl From<std::io::Error> for Error {
  fn from(err: std::io::Error) -> Self {
    Self { msg: format!("IO Error: {}", err.to_string()) }
  }
}

impl<T> From<std::sync::PoisonError<T>> for Error {
  fn from(err: std::sync::PoisonError<T>) -> Self {
    Self { msg: format!("Lock Error: {}", err.to_string()) }
  }
}

impl From<std::string::FromUtf8Error> for Error {
  fn from(err: std::string::FromUtf8Error) -> Self {
    Self { msg: format!("UTF8: {}", err.to_string()) }
  }
}

macro_rules! err {
  ($fmt:expr) => (crate::error::Error::from($fmt.to_owned()));
  ($fmt:expr, $($args:expr),*) => (crate::error::Error::from(format!($fmt, $($args),*)));
  ($e:expr, $fmt:expr) => (crate::error::Error::from($fmt.to_owned(), $e));
  ($e:ident, $fmt:expr, $($args:tt),*) =>
    (crate::error::Error::from(&format!($fmt, $($args),*), $e));
}

// Internal type for the Result.
pub type Res<T> = Result<T, Error>;

macro_rules! res {
  ($e:expr) => ($e.unwrap());
  ($e:expr, $fmt:expr) => ($e.expect(&format!($fmt)));
  ($e:expr, $fmt:expr, $($args:expr),*) => ($e.expect(&format!($fmt, $($args),*)));
}
