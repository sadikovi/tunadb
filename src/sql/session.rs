//! User session.

const DEFAULT_SCHEMA: &str = "default";

pub struct SessionBuilder {
  current_schema: String,
}

impl SessionBuilder {
  pub fn with_schema(mut self, schema: &str) -> Self {
    self.current_schema = schema.to_string();
    self
  }

  pub fn build(self) -> Session {
    Session { current_schema: self.current_schema }
  }
}

#[derive(Debug)]
pub struct Session {
  current_schema: String,
}

impl Session {
  pub fn builder() -> SessionBuilder {
    SessionBuilder { current_schema: DEFAULT_SCHEMA.to_string() }
  }

  // Returns current schema set by the user.
  #[inline]
  pub fn current_schema(&self) -> &str {
    &self.current_schema
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_session_default_schema() {
    let session = Session::builder().build();
    assert_eq!(session.current_schema(), DEFAULT_SCHEMA);
  }

  #[test]
  fn test_session_custom_schema() {
    let session = Session::builder().with_schema("myschema").build();
    assert_eq!(session.current_schema(), "myschema");
  }
}
