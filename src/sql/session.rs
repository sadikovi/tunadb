//! User session.

#[derive(Debug)]
pub struct Session {
  current_schema: String,
}

impl Session {
  pub fn new() -> Self {
    Self {
      // TODO: figure out how to set the default schema.
      current_schema: "default".to_string(),
    }
  }

  // Returns current schema set by the user.
  #[inline]
  pub fn current_schema(&self) -> &str {
    &self.current_schema
  }
}
