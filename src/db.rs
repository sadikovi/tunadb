use crate::error::Res;

pub struct DatabaseClient {
}

impl DatabaseClient {
  pub fn new() -> Self {
    unimplemented!()
  }

  pub fn get(&self, key: &[u8]) -> Res<Vec<u8>> {
    unimplemented!()
  }

  pub fn put(&mut self, key: &[u8], value: &[u8]) -> Res<()> {
    unimplemented!()
  }

  pub fn range(&self, start_key: Option<&[u8]>, end_key: Option<&[u8]>) -> Res<()> {
    unimplemented!()
  }
}

// Each table is represented by B+Tree.
// Table catalog is a system table.
