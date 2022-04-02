use crate::storage::StorageManager;

// Handler for the database state.
pub struct DB {
  mngr: StorageManager,
}

// Opens a database using the provided path or an in-memory database.
pub fn open(path: Option<&str>) -> DB {
  match path {
    Some(p) => {
      DB { mngr: StorageManager::builder().as_disk(p).build() }
    },
    None => {
      // Open an in-memory database with 0 capacity.
      // TODO: Adjust the capacity or make it configurable.
      DB { mngr: StorageManager::builder().as_mem(0).build() }
    }
  }
}

// information_schema
// default
