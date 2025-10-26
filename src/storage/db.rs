use std::cell::RefCell;
use std::rc::Rc;
use crate::common::DB_VERSION;
use crate::common::error::Res;
use crate::storage::block::BlockManager;
use crate::storage::cache::{DEFAULT_PAGE_CACHE_MEM, NoPageCache, PageCache};
use crate::storage::smgr::{DEFAULT_PAGE_SIZE, StorageManager};
use crate::storage::txn::{TransactionRef, TransactionManager, TransactionManagerStats};

// Main entry to create a database client.
// Opens a database using the provided path or an in-memory database.
pub fn open(path: Option<&str>) -> DbBuilder {
  DbBuilder {
    path: path.map(|p| p.to_string()),
    page_size: DEFAULT_PAGE_SIZE,
    max_mem: DEFAULT_PAGE_CACHE_MEM,
  }
}

pub struct DbBuilder {
  path: Option<String>,
  page_size: u32,
  max_mem: usize,
}

impl DbBuilder {
  // Creates a database with the provided page size.
  // If the database has already been created, this configuration has no effect.
  pub fn with_page_size(mut self, page_size: u32) -> Self {
    self.page_size = page_size;
    self
  }

  // Configures the maximum memory for the page cache.
  pub fn with_max_mem(mut self, max_mem: usize) -> Self {
    self.max_mem = max_mem;
    self
  }

  // Creates a database handle.
  pub fn try_build(self) -> Res<DB> {
    let mngr: Rc<RefCell<dyn BlockManager>> = match self.path {
      Some(p) => {
        let storage = StorageManager::builder()
          .as_disk(&p)
          .with_page_size(self.page_size)
          .try_build()?;
        Rc::new(RefCell::new(PageCache::new(self.max_mem, storage)))
      },
      None => {
        // Open an in-memory database with 0 capacity.
        // TODO: Adjust the capacity or make it configurable.
        let storage = StorageManager::builder()
          .as_mem(0)
          .with_page_size(self.page_size)
          .try_build()?;
        // We use no-op page cache since the storage data is already in memory.
        Rc::new(RefCell::new(NoPageCache::new(storage)))
      }
    };

    Ok(DB { mngr: TransactionManager::new(mngr) })
  }
}

#[derive(Clone, Copy, Debug)]
pub struct DbStats {
  pub engine_version: u32,
  pub mngr_stats: TransactionManagerStats,
}

// Handler for the database state.
pub struct DB {
  mngr: TransactionManager,
}

impl DB {
  // Returns the database/engine version.
  #[inline]
  pub fn version(&self) -> u32 {
    DB_VERSION
  }

  // Database/storage statistics.
  pub fn stats(&self) -> DbStats {
    DbStats {
      engine_version: self.version(),
      mngr_stats: self.mngr.stats(),
    }
  }

  // Starts a new transaction and runs any operations within it.
  // When auto_commit is enabled, commits by the end of the function.
  pub fn with_txn<F, T>(&mut self, auto_commit: bool, func: F) -> T
      where F: Fn(TransactionRef) -> T, {
    self.mngr.with_txn(auto_commit, func).expect("Encountered error in transaction")
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::storage::smgr::tests::with_tmp_file;
  use crate::storage::txn::{create_set, get_set};

  #[test]
  fn test_db_stats() {
    let db = open(None).try_build().unwrap();
    let stats = db.stats();
    assert_eq!(stats.engine_version, db.version());
  }

  #[test]
  fn test_db_open_close() {
    with_tmp_file(|path| {
      // Once the scope is done, database should be persisted on disk and lock should be removed.
      {
        let mut db = open(Some(path)).try_build().unwrap();
        db.with_txn(true, |txn| {
          let mut t1 = create_set(&txn, b"t1").unwrap();
          t1.put(&[1], &[10]);
          t1.put(&[2], &[20]);
          t1.put(&[3], &[30]);
        });
      }

      // Scope 2: persisted data should be read correctly.
      {
        let mut db = open(Some(path)).try_build().unwrap();
        db.with_txn(false, |txn| {
          let t1 = get_set(&txn, b"t1").unwrap();
          assert_eq!(t1.get(&[1]), Some(vec![10]));
          assert_eq!(t1.get(&[2]), Some(vec![20]));
          assert_eq!(t1.get(&[3]), Some(vec![30]));
        });
      }
    });
  }

  #[test]
  fn test_db_auto_commit() {
    let mut db = open(None).try_build().unwrap();

    // Changes are persisted, auto-commit should be a no-op.
    db.with_txn(true, |txn| {
      let mut t1 = create_set(&txn, b"t1").unwrap();
      t1.put(&[1], &[10]);
      txn.borrow_mut().commit();
    });

    // Changes are rolled back.
    db.with_txn(false, |txn| {
      let mut t1 = get_set(&txn, b"t1").unwrap();
      t1.put(&[2], &[20]);
    });

    // Changes are committed.
    db.with_txn(true, |txn| {
      let mut t1 = get_set(&txn, b"t1").unwrap();
      t1.put(&[3], &[30]);
    });

    db.with_txn(false, |txn| {
      let t1 = get_set(&txn, b"t1").unwrap();
      assert_eq!(t1.get(&[1]), Some(vec![10]));
      assert_eq!(t1.get(&[2]), None);
      assert_eq!(t1.get(&[3]), Some(vec![30]));
    });
  }
}
