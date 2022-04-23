use std::cell::RefCell;
use std::rc::Rc;
use crate::block::BlockManager;
use crate::cache::{DEFAULT_PAGE_CACHE_MEM, PageCache, PageCacheProxy};
use crate::error::Res;
use crate::storage::{DEFAULT_PAGE_SIZE, StorageManager};
use crate::txn::Transaction;

// Handler for the database state.
// TODO: implement file locking.
pub struct DB {
  mngr: Rc<RefCell<dyn BlockManager>>,
  txn_counter: usize,
  curr_txn: Option<Rc<RefCell<Transaction>>>,
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
        // We use proxy since the storage data is already in memory.
        Rc::new(RefCell::new(PageCacheProxy::new(storage)))
      }
    };

    Ok(DB {
      mngr: mngr,
      txn_counter: 0, // TODO: make it persistent
      curr_txn: None,
    })
  }
}

// Opens a database using the provided path or an in-memory database.
pub fn open(path: Option<&str>) -> DbBuilder {
  DbBuilder {
    path: path.map(|p| p.to_owned()),
    page_size: DEFAULT_PAGE_SIZE,
    max_mem: DEFAULT_PAGE_CACHE_MEM,
  }
}

impl DB {
  // Starts a new transaction and runs any operations within it.
  // When auto_commit is enabled, commits by the end of the function.
  pub fn with_txn<F, T>(&mut self, auto_commit: bool, func: F) -> T
      where F: Fn(Rc<RefCell<Transaction>>) -> T, {
    match &self.curr_txn {
      Some(txn) => {
        panic!("Transaction {} is active", txn.borrow().id());
      },
      None => {
        // No active transactions, proceed.
      }
    }

    let txn = Rc::new(RefCell::new(self.new_txn()));
    self.curr_txn = Some(txn.clone());
    let res = func(txn.clone());
    // Roll back all of the changes if they have not been explicitly committed.
    if txn.borrow().is_valid() {
      if auto_commit {
        txn.borrow_mut().commit();
      } else {
        txn.borrow_mut().rollback();
      }
    }
    self.curr_txn = None;

    res
  }

  // Creates a new transaction.
  fn new_txn(&mut self) -> Transaction {
    let id = self.txn_counter;
    self.txn_counter += 1;
    Transaction::new(id, self.mngr.clone())
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::storage::tests::with_tmp_file;
  use crate::txn::BTree;

  #[test]
  fn test_db_open_close() {
    with_tmp_file(|path| {
      let mut db = open(Some(path)).try_build().unwrap();
      db.with_txn(true, |txn| {
        let mut t1 = BTree::new("table1".to_owned(), txn.clone());
        t1.put(&[1], &[10]);
        t1.put(&[2], &[20]);
        t1.put(&[3], &[30]);
      });

      let mut db = open(Some(path)).try_build().unwrap();
      db.with_txn(false, |txn| {
        let t1 = BTree::find("table1", txn.clone()).unwrap();
        assert_eq!(t1.get(&[1]), Some(vec![10]));
        assert_eq!(t1.get(&[2]), Some(vec![20]));
        assert_eq!(t1.get(&[3]), Some(vec![30]));
      });
    });
  }
}
