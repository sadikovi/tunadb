use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use crate::btree;
use crate::block::BlockManager;
use crate::cache::is_virtual_page_id;
use crate::error::Res;
use crate::storage::INVALID_PAGE_ID;

// State enum for sets.
#[derive(Clone, Copy, Debug, PartialEq)]
enum State {
  Clean,
  Modified,
  Deleted,
}

// Merges state to return the modified one if available.
// Used to determine if we need to commit changes.
#[inline]
fn merge_state(state1: State, state2: State) -> State {
  match (state1, state2) {
    (State::Clean, _) => state2,
    (_, State::Clean) => state1,
    (State::Deleted, _) => state1,
    (_, State::Deleted) => state2,
    _ => state1, // both states are Modified
  }
}

// Returns true if we consider the state to be data changing.
#[inline]
fn is_state_modified(state: State) -> bool {
  state == State::Modified || state == State::Deleted
}

// Transaction for working with sets.
pub struct Transaction {
  id: usize,
  mngr: Rc<RefCell<dyn BlockManager>>, // shared mutability
  active_sets: HashMap<String, (u32, State)>, // mapping of the set name to page id + state
  is_finalised: bool, // whether or not transaction has been committed or rolled back
  is_modified: bool, // whether or not we require commit/rollback
}

impl Transaction {
  // Creates new transaction.
  // Although it is public, it is considered an internal method and should not be used to create
  // a transaction.
  pub fn new(id: usize, mngr: Rc<RefCell<dyn BlockManager>>) -> Self {
    Self { id, mngr, active_sets: HashMap::new(), is_finalised: false, is_modified: false }
  }

  // Returns transaction id.
  #[inline]
  pub fn id(&self) -> usize {
    self.id
  }

  // Returns true if the transaction has been finalised.
  // In other words, if we can/cannot perform any operations on the transaction anymore.
  #[inline]
  pub fn is_finalised(&self) -> bool {
    self.is_finalised
  }

  // Returns true if the transaction has made modifications, i.e. read-only or not.
  #[inline]
  pub fn is_modified(&self) -> bool {
    self.is_modified
  }

  // Commits all of the tables updated in the transaction.
  // If nothing was changed in the transaction, we skip commit and sync.
  pub fn commit(&mut self) {
    self.assert_not_finalised();

    // If the transaction is read-only, no checks are required.
    if self.is_modified {
      // 1. Commit all of the written pages.
      let vid_to_pid = self.mngr.borrow_mut().commit();

      // 2. Resolve root page id.
      let mut root = self.get_root_page();
      for (name, &(id, state)) in &self.active_sets {
        match state {
          State::Clean => {
            // Do nothing, the page was not modified.
          },
          State::Modified => {
            let pid = if is_virtual_page_id(id) {
              // The page is a virtual page.
              *vid_to_pid.get(&id)
                .expect(
                  &format!("Set {} (root {}) could not be resolved", name, id)
                )
            } else {
              id // physical page, no need to resolve it
            };
            root = btree::put(root, name.as_bytes(), &u32_u8!(pid), &mut *self.mngr.borrow_mut());
          },
          State::Deleted => {
            assert_eq!(id, INVALID_PAGE_ID, "Set {} (root {}) data was not deleted", name, id);
            // The set must have been deleted or was never created on disk.
            root = btree::del(root, name.as_bytes(), &mut *self.mngr.borrow_mut());
          },
        }
      }

      // 3. Update the root tree + commit.
      let vid_to_pid = self.mngr.borrow_mut().commit();
      let root = match root {
        vid if is_virtual_page_id(vid) =>
          *vid_to_pid.get(&vid)
            .expect(&format!("Root page (vid {}) could not be resolved", root)),
        pid => pid,
      };

      // 4. Sync storage manager.
      self.set_root_page(root);
      self.mngr.borrow_mut().get_mngr_mut().sync();
    }
    self.finalise();
  }

  // Rolls back all of the written tables.
  // If nothing was changed in the transaction, we skip rollback and sync.
  pub fn rollback(&mut self) {
    self.assert_not_finalised();
    if self.is_modified {
      self.mngr.borrow_mut().rollback();
      self.mngr.borrow_mut().get_mngr_mut().sync();
    }
    self.finalise();
  }

  // Panics if the current transaction has been finalised.
  // If the transaction is still active, then it is no-op.
  #[inline]
  fn assert_not_finalised(&self) {
    assert!(!self.is_finalised, "Transaction {} has been finalised", self.id);
  }

  // Updates the root page for the table with the provided name.
  #[inline]
  fn update(&mut self, name: &str, root: u32, new_state: State) {
    match self.active_sets.get_mut(name) {
      Some((pid, state)) => {
        *pid = root;
        *state = merge_state(*state, new_state);
      },
      None => {
        self.active_sets.insert(name.to_owned(), (root, new_state));
      },
    }
    self.is_modified |= is_state_modified(new_state);
  }

  // Invalidates transaction and clears state.
  // This is used in commit and rollback functions.
  #[inline]
  fn finalise(&mut self) {
    self.is_finalised = true;
    self.is_modified = false;
    self.active_sets.clear();
  }

  // Returns the root page id or INVALID_PAGE_ID if none are set.
  #[inline]
  fn get_root_page(&self) -> u32 {
    self.mngr.borrow().get_mngr().root_page().unwrap_or(INVALID_PAGE_ID)
  }

  // Sets root page in the storage manager.
  #[inline]
  fn set_root_page(&mut self, pid: u32) {
    let root = if pid == INVALID_PAGE_ID { None } else { Some(pid) };
    self.mngr.borrow_mut().get_mngr_mut().update_root_page(root);
  }
}

impl Drop for Transaction {
  fn drop(&mut self) {
    // Check the flag to avoid panic in rollback.
    if !self.is_finalised {
      self.rollback();
    }
  }
}

// Creates a new set with the provided name.
// If a set with the name already exists, an error is returned.
pub fn create_set(txn: Rc<RefCell<Transaction>>, name: &str) -> Res<Set> {
  txn.borrow().assert_not_finalised();

  // Check if there is such name in active sets.
  if let Some(_) = txn.borrow().active_sets.get(name) {
    return Err(already_exists_err!("Set {} already exists", name));
  }

  // Check if we already have such a set in the btree.
  let root = txn.borrow().get_root_page();
  if let Some(_) = btree::get(root, name.as_bytes(), &mut *txn.borrow_mut().mngr.borrow_mut()) {
    return Err(already_exists_err!("Set {} already exists", name));
  }

  // The new set has an empty page and is not modified.
  // This allows us to ignore writes when no put or del operations have been done.
  txn.borrow_mut().update(name, INVALID_PAGE_ID, State::Clean);

  Ok(Set { name: name.to_owned(), root: INVALID_PAGE_ID, txn: txn.clone() })
}

// Returns a set for the provided name if it exists.
pub fn get_set(txn: Rc<RefCell<Transaction>>, name: &str) -> Option<Set> {
  txn.borrow().assert_not_finalised();

  if let Some(&(root, _)) = txn.borrow().active_sets.get(name) {
    return Some(Set { name: name.to_owned(), root: root, txn: txn.clone() })
  }

  let root = txn.borrow().get_root_page();
  match btree::get(root, name.as_bytes(), &mut *txn.borrow_mut().mngr.borrow_mut()) {
    Some(buf) => {
      let pid = u8_u32!(&buf[..]);
      Some(Set { name: name.to_owned(), root: pid, txn: txn.clone() })
    },
    None => None,
  }
}

// Drops set so it is no longer accessible, all of the data is also deleted.
// No-op if no such set exists.
pub fn drop_set(txn: Rc<RefCell<Transaction>>, mut set: Set) {
  set.truncate();
  txn.borrow_mut().update(&set.name, set.root, State::Deleted);
}

// A high-level wrapper on btree module.
// Has a unique name and the root page and is associated with a transaction.
pub struct Set {
  name: String,
  root: u32,
  txn: Rc<RefCell<Transaction>>,
}

impl Set {
  // Returns value for the key if exists.
  pub fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
    self.txn.borrow().assert_not_finalised();
    let txn = self.txn.borrow_mut();
    let res = btree::get(self.root, key, &mut *txn.mngr.borrow_mut());
    // The operation is read-only, no need to update the entry.
    res
  }

  // Returns the list of keys and values.
  // `start` and `end` define the range.
  pub fn list(&mut self, start: Option<&[u8]>, end: Option<&[u8]>) -> btree::BTreeIter {
    self.txn.borrow().assert_not_finalised();
    let txn = self.txn.borrow_mut();
    // The operation is read-only, no need to update the entry.
    btree::BTreeIter::new(self.root, start, end, txn.mngr.clone())
  }

  // Inserts key and value into the set.
  pub fn put(&mut self, key: &[u8], value: &[u8]) {
    self.txn.borrow().assert_not_finalised();

    let mut txn = self.txn.borrow_mut();
    let curr_root = self.root;
    self.root = btree::put(curr_root, key, value, &mut *txn.mngr.borrow_mut());

    let new_state = if self.root != curr_root { State::Modified } else { State::Clean };
    txn.update(&self.name, self.root, new_state);
  }

  // Deletes key if exists.
  pub fn del(&mut self, key: &[u8]) {
    self.txn.borrow().assert_not_finalised();

    let mut txn = self.txn.borrow_mut();
    let curr_root = self.root;
    self.root = btree::del(curr_root, key, &mut *txn.mngr.borrow_mut());

    let new_state = if self.root != curr_root { State::Modified } else { State::Clean };
    txn.update(&self.name, self.root, new_state);
  }

  // Deletes all of the data in the set.
  pub fn truncate(&mut self) {
    self.txn.borrow().assert_not_finalised();

    let mut txn = self.txn.borrow_mut();
    let curr_root = self.root;
    self.root = btree::drop(curr_root, &mut *txn.mngr.borrow_mut());

    assert_eq!(self.root, INVALID_PAGE_ID, "Root must be INVALID_PAGE_ID after truncate");

    let new_state = if self.root != curr_root { State::Modified } else { State::Clean };
    txn.update(&self.name, self.root, new_state);
  }

  // Returns btree debug information.
  // Mostly used for testing.
  pub fn btree_debug(&mut self) -> String {
    let mut buf = String::new();
    let txn = self.txn.borrow_mut();
    btree::btree_debug(&mut buf, self.root, &mut *txn.mngr.borrow_mut());
    buf
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::cache::PageCache;
  use crate::storage::StorageManager;

  fn get_block_mngr() -> Rc<RefCell<dyn BlockManager>> {
    let mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();
    Rc::new(RefCell::new(PageCache::new(1 * 1024 * 1024, mngr)))
  }

  // A wrapper for transactions in tests.
  fn with_txn<F>(id: usize, cache: Rc<RefCell<dyn BlockManager>>, func: F)
      where F: Fn(Rc<RefCell<Transaction>>) -> () {
    let txn = Rc::new(RefCell::new(Transaction::new(id, cache)));
    func(txn);
  }

  // Helper function to check total pages and free pages.
  fn assert_block_mngr(
    cache: Rc<RefCell<dyn BlockManager>>,
    num_pages: usize,
    num_free_pages: usize
  ) {
    assert_eq!(cache.borrow_mut().get_mngr().num_pages(), num_pages, "num_pages");
    assert_eq!(cache.borrow_mut().get_mngr().num_free_pages(), num_free_pages, "num_free_pages");
  }

  #[test]
  fn test_txn_create_set_already_exists() {
    let cache = get_block_mngr();

    with_txn(1, cache, |txn| {
      assert!(create_set(txn.clone(), "abc").is_ok());
      // Should return an error.
      assert!(!create_set(txn.clone(), "abc").is_ok());
    });
  }

  #[test]
  fn test_txn_create_set_already_exists_persistent() {
    let cache = get_block_mngr();

    with_txn(1, cache.clone(), |txn| {
      let mut set = create_set(txn.clone(), "abc").unwrap();
      set.put(&[1], &[2]);
      txn.borrow_mut().commit();
    });

    with_txn(2, cache.clone(), |txn| {
      assert!(!create_set(txn.clone(), "abc").is_ok());
    });
  }

  #[test]
  fn test_txn_get_set_empty() {
    let cache = get_block_mngr();

    // Set does not exist.
    with_txn(1, cache.clone(), |txn| {
      assert!(get_set(txn.clone(), "abc").is_none());
    });

    // Set has been created but not committed yet.
    with_txn(2, cache.clone(), |txn| {
      create_set(txn.clone(), "abc").unwrap();
      assert!(get_set(txn.clone(), "abc").is_some());
    });

    // Set has been created and committed.
    with_txn(3, cache.clone(), |txn| {
      let mut set = create_set(txn.clone(), "abc").unwrap();
      set.put(&[1], &[2]);
      txn.borrow_mut().commit();
    });

    with_txn(4, cache, |txn| {
      assert!(get_set(txn.clone(), "abc").is_some());
    });
  }

  #[test]
  fn test_txn_commit_empty() {
    let cache = get_block_mngr();
    with_txn(1, cache, |txn| {
      txn.borrow_mut().commit();
      assert_eq!(txn.borrow().get_root_page(), INVALID_PAGE_ID);
    });
  }

  #[test]
  fn test_txn_commit() {
    let cache = get_block_mngr();

    with_txn(1, cache.clone(), |txn| {
      let mut t1 = create_set(txn.clone(), "t1").unwrap();
      let mut t2 = create_set(txn.clone(), "t2").unwrap();

      t1.put(&[1], &[10]);
      t1.put(&[2], &[20]);

      t2.put(&[8], &[80]);
      t2.put(&[9], &[90]);

      let v = t1.get(&[1]);
      assert_eq!(v, Some(vec![10]));

      let v = v.unwrap();
      t2.put(&v, &v);

      assert!(txn.borrow().is_modified());
      txn.borrow_mut().commit();
    });

    // 3 = 1 page for t1, 1 page for t2, 1 page for root.
    assert_block_mngr(cache, 3, 0);
  }

  #[test]
  fn test_txn_commit_ops_order() {
    let cache = get_block_mngr();

    with_txn(1, cache.clone(), |txn| {
      let mut t1 = create_set(txn.clone(), "t1").unwrap();

      t1.put(&[1], &[10]);
      assert_eq!(t1.get(&[1]), Some(vec![10])); // should not overwrite Modified state

      assert!(txn.borrow().is_modified());
      txn.borrow_mut().commit();
    });

    // 2 = 1 page for t1, 1 page for root.
    assert_block_mngr(cache, 2, 0);
  }


  #[test]
  fn test_txn_commit_put_and_get() {
    // Test verifies that get operations on the existing table don't result in modified pages.
    let cache = get_block_mngr();

    with_txn(1, cache.clone(), |txn| {
      let mut t = create_set(txn.clone(), "t").unwrap();
      t.put(&[1], &[10]);

      assert!(txn.borrow().is_modified());
      txn.borrow_mut().commit();
    });

    with_txn(2, cache.clone(), |txn| {
      let t = get_set(txn.clone(), "t").unwrap();
      assert_eq!(t.get(&[1]), Some(vec![10]));

      assert!(!txn.borrow().is_modified());
      txn.borrow_mut().commit();
    });

    // 2 = 1 page for t, 1 page for root.
    assert_block_mngr(cache, 2, 0);
  }

  #[test]
  fn test_txn_commit_multiple_puts() {
    // The test verifies two commits and how the page ids change.
    let cache = get_block_mngr();

    with_txn(1, cache.clone(), |txn| {
      let mut t = create_set(txn.clone(), "table").unwrap();
      t.put(&[1], &[10]);

      assert!(txn.borrow().is_modified());
      txn.borrow_mut().commit();
    });

    // 2 = 1 page for table, 1 page for root.
    assert_block_mngr(cache.clone(), 2, 0);

    with_txn(2, cache.clone(), |txn| {
      let mut t = get_set(txn.clone(), "table").unwrap();
      t.put(&[2], &[20]);

      assert!(txn.borrow().is_modified());
      txn.borrow_mut().commit();
    });

    // 2 previous pages are empty, so we acquire the other two.
    assert_block_mngr(cache.clone(), 4, 2);

    with_txn(3, cache.clone(), |txn| {
      let mut t = get_set(txn.clone(), "table").unwrap();
      t.put(&[3], &[30]);

      assert!(txn.borrow().is_modified());
      txn.borrow_mut().commit();
    });

    // We overwrite the original two pages, the free pages are truncated.
    assert_block_mngr(cache, 2, 0);
  }

  #[test]
  fn test_txn_commit_put_and_del() {
    // Test verifies that get operations on the existing table don't result in modified pages.
    let cache = get_block_mngr();

    with_txn(1, cache.clone(), |txn| {
      let mut t = create_set(txn.clone(), "t").unwrap();
      t.put(&[1], &[10]);

      assert!(txn.borrow().is_modified());
      txn.borrow_mut().commit();
    });

    // 2 = 1 page for data + 1 page for root.
    assert_block_mngr(cache.clone(), 2, 0);

    with_txn(2, cache.clone(), |txn| {
      let mut t = get_set(txn.clone(), "t").unwrap();
      t.del(&[1]);

      println!("{}", t.btree_debug());

      assert!(txn.borrow().is_modified());
      txn.borrow_mut().commit();
    });

    // 3 = 2 free pages + 1 page for root.
    assert_block_mngr(cache, 3, 2);
  }

  #[test]
  fn test_txn_commit_delete_of_non_existent_key() {
    // The test checks for regression when deleting a non-existent key would result in page
    // rewrite. Because we don't modify anything, there is no need to update root pid.
    let cache = get_block_mngr();

    with_txn(1, cache.clone(), |txn| {
      let mut t = create_set(txn.clone(), "table").unwrap();
      t.put(&[1], &[10]);

      assert!(txn.borrow().is_modified());
      txn.borrow_mut().commit();
    });

    with_txn(2, cache.clone(), |txn| {
      let mut t = get_set(txn.clone(), "table").unwrap();
      t.del(&[2]); // key does not exist in the table

      assert!(!txn.borrow().is_modified());
      txn.borrow_mut().commit();
    });

    // 1 page is for table's btree, 1 page is for root btree.
    // No other pages should be modified.
    assert_block_mngr(cache, 2, 0);
  }

  #[test]
  fn test_txn_commit_list_on_new_table() {
    // We should not create a new table when it is just a list operation.
    let cache = get_block_mngr();

    with_txn(1, cache.clone(), |txn| {
      let mut t = create_set(txn.clone(), "table").unwrap();
      assert_eq!(t.list(None, None).next(), None);

      assert!(!txn.borrow().is_modified()); // new trees should not be persisted
      txn.borrow_mut().commit();
    });

    assert_eq!(cache.borrow_mut().get_mngr().root_page(), None);
    assert_eq!(cache.borrow_mut().get_mngr().num_pages(), 0);
    assert_eq!(cache.borrow_mut().get_mngr().num_free_pages(), 0);
  }

  #[test]
  fn test_txn_commit_get_on_new_table() {
    // We should not create a new table when it is just a get operation.
    let cache = get_block_mngr();

    with_txn(1, cache.clone(), |txn| {
      let t = create_set(txn.clone(), "table").unwrap();
      assert_eq!(t.get(&[1]), None);

      assert!(!txn.borrow().is_modified()); // new trees should not be persisted
      txn.borrow_mut().commit();
    });

    assert_eq!(cache.borrow_mut().get_mngr().root_page(), None);
    assert_eq!(cache.borrow_mut().get_mngr().num_pages(), 0);
    assert_eq!(cache.borrow_mut().get_mngr().num_free_pages(), 0);
  }

  #[test]
  fn test_txn_truncate_commit() {
    let cache = get_block_mngr();

    with_txn(1, cache.clone(), |txn| {
      let mut t = create_set(txn.clone(), "table").unwrap();
      t.put(&[1], &[10]);
      t.put(&[2], &[20]);
      t.put(&[3], &[30]);
      txn.borrow_mut().commit();
    });

    // 2 = 1 page for data + 1 page for root.
    assert_block_mngr(cache.clone(), 2, 0);

    with_txn(2, cache.clone(), |txn| {
      let mut t = get_set(txn.clone(), "table").unwrap();
      t.truncate();
      txn.borrow_mut().commit();
    });

    // 3 = 2 free pages + 1 page for root.
    assert_block_mngr(cache, 3, 2);
  }

  #[test]
  fn test_txn_truncate_rollback() {
    let cache = get_block_mngr();

    with_txn(1, cache.clone(), |txn| {
      let mut t = create_set(txn.clone(), "table").unwrap();
      t.put(&[1], &[10]);
      t.put(&[2], &[20]);
      t.put(&[3], &[30]);
      txn.borrow_mut().commit();
    });

    // 2 = 1 page for data + 1 page for root.
    assert_block_mngr(cache.clone(), 2, 0);

    with_txn(2, cache.clone(), |txn| {
      let mut t = get_set(txn.clone(), "table").unwrap();
      t.truncate();
      txn.borrow_mut().rollback();
    });

    // 2 = 1 page for data + 1 page for root.
    assert_block_mngr(cache.clone(), 2, 0);

    with_txn(3, cache.clone(), |txn| {
      let t = get_set(txn.clone(), "table").unwrap();
      assert_eq!(t.get(&[1]), Some(vec![10]));
      assert_eq!(t.get(&[2]), Some(vec![20]));
      assert_eq!(t.get(&[3]), Some(vec![30]));
    });
  }

  #[test]
  fn test_txn_drop_commit() {
    let cache = get_block_mngr();

    with_txn(1, cache.clone(), |txn| {
      let t = create_set(txn.clone(), "table").unwrap();
      drop_set(txn.clone(), t);
      txn.borrow_mut().commit();
    });

    assert_block_mngr(cache.clone(), 0, 0);

    // Try to insert data into the table and then drop.
    with_txn(2, cache.clone(), |txn| {
      let mut t = create_set(txn.clone(), "table").unwrap();
      t.put(&[1], &[10]);
      txn.borrow_mut().commit();
    });

    assert_block_mngr(cache.clone(), 2, 0);

    // Drop should delete all of the pages.
    with_txn(3, cache.clone(), |txn| {
      let t = get_set(txn.clone(), "table").unwrap();
      drop_set(txn.clone(), t);
      txn.borrow_mut().commit();
    });

    assert_block_mngr(cache.clone(), 0, 0);
  }

  #[test]
  fn test_txn_drop_rollback() {
    let cache = get_block_mngr();

    with_txn(1, cache.clone(), |txn| {
      let mut t = create_set(txn.clone(), "table").unwrap();
      t.put(&[1], &[10]);
      txn.borrow_mut().commit();
    });

    assert_block_mngr(cache.clone(), 2, 0);

    with_txn(2, cache.clone(), |txn| {
      let t = get_set(txn.clone(), "table").unwrap();
      drop_set(txn.clone(), t);
      txn.borrow_mut().rollback();
    });

    assert_block_mngr(cache.clone(), 2, 0);
  }

  #[test]
  fn test_txn_rollback_empty() {
    let cache = get_block_mngr();

    with_txn(1, cache, |txn| {
      assert!(!txn.borrow().is_modified());
      txn.borrow_mut().rollback();
      assert_eq!(txn.borrow().get_root_page(), INVALID_PAGE_ID);
    });
  }

  #[test]
  fn test_txn_rollback_read_only_new_table() {
    let cache = get_block_mngr();

    with_txn(1, cache.clone(), |txn| {
      let t = create_set(txn.clone(), "table").unwrap();
      assert_eq!(t.get(&[1]), None);

      assert!(!txn.borrow().is_modified());
      txn.borrow_mut().rollback(); // rollback should be a no-op
    });

    assert_eq!(cache.borrow_mut().get_mngr().root_page(), None);
    assert_eq!(cache.borrow_mut().get_mngr().num_pages(), 0);
    assert_eq!(cache.borrow_mut().get_mngr().num_free_pages(), 0);
  }

  #[test]
  fn test_txn_rollback_read_only_existing_table() {
    let cache = get_block_mngr();

    // Test read-only mode for an existing table.
    with_txn(1, cache.clone(), |txn| {
      let mut t = create_set(txn.clone(), "table").unwrap();
      t.put(&[1], &[2]);
      txn.borrow_mut().commit();
    });

    with_txn(2, cache.clone(), |txn| {
      let t = get_set(txn.clone(), "table").unwrap();
      assert_eq!(t.get(&[2]), None);

      assert!(!txn.borrow().is_modified());
      txn.borrow_mut().rollback();
    });

    assert_eq!(cache.borrow_mut().get_mngr().root_page(), Some(1)); // table was stored
    assert_eq!(cache.borrow_mut().get_mngr().num_pages(), 2); // table data + root page
    assert_eq!(cache.borrow_mut().get_mngr().num_free_pages(), 0);
  }

  #[test]
  fn test_txn_rollback_modified() {
    let cache = get_block_mngr();

    // Writes only.
    with_txn(1, cache.clone(), |txn| {
      let mut t1 = create_set(txn.clone(), "t1").unwrap();
      t1.put(&[1], &[10]);
      t1.put(&[2], &[20]);

      assert!(txn.borrow().is_modified());
      txn.borrow_mut().rollback();
    });

    assert_eq!(cache.borrow_mut().get_mngr().root_page(), None);
    assert_eq!(cache.borrow_mut().get_mngr().num_pages(), 0);
    assert_eq!(cache.borrow_mut().get_mngr().num_free_pages(), 0);

    // Reads + writes.
    with_txn(2, cache.clone(), |txn| {
      let mut t1 = create_set(txn.clone(), "t1").unwrap();
      t1.put(&[1], &[10]);
      assert_eq!(t1.get(&[1]), Some(vec![10]));

      assert!(txn.borrow().is_modified());
      txn.borrow_mut().rollback();
    });

    assert_eq!(cache.borrow_mut().get_mngr().root_page(), None);
    assert_eq!(cache.borrow_mut().get_mngr().num_pages(), 0);
    assert_eq!(cache.borrow_mut().get_mngr().num_free_pages(), 0);
  }

  #[test]
  fn test_txn_btree_debug() {
    let cache = get_block_mngr();

    with_txn(1, cache, |txn| {
      let mut t1 = create_set(txn.clone(), "t1").unwrap();
      assert_eq!(t1.btree_debug(), format!(" ! INVALID PAGE\n"));

      let mut t2 = create_set(txn.clone(), "t2").unwrap();
      t2.put(&[1], &[2]);
      assert_eq!(t2.btree_debug(), format!(" * 2147483649 | cnt: 1 | min: [1] | max: [1]\n"));

      let mut t3 = create_set(txn.clone(), "t3").unwrap();
      t3.put(&[1; 128], &[2; 128]);
      assert_eq!(
        t3.btree_debug(),
        format!(
          " * 2147483652 | cnt: 1 | min: [1, 1, 1, 1, 1, 1, 1, 1] trunc. len=128 | max: [1, 1, 1, 1, 1, 1, 1, 1] trunc. len=128\n"
        )
      );
    });
  }
}
