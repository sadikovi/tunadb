use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use crate::btree;
use crate::block::BlockManager;
use crate::cache::is_physical_page_id;
use crate::storage::INVALID_PAGE_ID;

// Transaction for working with BTree instances.
pub struct Transaction {
  id: usize,
  mngr: Rc<RefCell<dyn BlockManager>>, // shared mutability
  trees: HashMap<String, (u32, bool)>, // mapping of tree name to page id + is_dirty flag
  is_valid: bool,
}

impl Transaction {
  // Creates new transaction.
  pub fn new(id: usize, mngr: Rc<RefCell<dyn BlockManager>>) -> Self {
    Self { id, mngr, trees: HashMap::new(), is_valid: true }
  }

  // Returns transaction id.
  #[inline]
  pub fn id(&self) -> usize {
    self.id
  }

  // Returns true if the transaction is valid.
  #[inline]
  pub fn is_valid(&self) -> bool {
    self.is_valid
  }

  // Checks if the current transaction is valid and panics otherwise.
  #[inline]
  pub fn assert_valid(&self) {
    assert!(self.is_valid, "Transaction {} is not valid", self.id);
  }

  // Commits all of the tables updated in the transaction.
  pub fn commit(&mut self) {
    self.assert_valid();

    // 1. Commit all of the written pages.
    let vid_to_pid = self.mngr.borrow_mut().commit();

    // 2. Resolve root page id.
    let mut root = self.get_root_page();
    for (k, &(id, is_dirty)) in &self.trees {
      let pid = match id {
        vid if vid != INVALID_PAGE_ID && !is_physical_page_id(vid) =>
          *vid_to_pid.get(&vid)
            .expect(&format!("Table {} (vid {}, dirty {}) could not be resolved", k, vid, is_dirty)),
        pid => pid, // physical pages are never dirty
      };
      if is_dirty {
        root = btree::put(root, k.as_bytes(), &u32_u8!(pid), &mut *self.mngr.borrow_mut());
      }
    }

    // 3. Update the root tree + commit.
    let vid_to_pid = self.mngr.borrow_mut().commit();
    let root = match root {
      vid if vid != INVALID_PAGE_ID && !is_physical_page_id(vid) =>
        *vid_to_pid.get(&vid)
          .expect(&format!("Root page (vid {}) could not be resolved", root)),
      pid => pid,
    };

    // 4. Sync storage manager.
    self.set_root_page(root);
    self.mngr.borrow_mut().get_mngr_mut().sync();
    self.invalidate();
  }

  // Rolls back all of the written tables.
  pub fn rollback(&mut self) {
    self.assert_valid();
    self.mngr.borrow_mut().rollback();
    self.mngr.borrow_mut().get_mngr_mut().sync();
    self.invalidate();
  }

  // Registers table for the first time.
  // Only called once per table within the transaction.
  #[inline]
  fn register(&mut self, name: &str, root: u32, is_dirty: bool) {
    assert_eq!(
      self.trees.insert(name.to_owned(), (root, is_dirty)),
      None,
      "BTree '{}' already exists", name
    );
  }

  // Updates the root page for the table with the provided name.
  #[inline]
  fn update(&mut self, name: &str, root: u32, is_dirty: bool) {
    match self.trees.get_mut(name) {
      Some((pid, dirty)) => {
        *pid = root;
        *dirty = is_dirty;
      },
      None => {
        panic!("No such btree '{}' in the current transaction {}", name, self.id);
      },
    }
  }

  // Invalidates transaction and clears state.
  #[inline]
  fn invalidate(&mut self) {
    self.is_valid = false;
    self.trees.clear();
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
    if self.is_valid {
      self.rollback();
    }
  }
}

pub struct BTree {
  name: String,
  root: u32,
  txn: Rc<RefCell<Transaction>>,
}

impl BTree {
  // Creates a new btree with the provided name.
  // Panics if the tree already exists.
  pub fn new(name: String, txn: Rc<RefCell<Transaction>>) -> Self {
    txn.borrow().assert_valid();
    let root = INVALID_PAGE_ID; // empty table
    txn.borrow_mut().register(&name, root, true); // new table is always dirty
    Self { name, root, txn }
  }

  // Returns a btree for the provided name if it exists, None otherwise.
  pub fn find(name: &str, txn: Rc<RefCell<Transaction>>) -> Option<Self> {
    let root = txn.borrow().get_root_page();
    let opt = match btree::get(root, name.as_bytes(), &mut *txn.borrow_mut().mngr.borrow_mut()) {
      Some(buf) => {
        let pid = u8_u32!(&buf[..]);
        Some(Self { name: name.to_owned(), root: pid, txn: txn.clone() })
      },
      None => None,
    };

    if let Some(tree) = opt.as_ref() {
      txn.borrow_mut().register(&tree.name, tree.root, false); // existing tree is clean
    }

    opt
  }

  // Inserts/updates key-value pair.
  pub fn put(&mut self, key: &[u8], val: &[u8]) {
    self.txn.borrow().assert_valid();
    let mut txn = self.txn.borrow_mut();
    // Although we derive is_dirty check from root pid comparison, it will always be different
    // in practice due to the fact that we always update key-value pair.
    let curr_root = self.root;
    self.root = btree::put(curr_root, key, val, &mut *txn.mngr.borrow_mut());
    txn.update(&self.name, self.root, self.root != curr_root);
  }

  // Returns a value for the provided key.
  pub fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
    self.txn.borrow().assert_valid();
    let txn = self.txn.borrow_mut();
    let res = btree::get(self.root, key, &mut *txn.mngr.borrow_mut());
    // We don't need to update the root page or is_dirty flag here.
    res
  }

  // Deletes the key in the btree.
  pub fn del(&mut self, key: &[u8]) {
    self.txn.borrow().assert_valid();
    let mut txn = self.txn.borrow_mut();
    let curr_root = self.root;
    self.root = btree::del(curr_root, key, &mut *txn.mngr.borrow_mut());
    txn.update(&self.name, self.root, self.root != curr_root);
  }

  // Returns all of the key-value pairs in the btree.
  pub fn list(&mut self) -> btree::BTreeIter {
    self.txn.borrow().assert_valid();
    let txn = self.txn.borrow_mut();
    // We don't need to update the root page or is_dirty flag here.
    btree::BTreeIter::new(self.root, None, None, txn.mngr.clone())
  }

  // Returns btree debug information.
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

  #[test]
  #[should_panic(expected = "BTree 'abc' already exists")]
  fn test_txn_register_already_exists() {
    let cache = get_block_mngr();
    let txn = Rc::new(RefCell::new(Transaction::new(0, cache)));
    BTree::new("abc".to_owned(), txn.clone());
    BTree::new("abc".to_owned(), txn.clone());
  }

  #[test]
  fn test_txn_find_empty() {
    let cache = get_block_mngr();
    let txn = Rc::new(RefCell::new(Transaction::new(0, cache)));
    assert!(BTree::find("abc", txn.clone()).is_none());
  }

  #[test]
  #[should_panic(expected = "No such btree 'abc' in the current transaction 0")]
  fn test_txn_update_failure() {
    let cache = get_block_mngr();
    let mut txn = Transaction::new(0, cache);
    txn.update("abc", 100, true);
  }

  #[test]
  fn test_txn_register_update_ok() {
    let cache = get_block_mngr();
    let mut txn = Transaction::new(0, cache);

    let tname = "abc";

    txn.register(tname, INVALID_PAGE_ID, false);
    assert_eq!(txn.trees.get(tname), Some(&(INVALID_PAGE_ID, false)));

    txn.update(tname, 100, true);
    assert_eq!(txn.trees.get(tname), Some(&(100, true)));
  }

  #[test]
  fn test_txn_commit_empty() {
    let cache = get_block_mngr();
    let mut txn = Transaction::new(0, cache);
    txn.commit();
    assert_eq!(txn.get_root_page(), INVALID_PAGE_ID);
  }

  #[test]
  fn test_txn_commit() {
    let cache = get_block_mngr();
    let txn = Rc::new(RefCell::new(Transaction::new(0, cache.clone())));

    let mut t1 = BTree::new("table1".to_owned(), txn.clone());
    let mut t2 = BTree::new("table2".to_owned(), txn.clone());

    t1.put(&[1], &[10]);
    t1.put(&[2], &[20]);

    t2.put(&[8], &[80]);
    t2.put(&[9], &[90]);

    let v = t1.get(&[1]);
    assert_eq!(v, Some(vec![10]));

    let v = v.unwrap();
    t2.put(&v, &v);

    txn.borrow_mut().commit();

    assert_eq!(cache.borrow_mut().get_mngr().num_pages(), 3);
    assert_eq!(cache.borrow_mut().get_mngr().num_free_pages(), 0);
  }

  #[test]
  fn test_txn_commit_non_modified() {
    let cache = get_block_mngr();

    let txn1 = Rc::new(RefCell::new(Transaction::new(0, cache.clone())));
    let mut t = BTree::new("table".to_owned(), txn1.clone());
    t.put(&[1], &[10]);
    txn1.borrow_mut().commit();

    let txn2 = Rc::new(RefCell::new(Transaction::new(1, cache.clone())));
    let t = BTree::find("table", txn2.clone()).unwrap();
    assert_eq!(t.get(&[1]), Some(vec![10]));
    txn2.borrow_mut().commit();

    // 1 page is for table's btree, 1 page is for root btree.
    // No pages should be modified.
    assert_eq!(cache.borrow_mut().get_mngr().num_pages(), 2);
    assert_eq!(cache.borrow_mut().get_mngr().num_free_pages(), 0);
  }

  #[test]
  fn test_txn_commit_delete_of_non_existent_key() {
    // The test checks for regression when deleting a non-existent key would result in page
    // rewrite. Because we don't modify anything, there is no need to update root pid.
    let cache = get_block_mngr();

    let txn1 = Rc::new(RefCell::new(Transaction::new(0, cache.clone())));
    let mut t = BTree::new("table".to_owned(), txn1.clone());
    t.put(&[1], &[10]);
    txn1.borrow_mut().commit();

    let txn2 = Rc::new(RefCell::new(Transaction::new(1, cache.clone())));
    let mut t = BTree::find("table", txn2.clone()).unwrap();
    t.del(&[2]); // key does not exist in the table
    txn2.borrow_mut().commit();

    // 1 page is for table's btree, 1 page is for root btree.
    // No other pages should be modified.
    assert_eq!(cache.borrow_mut().get_mngr().num_pages(), 2);
    assert_eq!(cache.borrow_mut().get_mngr().num_free_pages(), 0);
  }

  #[test]
  fn test_txn_rollback_empty() {
    let cache = get_block_mngr();
    let mut txn = Transaction::new(0, cache);
    txn.rollback();
    assert_eq!(txn.get_root_page(), INVALID_PAGE_ID);
  }

  #[test]
  fn test_txn_rollback() {
    let cache = get_block_mngr();
    let txn = Rc::new(RefCell::new(Transaction::new(0, cache.clone())));

    let mut t1 = BTree::new("table1".to_owned(), txn.clone());

    t1.put(&[1], &[10]);
    t1.put(&[2], &[20]);

    txn.borrow_mut().rollback();

    assert_eq!(cache.borrow_mut().get_mngr().root_page(), None);
    assert_eq!(cache.borrow_mut().get_mngr().num_pages(), 0);
    assert_eq!(cache.borrow_mut().get_mngr().num_free_pages(), 0);
  }

  #[test]
  fn test_txn_btree_debug() {
    let cache = get_block_mngr();
    let txn = Rc::new(RefCell::new(Transaction::new(0, cache.clone())));

    let mut t1 = BTree::new("table1".to_owned(), txn.clone());
    assert_eq!(t1.btree_debug(), format!(" ! INVALID PAGE\n"));

    let mut t2 = BTree::new("table2".to_owned(), txn.clone());
    t2.put(&[1], &[2]);
    assert_eq!(t2.btree_debug(), format!(" * 2147483649 | cnt: 1 | min: [1] | max: [1]\n"));

    let mut t3 = BTree::new("table3".to_owned(), txn.clone());
    t3.put(&[1; 128], &[2; 128]);
    assert_eq!(t3.btree_debug(),
      format!(
        " * 2147483652 | cnt: 1 | min: [1, 1, 1, 1, 1, 1, 1, 1] trunc. len=128 | max: [1, 1, 1, 1, 1, 1, 1, 1] trunc. len=128\n"
      )
    );
  }
}
