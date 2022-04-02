use std::cell::RefCell;
use std::rc::Rc;
use crate::btree;
use crate::storage::{INVALID_PAGE_ID, PageManager};

const FLAG_LEAF_TREE: u32 = 0;
const FLAG_META_TREE: u32 = 1;

// High-level wrapper on btree module allowing us to represent a tree-like structure
// of all of the objects in the database.

pub struct Tree {
  root: u32, // root pid
  mngr: Rc<RefCell<dyn PageManager>>, // shared mutability
  is_meta: bool, // whether or not it is META tree
  is_dirty: bool, // whether or not the tree has been modified
}

impl Tree {
  // Creates a new tree.
  pub fn new(root: u32, is_meta: bool, mngr: Rc<RefCell<dyn PageManager>>) -> Self {
    Self { root, mngr, is_meta, is_dirty: false }
  }

  // Creates an empty tree with root as INVALID_PAGE_ID.
  pub fn empty(is_meta: bool, mngr: Rc<RefCell<dyn PageManager>>) -> Self {
    Self::new(INVALID_PAGE_ID, is_meta, mngr)
  }

  // Returns true if the tree is empty, i.e. no keys.
  pub fn is_empty(&self) -> bool {
    self.root == INVALID_PAGE_ID
  }

  // Returns true if this tree is a meta tree.
  pub fn is_meta(&self) -> bool {
    self.is_meta
  }

  // Frees the current Tree and marks all of the underlying pages as free.
  // Effectively drops the tree and its children.
  pub fn free(&mut self) {
    if self.is_meta {
      // We need to drop child trees first.
      // TODO: optimise this case, we don't need the key-value pairs, instead we could delete
      // trees as we are traversing pages.
      let mut children = Vec::new();
      {
        let mngr_ref = &mut *self.mngr.borrow_mut();
        let mut iter = btree::BTreeIter::new(self.root, None, None, mngr_ref);
        while let Some((_, val)) = iter.next() {
          children.push(decode(&val));
        }
      }

      for &(root, is_meta) in &children {
        let mut tree = Self::new(root, is_meta, self.mngr.clone());
        tree.free();
      }
    }
    // Drops all of the overflow, leaf, and internal pages.
    self.root = btree::drop(self.root, &mut *self.mngr.borrow_mut());
    self.is_dirty = true;
  }

  // Returns stored data for the provided key or None if no such key exists.
  // Only used for Leaf nodes.
  pub fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
    assert!(!self.is_meta, "Leaf tree is expected");
    btree::get(self.root, key, &mut *self.mngr.borrow_mut())
  }

  // Inserts a key-value pair into the leaf tree.
  pub fn put(&mut self, key: &[u8], val: &[u8]) {
    assert!(!self.is_meta, "Leaf tree is expected");
    self.root = btree::put(self.root, key, val, &mut *self.mngr.borrow_mut());
    self.is_dirty = true;
  }

  // Deletes the key-value pair in the meta or leaf tree.
  pub fn del(&mut self, key: &[u8]) {
    assert!(!self.is_meta, "Leaf tree is expected");
    self.root = btree::del(self.root, key, &mut *self.mngr.borrow_mut());
    self.is_dirty = true;
  }

  // Returns a copy of Tree for the key.
  // Note that if Tree object is modified, it needs to be updated with `meta_put()`.
  pub fn meta_get(&self, key: &[u8]) -> Option<Self> {
    assert!(self.is_meta, "Meta tree is expected");
    match btree::get(self.root, key, &mut *self.mngr.borrow_mut()) {
      Some(buf) => {
        let (pid, is_meta) = decode(&buf[..]);
        Some(Self::new(pid, is_meta, self.mngr.clone()))
      },
      None => None,
    }
  }

  // Inserts (or updates if the key exists) key -> Tree object pair.
  pub fn meta_put(&mut self, key: &[u8], mut val: Tree) {
    assert!(self.is_meta, "Meta tree is expected");
    let buf = encode(val.root, val.is_meta);
    self.root = btree::put(self.root, key, &buf[..], &mut *self.mngr.borrow_mut());
    self.is_dirty = true;
    // Mark the tree as non dirty so it can be freed correctly.
    val.is_dirty = false;
  }

  // Delets the reference to the Tree object for the key if exists.
  // Note that this does not delete pages for the Tree object, the tree needs to be freed
  // separately.
  pub fn meta_del(&mut self, key: &[u8]) {
    assert!(self.is_meta, "Meta tree is expected");
    self.root = btree::del(self.root, key, &mut *self.mngr.borrow_mut());
    self.is_dirty = true;
  }
}

// Serialises tree components into a byte buffer.
#[inline]
fn encode(root: u32, is_meta: bool) -> [u8; 8] {
  let tpe = if is_meta { FLAG_META_TREE } else { FLAG_LEAF_TREE };
  let payload = (tpe as u64) << 32 | root as u64;
  u64_u8!(payload)
}

// Deserialises byte buffer into a tree.
// Returns root page id and is_meta flag.
#[inline]
fn decode(buf: &[u8]) -> (u32, bool) {
  let payload = u8_u64!(&buf[..]);
  let tpe = (payload >> 32) as u32;
  let pid = (payload & 0xffffffff) as u32;
  (pid, tpe == FLAG_META_TREE)
}

impl Drop for Tree {
  fn drop(&mut self) {
    // TODO: Log a warning if Tree goes out of scope with is_dirty = true.
    if self.is_dirty {
      println!("WARN {} tree is dropped as dirty", if self.is_meta { "Meta" } else { "Leaf" });
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::storage::StorageManager;

  fn get_mngr() -> Rc<RefCell<dyn PageManager>> {
    let mngr = StorageManager::builder().as_mem(0).with_page_size(512).build();
    Rc::new(RefCell::new(mngr))
  }

  #[test]
  fn test_tree_leaf_put_get_del() {
    let mut prev_root = INVALID_PAGE_ID;
    let mngr = get_mngr();

    let mut tree = Tree::empty(false, mngr);
    assert_eq!(tree.root, prev_root);

    tree.put(&[1, 1, 1], &[2, 2, 2]);
    assert_ne!(tree.root, prev_root);
    assert_eq!(tree.is_dirty, true);

    prev_root = tree.root;

    assert_eq!(tree.get(&[1, 1, 1]), Some(vec![2, 2, 2]));
    assert_eq!(tree.root, prev_root);
    assert_eq!(tree.is_dirty, true);

    tree.del(&[1, 1, 1]);
    assert_ne!(tree.root, prev_root);
    assert_eq!(tree.is_dirty, true);
  }

  #[test]
  #[should_panic(expected = "Meta tree is expected")]
  fn test_tree_leaf_fail_invoking_meta_methods() {
    let mngr = get_mngr();
    let leaf_1 = Tree::empty(false, mngr.clone());
    let mut leaf_2 = Tree::empty(false, mngr);
    leaf_2.meta_put(&[1], leaf_1);
  }

  #[test]
  fn test_tree_meta_put_get_del() {
    let mut prev_root = INVALID_PAGE_ID;
    let mngr = get_mngr();

    let leaf = Tree::empty(false, mngr.clone());
    let mut meta = Tree::empty(true, mngr);
    assert_eq!(meta.root, prev_root);

    meta.meta_put(&[1, 1, 1], leaf);
    assert_ne!(meta.root, prev_root);
    assert_eq!(meta.is_dirty, true);

    prev_root = meta.root;

    let new_leaf = meta.meta_get(&[1, 1, 1]).unwrap();
    assert_eq!(meta.root, prev_root);
    assert_eq!(meta.is_dirty, true);
    assert_eq!(new_leaf.is_dirty, false);

    meta.meta_del(&[1, 1, 1]);
    assert_ne!(meta.root, prev_root);
    assert_eq!(meta.is_dirty, true);
  }

  #[test]
  #[should_panic(expected = "Leaf tree is expected")]
  fn test_tree_meta_fail_invoking_leaf_methods() {
    let mngr = get_mngr();
    let mut meta = Tree::empty(true, mngr.clone());
    meta.put(&[1], &[2]);
  }

  fn recur_build_tree(tree: &mut Tree, mut curr_level: usize, levels: usize) {
    if curr_level > levels {
      return;
    }

    curr_level += 1;
    let num_keys = 128;

    if tree.is_meta() {
      for i in 0..num_keys {
        let mut child = Tree::empty(curr_level < levels, tree.mngr.clone());
        recur_build_tree(&mut child, curr_level, levels);
        tree.meta_put(&[i; 128], child);
      }
    } else {
      for i in 0..num_keys {
        tree.put(&[i; 128], &[i; 128]);
      }
    }
  }

  #[test]
  fn test_tree_free() {
    let mngr = get_mngr();
    let mut meta = Tree::empty(true, mngr.clone());
    recur_build_tree(&mut meta, 0, 1);

    meta.free();

    mngr.borrow_mut().sync();

    assert_eq!(meta.root, INVALID_PAGE_ID);
    assert_eq!(meta.is_dirty, true);
    assert_eq!(mngr.borrow().num_pages(), 0);
    assert_eq!(mngr.borrow().num_free_pages(), 0);
  }

  #[test]
  fn test_tree_encode_decode() {
    assert_eq!(decode(&encode(INVALID_PAGE_ID, true)), (INVALID_PAGE_ID, true));
    assert_eq!(decode(&encode(INVALID_PAGE_ID, false)), (INVALID_PAGE_ID, false));

    for i in 0..1_000_000 {
      assert_eq!(decode(&encode(i, false)), (i, false));
      assert_eq!(decode(&encode(i, true)), (i, true));
    }
  }
}
