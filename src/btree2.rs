use std::cell::RefCell;
use std::rc::Rc;
use crate::error::Res;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum PageType {
  Leaf,
  Internal,
}

#[derive(Debug)]
pub struct BTreePage {
  id: u64, // unique page id
  snapshot_id: u64, // btree snapshot id, used for GC
  tpe: PageType, // type of the page
  keys: Vec<Vec<u8>>,
  vals: Vec<Vec<u8>>,
  ptrs: Vec<u64>,
}

impl BTreePage {
  pub fn is_leaf(&self) -> bool {
    self.tpe == PageType::Leaf
  }

  pub fn num_keys(&self) -> usize {
    self.keys.len()
  }
}

// Page manager that maintains BTreePage instances.
pub trait BTreePageManager {
  // Creates a new page for the provided snapshot id.
  fn new_page(&mut self, tpe: PageType, snapshot_id: u64) -> Res<BTreePage>;
  // Duplicates the page for the provided snapshot id.
  fn dup_page(&mut self, page_id: u64, snapshot_id: u64) -> Res<BTreePage>;
  // Returns a page for the page id.
  fn get_page(&mut self, page_id: u64) -> Res<Rc<BTreePage>>;
  // Updates the page after `new_page` or `dup_page` calls
  fn put_page(&mut self, page: BTreePage) -> Res<()>;
}

// A simple implementation of copy-on-write B+tree
#[derive(Clone)]
pub struct BTree {
  cache: Rc<RefCell<dyn BTreePageManager>>, // shared mutability for the cache
  root_page_id: u64, // page id that BTree starts with
  snapshot_id: u64, // uniquely identifies the tree
  min_keys: usize,
  max_keys: usize,
}

impl BTree {
  // Cache helpers

  fn cache_new(&self, tpe: PageType) -> Res<BTreePage> {
    self.cache.borrow_mut().new_page(tpe, self.snapshot_id)
  }

  fn cache_clone(&self, page_id: u64) -> Res<BTreePage> {
    self.cache.borrow_mut().dup_page(page_id, self.snapshot_id)
  }

  fn cache_get(&self, page_id: u64) -> Res<Rc<BTreePage>> {
    self.cache.borrow_mut().get_page(page_id)
  }

  fn cache_put(&self, page: BTreePage) -> Res<()> {
    self.cache.borrow_mut().put_page(page)
  }
}

// Returns true if key exists and position to insert
fn bsearch(keys: &[Vec<u8>], key: &[u8]) -> (bool, usize) {
  let mut start = 0;
  let mut end = keys.len();
  // "start" would point to the insertion point where keys[start] >= key
  while start < end {
    let pivot = (start + end - 1) >> 1;
    if key < &keys[pivot] {
      end = pivot;
    } else if key > &keys[pivot] {
      start = pivot + 1;
    } else {
      return (true, pivot);
    }
  }
  (false, start)
}

// Returns Some(value) for an existing key.
// If the key does not exist, returns None.
pub fn get(btree: &BTree, key: &[u8]) -> Res<Option<Vec<u8>>> {
  let mut curr_id = btree.root_page_id;
  loop {
    let page = btree.cache_get(curr_id)?;
    let (exists, pos) = bsearch(&page.keys[..], key);
    if page.is_leaf() {
      return if exists { Ok(Some(page.vals[pos].clone())) } else { Ok(None) };
    } else {
      curr_id = if exists { page.ptrs[pos + 1] } else { page.ptrs[pos] };
    }
  }
}

// B+tree iterator for range scans.
// Allows to specify start and end keys to return a subset of keys.
pub struct BTreeIter<'a, 'b> {
  btree: &'a BTree,
  stack: Vec<(Rc<BTreePage>, usize)>, // stack of internal nodes
  page: Option<Rc<BTreePage>>, // leaf page ref to traverse
  pos: usize, // key position in the leaf page
  end_key: Option<&'b [u8]>,
}

impl<'a, 'b> BTreeIter<'a, 'b> {
  // Creates a new iterator.
  // If start and end keys are not provided, full range is returned.
  pub fn new(btree: &'a BTree, start_key: Option<&[u8]>, end_key: Option<&'b [u8]>) -> Self {
    let mut stack = Vec::new();
    let mut page = btree.cache_get(btree.root_page_id).unwrap();
    while !page.is_leaf() {
      let pos = if let Some(key) = start_key {
        let (exists, i) = bsearch(&page.keys[..], key);
        if exists { i + 1 } else { i } // only applicable to internal pages
      } else {
        0
      };
      stack.push((page.clone(), pos));
      page = btree.cache_get(page.ptrs[pos]).unwrap();
    }
    let pos = if let Some(key) = start_key { bsearch(&page.keys[..], key).1 } else { 0 };
    Self { btree, stack, page: Some(page), pos, end_key }
  }
}

impl<'a, 'b> Iterator for BTreeIter<'a, 'b> {
  type Item = (Vec<u8>, Vec<u8>);

  fn next(&mut self) -> Option<Self::Item> {
    while let Some(page) = &self.page {
      if self.pos < page.num_keys() {
        let key = page.keys[self.pos].clone();
        if let Some(ekey) = self.end_key {
          if &key[..] > ekey {
            self.page = None;
            return None;
          }
        }
        let val = page.vals[self.pos].clone();
        self.pos += 1;
        return Some((key, val))
      } else {
        self.page = None;
        self.pos = 0;
        while let Some((ipage, mut iptr)) = self.stack.pop() {
          if iptr + 1 < ipage.ptrs.len() {
            iptr += 1;
            let mut page = self.btree.cache_get(ipage.ptrs[iptr]).unwrap();
            self.stack.push((ipage, iptr));
            while !page.is_leaf() {
              let tmp_page = self.btree.cache_get(page.ptrs[0]).unwrap();
              self.stack.push((page, 0));
              page = tmp_page;
            }
            self.page = Some(page);
            break;
          }
        }
      }
    }
    None
  }
}

// Puts key and value into the btree.
//
// If the key already exists, the value is updated,
// otherwise a new pair of key and value is inserted.
// The method always returns a new BTree that contains the modification.
pub fn put(btree: &BTree, key: &[u8], value: &[u8]) -> Res<BTree> {
  let mut btree = btree.clone();
  btree.root_page_id = match recur_put(&btree, btree.root_page_id, key, value)? {
    PutResult::Update(page_id) => {
      page_id
    },
    PutResult::Split(left_id, right_id, skey) => {
      // Root page will always be internal after splitting
      let mut page = btree.cache_new(PageType::Internal)?;
      page.keys.push(skey);
      page.ptrs.push(left_id);
      page.ptrs.push(right_id);

      let page_id = page.id;
      btree.cache_put(page)?;
      page_id
    },
  };
  Ok(btree)
}

enum PutResult {
  // Update or insert (page_id)
  Update(u64),
  // Split + update (left_id, right_id, key)
  Split(u64, u64, Vec<u8>),
}

fn recur_put(btree: &BTree, curr_id: u64, key: &[u8], value: &[u8]) -> Res<PutResult> {
  // Clone the page since it will be modified anyway
  let mut page = btree.cache_clone(curr_id)?;
  // Perform search to find the position of the key and whether or not it exists
  let (exists, pos) = bsearch(&page.keys[..], key);

  let res = if page.is_leaf() {
    if exists {
      // Update
      let page_id = page.id;
      page.vals[pos] = value.to_vec();
      btree.cache_put(page)?;
      PutResult::Update(page_id)
    } else if page.num_keys() < btree.max_keys {
      // Direct insert
      let page_id = page.id;
      page.keys.insert(pos, key.to_vec());
      page.vals.insert(pos, value.to_vec());
      btree.cache_put(page)?;
      PutResult::Update(page_id)
    } else {
      // Split + Insert
      let spos = page.num_keys() / 2 + (page.num_keys() & 1); // split point
      // Split key to propagate to the parent
      // If the key is inserted into split position, it becomes the split key
      let skey = if pos == spos { key.to_vec() } else { page.keys[spos].clone() };

      let mut right_page = btree.cache_new(page.tpe)?;
      for i in spos..page.num_keys() {
        right_page.keys.push(page.keys[i].clone());
        right_page.vals.push(page.vals[i].clone());
      }
      page.keys.truncate(spos);
      page.vals.truncate(spos);

      if pos >= spos {
        right_page.keys.insert(pos - spos, key.to_vec());
        right_page.vals.insert(pos - spos, value.to_vec());
      } else {
        page.keys.insert(pos, key.to_vec());
        page.vals.insert(pos, value.to_vec());
      }

      let left_id = page.id;
      let right_id = right_page.id;
      btree.cache_put(page)?;
      btree.cache_put(right_page)?;
      PutResult::Split(left_id, right_id, skey)
    }
  } else {
    let ptr = if exists { pos + 1 } else { pos };
    match recur_put(btree, page.ptrs[ptr], key, value)? {
      PutResult::Update(page_id) => {
        page.ptrs[ptr] = page_id;
        let page_id = page.id;
        btree.cache_put(page)?;
        PutResult::Update(page_id)
      },
      PutResult::Split(left_id, right_id, skey) => {
        // Update the current pointer to the new right node
        page.ptrs[pos] = right_id;
        page.keys.insert(pos, skey);
        page.ptrs.insert(pos, left_id);

        if page.num_keys() < btree.max_keys {
          // Direct insert
          let page_id = page.id;
          btree.cache_put(page)?;
          PutResult::Update(page_id)
        } else {
          // Split + insert
          let spos = page.num_keys() / 2 + 1;
          let skey = page.keys[spos].clone();

          let mut right_page = btree.cache_new(page.tpe)?;
          // Internal nodes do not include the separator key when split
          for i in spos + 1..page.num_keys() {
            right_page.keys.push(page.keys[i].clone());
          }
          // Pointers have +1 length
          for i in spos + 1..page.num_keys() + 1 {
            right_page.ptrs.push(page.ptrs[i]);
          }
          page.keys.truncate(spos);
          page.ptrs.truncate(spos + 1);

          let left_id = page.id;
          let right_id = right_page.id;
          btree.cache_put(page)?;
          btree.cache_put(right_page)?;
          PutResult::Split(left_id, right_id, skey)
        }
      }
    }
  };

  Ok(res)
}

// Deletes a key in the btree.
//
// If the key does not exist, we still return a modified tree.
// TODO: optimise this case
// The method always returns a new BTree that contains the modification.
pub fn del(btree: &BTree, key: &[u8]) -> Res<BTree> {
  let mut btree = btree.clone();
  match recur_del(&btree, btree.root_page_id, key)? {
    DeleteResult::Update(page, ..) => {
      let page_id = if !page.is_leaf() && page.num_keys() == 0 { page.ptrs[0] } else { page.id };
      btree.cache_put(page)?;
      btree.root_page_id = page_id;
      Ok(btree)
    }
  }
}

enum DeleteResult {
  // Delete a key and update smallest (page, next_smallest_key)
  Update(BTreePage, Option<Vec<u8>>),
}

fn recur_del(btree: &BTree, curr_id: u64, key: &[u8]) -> Res<DeleteResult> {
  // Clone the page since it will be modified anyway
  let mut page = btree.cache_clone(curr_id)?;
  // Perform search to find the position of the key and whether or not it exists
  let (exists, pos) = bsearch(&page.keys[..], key);

  let res = if page.is_leaf() {
    let mut next_smallest_key = None;
    if exists {
      // Delete an existing key
      page.keys.remove(pos);
      page.vals.remove(pos);
      // We are deleting the smallest key, update parents to the next smallest
      if pos == 0 && page.num_keys() > 0 {
        next_smallest_key = Some(page.keys[0].clone())
      }
    }
    DeleteResult::Update(page, next_smallest_key)
  } else {
    let ptr = if exists { pos + 1 } else { pos };
    match recur_del(btree, page.ptrs[ptr], key)? {
      DeleteResult::Update(mut child, next_smallest_key) => {
        page.ptrs[ptr] = child.id;

        if exists && page.keys[pos] == key {
          if let Some(smallest_key) = next_smallest_key.clone() {
            page.keys[pos] = smallest_key;
          }
        }

        if child.num_keys() < btree.min_keys {
          if ptr > 0 && btree.cache_get(page.ptrs[ptr - 1])?.num_keys() > btree.min_keys {
            // Steal from the left
            let mut left = btree.cache_clone(page.ptrs[ptr - 1])?;
            page.ptrs[ptr - 1] = left.id;
            steal_from_left(&mut page, ptr, &mut left, &mut child);
            btree.cache_put(left)?;
          } else if ptr < page.num_keys() && btree.cache_get(page.ptrs[ptr + 1])?.num_keys() > btree.min_keys {
            // Steal from the right
            let mut right = btree.cache_clone(page.ptrs[ptr + 1])?;
            page.ptrs[ptr + 1] = right.id;
            steal_from_right(&mut page, ptr, &mut child, &mut right);
            btree.cache_put(right)?;
          } else if ptr == 0 {
            // Merge with the right sibling
            let right = btree.cache_get(page.ptrs[ptr + 1])?;
            merge_right(&mut page, ptr, &mut child, &right)?;
          } else {
            // Merge with the left sibling
            let mut left = btree.cache_clone(page.ptrs[ptr - 1])?;
            page.ptrs[ptr - 1] = left.id;
            merge_right(&mut page, ptr - 1, &mut left, &child)?;
            btree.cache_put(left)?;
          }
        }
        // We are done modifying the child
        btree.cache_put(child)?;

        DeleteResult::Update(page, next_smallest_key)
      },
    }
  };

  Ok(res)
}

// Moves a value from left into curr (ptr).
fn steal_from_left(parent: &mut BTreePage, ptr: usize, left: &mut BTreePage, curr: &mut BTreePage) {
  assert_eq!(left.is_leaf(), curr.is_leaf());

  let num_keys = left.num_keys();
  if curr.is_leaf() {
    let last_key = left.keys.remove(num_keys - 1);
    let last_val = left.vals.remove(num_keys - 1);

    parent.keys[ptr - 1] = last_key.clone();
    curr.keys.insert(0, last_key);
    curr.vals.insert(0, last_val);
  } else {
    let last_key = left.keys.remove(num_keys - 1);
    let last_ptr = left.ptrs.remove(num_keys);

    curr.keys.insert(0, parent.keys[ptr - 1].clone());
    curr.ptrs.insert(0, last_ptr);
    parent.keys[ptr - 1] = last_key;
  }
}

// Moves a value from right into curr (ptr).
fn steal_from_right(parent: &mut BTreePage, ptr: usize, curr: &mut BTreePage, right: &mut BTreePage) {
  assert_eq!(curr.is_leaf(), right.is_leaf());

  if curr.is_leaf() {
    let first_key = right.keys.remove(0);
    let first_val = right.vals.remove(0);

    curr.keys.push(first_key);
    curr.vals.push(first_val);
    parent.keys[ptr] = right.keys[0].clone();
  } else {
    let first_key = right.keys.remove(0);
    let first_ptr = right.ptrs.remove(0);

    curr.keys.push(parent.keys[ptr].clone());
    curr.ptrs.push(first_ptr);
    parent.keys[ptr] = first_key;
  }
}

// Merges right into curr (ptr)
fn merge_right(parent: &mut BTreePage, ptr: usize, curr: &mut BTreePage, right: &BTreePage) -> Res<()> {
  assert_eq!(curr.is_leaf(), right.is_leaf());

  if curr.is_leaf() {
    for i in 0..right.num_keys() {
      curr.keys.push(right.keys[i].clone());
      curr.vals.push(right.vals[i].clone());
    }
  } else {
    curr.keys.push(parent.keys[ptr].clone());

    for i in 0..right.num_keys() {
      curr.keys.push(right.keys[i].clone());
    }
    for i in 0..right.num_keys() + 1 {
      curr.ptrs.push(right.ptrs[i]);
    }
  }

  parent.keys.remove(ptr);
  parent.ptrs.remove(ptr + 1);

  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::fmt;
  use rand::prelude::*;

  fn display(f: &mut fmt::Formatter<'_>, btree: &BTree, page_id: u64, prefix: &mut String) -> fmt::Result {
    let page = btree.cache_get(page_id).unwrap();
    prefix.push(' ');
    if page.is_leaf() {
      writeln!(f, "{}LEAF ({}) snapshot: {}, keys: {}", prefix, page_id, page.snapshot_id, page.keys.len())?;
      for i in 0..page.num_keys() {
        writeln!(f, "{}    k: {:?}, v: {:?}", prefix, &page.keys[i], &page.vals[i])?;
      }
    } else {
      writeln!(f, "{}INTERNAL ({}) snapshot: {}, keys: {}", prefix, page_id, page.snapshot_id, page.keys.len())?;
      prefix.push(' ');
      for i in 1..page.num_keys() + 1 {
        if i == 1 {
          writeln!(f, "{} < {:?}", prefix, page.keys[i - 1])?;
          prefix.push(' ');
          display(f, btree, page.ptrs[0], prefix)?;
          prefix.pop();
        }
        writeln!(f, "{} >= {:?}", prefix, page.keys[i - 1])?;
        prefix.push(' ');
        display(f, btree, page.ptrs[i], prefix)?;
        prefix.pop();
      }
      prefix.pop();
    }
    prefix.pop();
    Ok(())
  }

  impl fmt::Display for BTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      display(f, self, self.root_page_id, &mut String::new())
    }
  }

  struct TestPageManager {
    pages: Vec<Option<Rc<BTreePage>>>,
  }

  impl BTreePageManager for TestPageManager {
    fn new_page(&mut self, page_type: PageType, snapshot_id: u64) -> Res<BTreePage> {
      let page = BTreePage {
        id: self.pages.len() as u64,
        snapshot_id: snapshot_id,
        tpe: page_type,
        keys: Vec::new(),
        vals: Vec::new(),
        ptrs: Vec::new(),
      };
      self.pages.push(None);
      Ok(page)
    }

    fn dup_page(&mut self, page_id: u64, snapshot_id: u64) -> Res<BTreePage> {
      let page_ref = self.get_page(page_id)?;
      let page = BTreePage {
        id: self.pages.len() as u64,
        snapshot_id: snapshot_id,
        tpe: page_ref.tpe,
        keys: page_ref.keys.clone(),
        vals: page_ref.vals.clone(),
        ptrs: page_ref.ptrs.clone(),
      };
      self.pages.push(None);
      Ok(page)
    }

    fn get_page(&mut self, page_id: u64) -> Res<Rc<BTreePage>> {
      Ok(self.pages[page_id as usize].as_ref().expect(&format!("Page {} not found", page_id)).clone())
    }

    fn put_page(&mut self, page: BTreePage) -> Res<()> {
      let page_id = page.id;
      self.pages[page_id as usize] = Some(Rc::new(page));
      Ok(())
    }
  }

  fn new_btree(max_keys_per_page: usize) -> (BTree, Rc<RefCell<TestPageManager>>) {
    let mut cache = TestPageManager { pages: Vec::new() };
    let next_snapshot_id = 123;
    let page = cache.new_page(PageType::Leaf, next_snapshot_id).unwrap();
    let page_id = page.id;
    cache.put_page(page).unwrap();

    let cache_ref = Rc::new(RefCell::new(cache));
    let tree = BTree {
      cache: cache_ref.clone(),
      snapshot_id: next_snapshot_id,
      root_page_id: page_id,
      min_keys: max_keys_per_page / 2,
      max_keys: max_keys_per_page,
    };

    (tree, cache_ref)
  }

  fn assert_page_consistency(cache: &RefCell<TestPageManager>) {
    for page in &cache.borrow().pages[..] {
      assert!(page.is_some(), "Page was borrowed but not returned");
    }
  }

  fn assert_num_pages(cache: &RefCell<TestPageManager>, expected: usize) {
    assert_eq!(cache.borrow().pages.len(), expected);
  }

  fn get_page(cache: &RefCell<TestPageManager>, id: u64) -> Rc<BTreePage> {
    cache.borrow_mut().get_page(id).unwrap()
  }

  #[test]
  fn test_btree_cache_clone() {
    let (tree, cache) = new_btree(5);

    for &tpe in &[PageType::Leaf, PageType::Internal] {
      let page = tree.cache_new(tpe).unwrap();
      let page_id = page.id;
      let page = BTreePage { // create page to make sure we don't miss any new fields
        id: page_id,
        snapshot_id: page.snapshot_id,
        tpe: page.tpe,
        keys: vec![vec![1]],
        vals: vec![vec![2]],
        ptrs: vec![3, 4],
      };
      tree.cache_put(page).unwrap();

      let orig_page = tree.cache_get(page_id).unwrap();
      let cloned_page = tree.cache_clone(page_id).unwrap();

      // If an attribute is missing, please update below
      assert_ne!(orig_page.id, cloned_page.id);
      assert_eq!(orig_page.snapshot_id, cloned_page.snapshot_id);
      assert_eq!(orig_page.tpe, cloned_page.tpe);
      assert_eq!(orig_page.keys, cloned_page.keys);
      assert_eq!(orig_page.vals, cloned_page.vals);
      assert_eq!(orig_page.ptrs, cloned_page.ptrs);

      tree.cache_put(cloned_page).unwrap();
    }

    assert_page_consistency(&cache);
  }

  #[test]
  fn test_btree_snapshot_ids() {
    let (tree1, cache) = new_btree(5);
    assert_eq!(get_page(&cache, tree1.root_page_id).snapshot_id, tree1.snapshot_id);

    let tree2 = put(&tree1, &[1], &[10]).unwrap();
    assert_eq!(get_page(&cache, tree2.root_page_id).snapshot_id, tree2.snapshot_id);

    // BTree clone also clones snapshot ids - this allows us to reduce page allocations on disk
    // since we can return the same page if it was modified in the same snapshot.
    assert_eq!(tree2.snapshot_id, tree1.snapshot_id);
  }

  #[test]
  fn test_btree_put_insert_empty() {
    let (tree, cache) = new_btree(5);
    put(&tree, &[1], &[10]).unwrap();

    assert_page_consistency(&cache);
    assert_num_pages(&cache, 2);

    assert_eq!(get_page(&cache, 0).keys.len(), 0);
    assert_eq!(get_page(&cache, 0).vals.len(), 0);
    assert_eq!(get_page(&cache, 1).keys, &[vec![1]]);
    assert_eq!(get_page(&cache, 1).vals, &[vec![10]]);
  }

  #[test]
  fn test_btree_put_update() {
    let (mut tree, cache) = new_btree(5);
    tree = put(&tree, &[1], &[10]).unwrap();
    put(&tree, &[1], &[20]).unwrap();

    assert_page_consistency(&cache);
    assert_num_pages(&cache, 3);

    assert_eq!(get_page(&cache, 1).keys, &[vec![1]]);
    assert_eq!(get_page(&cache, 1).vals, &[vec![10]]);
    assert_eq!(get_page(&cache, 2).keys, &[vec![1]]);
    assert_eq!(get_page(&cache, 2).vals, &[vec![20]]);
  }

  #[test]
  fn test_btree_put_insert_capacity() {
    let (mut tree, cache) = new_btree(3);
    tree = put(&tree, &[1], &[10]).unwrap();
    tree = put(&tree, &[2], &[20]).unwrap();
    tree = put(&tree, &[3], &[30]).unwrap();

    assert_page_consistency(&cache);
    assert_num_pages(&cache, 4);

    assert_eq!(get_page(&cache, tree.root_page_id).keys, &[vec![1], vec![2], vec![3]]);
    assert_eq!(get_page(&cache, tree.root_page_id).vals, &[vec![10], vec![20], vec![30]]);
  }

  #[test]
  fn test_btree_put_insert_leaf_split() {
    let (mut tree, cache) = new_btree(3);
    tree = put(&tree, &[1], &[10]).unwrap();
    tree = put(&tree, &[2], &[20]).unwrap();
    tree = put(&tree, &[3], &[30]).unwrap();
    tree = put(&tree, &[4], &[40]).unwrap();

    assert_page_consistency(&cache);
    assert_num_pages(&cache, 7);

    assert_eq!(get_page(&cache, tree.root_page_id).keys, &[vec![3]]);
    assert_eq!(get_page(&cache, tree.root_page_id).vals.len(), 0);
    assert_eq!(get_page(&cache, tree.root_page_id).ptrs, &[4, 5]);

    assert_eq!(get_page(&cache, 4).keys, &[vec![1], vec![2]]);
    assert_eq!(get_page(&cache, 4).vals, &[vec![10], vec![20]]);

    assert_eq!(get_page(&cache, 5).keys, &[vec![3], vec![4]]);
    assert_eq!(get_page(&cache, 5).vals, &[vec![30], vec![40]]);
  }

  #[test]
  fn test_btree_put_insert_internal_split() {
    let (mut tree, cache) = new_btree(3);
    for i in 0..10 {
      tree = put(&tree, &[i], &[i * 10]).unwrap();
    }

    assert_page_consistency(&cache);
    assert_num_pages(&cache, 26);

    assert_eq!(get_page(&cache, tree.root_page_id).keys, &[vec![6]]);
    assert_eq!(get_page(&cache, tree.root_page_id).vals.len(), 0);
    assert_eq!(get_page(&cache, tree.root_page_id).ptrs, &[14, 23]);

    assert_eq!(get_page(&cache, 14).keys, &[vec![2], vec![4]]);
    assert_eq!(get_page(&cache, 14).vals.len(), 0);
    assert_eq!(get_page(&cache, 14).ptrs, &[4, 10, 15]);

    assert_eq!(get_page(&cache, 23).keys, &[vec![8]]);
    assert_eq!(get_page(&cache, 23).vals.len(), 0);
    assert_eq!(get_page(&cache, 23).ptrs, &[24, 25]);
  }

  #[test]
  fn test_btree_del_leaf_non_existent() {
    let (mut tree, cache) = new_btree(5);
    for i in 0..3 {
      tree = put(&tree, &[i], &[i * 10]).unwrap();
    }
    for i in 4..10 {
      tree = del(&tree, &[i]).unwrap();
    }

    assert_page_consistency(&cache);
    assert_num_pages(&cache, 10);
    assert_eq!(get_page(&cache, tree.root_page_id).keys, &[vec![0], vec![1], vec![2]]);
    assert_eq!(get_page(&cache, tree.root_page_id).vals, &[vec![0], vec![10], vec![20]]);
  }

  #[test]
  fn test_btree_del_leaf_asc() {
    let (mut tree, cache) = new_btree(5);
    for i in 0..5 {
      tree = put(&tree, &[i], &[i * 10]).unwrap();
    }
    for i in 0..5 {
      tree = del(&tree, &[i]).unwrap();
    }

    assert_page_consistency(&cache);
    assert_num_pages(&cache, 11);
    assert_eq!(get_page(&cache, tree.root_page_id).keys.len(), 0);
    assert_eq!(get_page(&cache, tree.root_page_id).vals.len(), 0);
  }

  #[test]
  fn test_btree_del_leaf_desc() {
    let (mut tree, cache) = new_btree(5);
    for i in 0..5 {
      tree = put(&tree, &[i], &[i * 10]).unwrap();
    }
    for i in (0..5).rev() {
      tree = del(&tree, &[i]).unwrap();
    }

    assert_page_consistency(&cache);
    assert_num_pages(&cache, 11);
    assert_eq!(get_page(&cache, tree.root_page_id).keys.len(), 0);
    assert_eq!(get_page(&cache, tree.root_page_id).vals.len(), 0);
  }

  #[test]
  fn test_btree_del_internal_asc() {
    let (mut tree, cache) = new_btree(5);
    for i in 0..10 {
      tree = put(&tree, &[i], &[i * 10]).unwrap();
    }
    for i in 0..10 {
      tree = del(&tree, &[i]).unwrap();
    }

    assert_page_consistency(&cache);
    assert_num_pages(&cache, 38);
    assert_eq!(get_page(&cache, tree.root_page_id).keys.len(), 0);
    assert_eq!(get_page(&cache, tree.root_page_id).vals.len(), 0);
  }

  #[test]
  fn test_btree_del_internal_desc() {
    let (mut tree, cache) = new_btree(5);
    for i in 0..10 {
      tree = put(&tree, &[i], &[i * 10]).unwrap();
    }
    for i in (0..10).rev() {
      tree = del(&tree, &[i]).unwrap();
    }

    assert_page_consistency(&cache);
    assert_num_pages(&cache, 39);
    assert_eq!(get_page(&cache, tree.root_page_id).keys.len(), 0);
    assert_eq!(get_page(&cache, tree.root_page_id).vals.len(), 0);
  }

  #[test]
  fn test_btree_del_split_key() {
    // Regression test to check that we update next smallest key correctly.
    // When deleting [3], the internal page key needs to be updated to [4]
    // and the subsequent delete of [4] does not cause "index out of bound" error.
    let (mut tree, cache) = new_btree(4);
    tree = put(&tree, &[1], &[1]).unwrap();
    tree = put(&tree, &[2], &[2]).unwrap();
    tree = put(&tree, &[3], &[3]).unwrap();
    tree = put(&tree, &[4], &[4]).unwrap();
    tree = put(&tree, &[5], &[5]).unwrap();
    tree = put(&tree, &[6], &[6]).unwrap();

    tree = del(&tree, &[3]).unwrap();
    tree = del(&tree, &[4]).unwrap();

    assert_page_consistency(&cache);
    assert_eq!(get(&tree, &[3]).unwrap(), None);
    assert_eq!(get(&tree, &[4]).unwrap(), None);
  }

  #[test]
  fn test_btree_get_existent_key() {
    let (mut tree, _) = new_btree(5);
    for i in 0..20 {
      tree = put(&tree, &[i], &[i * 10]).unwrap();
    }
    for i in 0..20 {
      assert_eq!(get(&tree, &[i]).unwrap(), Some(vec![i * 10]));
    }
    for i in (0..20).rev() {
      assert_eq!(get(&tree, &[i]).unwrap(), Some(vec![i * 10]));
    }
  }

  #[test]
  fn test_btree_get_non_existent_key() {
    let (mut tree, _) = new_btree(5);
    for i in 0..20 {
      tree = put(&tree, &[i], &[i * 10]).unwrap();
    }
    for i in 20..40 {
      assert_eq!(get(&tree, &[i]).unwrap(), None);
    }
    for i in (20..40).rev() {
      assert_eq!(get(&tree, &[i]).unwrap(), None);
    }
  }

  #[test]
  fn test_btree_put_get_split_key() {
    // Regression test for the issue when the inserted key falls into split position
    let (mut tree, _) = new_btree(6);
    tree = put(&tree, &[1], &[1]).unwrap();
    tree = put(&tree, &[2], &[2]).unwrap();
    tree = put(&tree, &[3], &[3]).unwrap();
    tree = put(&tree, &[4], &[4]).unwrap();
    tree = put(&tree, &[8], &[8]).unwrap();
    tree = put(&tree, &[9], &[9]).unwrap();

    // This insert results in split
    tree = put(&tree, &[5], &[5]).unwrap();

    assert_eq!(get(&tree, &[5]).unwrap(), Some(vec![5]));
  }

  // BTree range tests

  #[test]
  fn test_btree_range_no_bounds() {
    let (mut tree, _) = new_btree(5);
    let input: Vec<(Vec<u8>, Vec<u8>)> = (0..20).map(|i| (vec![i], vec![i * 10])).collect();

    for i in &input[..] {
      tree = put(&tree, &i.0, &i.1).unwrap();
    }

    let iter = BTreeIter::new(&tree, None, None);
    let res: Vec<(Vec<u8>, Vec<u8>)> = iter.collect();
    assert_eq!(res, input);
  }

  #[test]
  fn test_btree_range_start_bound() {
    let (mut tree, _) = new_btree(5);
    let input: Vec<(Vec<u8>, Vec<u8>)> = (0..20).map(|i| (vec![i], vec![i * 10])).collect();

    for i in &input[..] {
      tree = put(&tree, &i.0, &i.1).unwrap();
    }

    let iter = BTreeIter::new(&tree, Some(&[6]), None);
    let res: Vec<(Vec<u8>, Vec<u8>)> = iter.collect();
    assert_eq!(res, &input[6..]);
  }

  #[test]
  fn test_btree_range_end_bound() {
    let (mut tree, _) = new_btree(5);
    let input: Vec<(Vec<u8>, Vec<u8>)> = (0..20).map(|i| (vec![i], vec![i * 10])).collect();

    for i in &input[..] {
      tree = put(&tree, &i.0, &i.1).unwrap();
    }

    let iter = BTreeIter::new(&tree, None, Some(&[17]));
    let res: Vec<(Vec<u8>, Vec<u8>)> = iter.collect();
    assert_eq!(res, &input[..18]);
  }

  #[test]
  fn test_btree_range_both_bounds() {
    let (mut tree, _) = new_btree(5);
    let input: Vec<(Vec<u8>, Vec<u8>)> = (0..20).map(|i| (vec![i], vec![i * 10])).collect();

    for i in &input[..] {
      tree = put(&tree, &i.0, &i.1).unwrap();
    }

    let iter = BTreeIter::new(&tree, Some(&[6]), Some(&[17]));
    let res: Vec<(Vec<u8>, Vec<u8>)> = iter.collect();
    assert_eq!(res, &input[6..18]);
  }

  #[test]
  fn test_btree_range_outside_of_bounds() {
    let (mut tree, _) = new_btree(5);
    let input: Vec<(Vec<u8>, Vec<u8>)> = (0..20).map(|i| (vec![i + 1], vec![i])).collect();

    for i in &input[..] {
      tree = put(&tree, &i.0, &i.1).unwrap();
    }

    let iter = BTreeIter::new(&tree, Some(&[0]), Some(&[100]));
    let res: Vec<(Vec<u8>, Vec<u8>)> = iter.collect();
    assert_eq!(res, input);
  }

  // BTree fuzz testing

  // A sequence of random byte keys that may contain duplicate values
  fn random_byte_key_seq(len: usize) -> Vec<Vec<u8>> {
    let mut rng = thread_rng();
    let mut input = Vec::with_capacity(len);
    for _ in 0..len {
      input.push(rng.gen::<[u8; 10]>().to_vec());
    }
    input
  }

  // A sequence of unique integer values that are shuffled
  fn random_unique_key_seq(len: usize) -> Vec<Vec<u8>> {
    let mut input = Vec::with_capacity(len);
    for i in 0..len {
      input.push((i as u64).to_be_bytes().to_vec());
    }
    shuffle(&mut input);
    input
  }

  fn shuffle(input: &mut Vec<Vec<u8>>) {
    input.shuffle(&mut thread_rng());
  }

  fn assert_find(btree: &BTree, keys: &[Vec<u8>], assert_match: bool) {
    for key in keys {
      let res = get(btree, key).unwrap();
      if assert_match && res != Some(key.to_vec()) {
        assert!(false, "Failed to find {:?}", key);
      } else if !assert_match && res == Some(key.to_vec()) {
        assert!(false, "Failed, the key {:?} existed", key);
      }
    }
  }

  #[test]
  fn test_fuzz_unique_put_get_del() {
    let mut input = random_unique_key_seq(200);

    for &max_keys in &[10, 11] {
      shuffle(&mut input);

      println!("Input: {:?}, max keys: {}", input, max_keys);

      let (mut tree, cache) = new_btree(max_keys);
      for i in 0..input.len() {
        tree = put(&tree, &input[i], &input[i]).unwrap();
        assert_find(&tree, &input[0..i + 1], true);
        assert_find(&tree, &input[i + 1..], false);
      }

      let iter = BTreeIter::new(&tree, None, None);
      let res: Vec<(Vec<u8>, Vec<u8>)> = iter.collect();
      let mut exp: Vec<(Vec<u8>, Vec<u8>)> = input.iter().map(|i| (i.clone(), i.clone())).collect();
      exp.sort();
      assert_eq!(res, exp);

      shuffle(&mut input);
      for i in 0..input.len() {
        assert_find(&tree, &[input[i].clone()], true);
        tree = del(&tree, &input[i]).unwrap();
        assert_find(&tree, &[input[i].clone()], false);
      }

      assert_page_consistency(&cache);
      assert_eq!(get_page(&cache, tree.root_page_id).keys.len(), 0);
    }
  }

  #[test]
  fn test_fuzz_byte_put_get_del() {
    let mut input = random_byte_key_seq(200);

    for &max_keys in &[10, 11] {
      shuffle(&mut input);

      println!("Input: {:?}, max keys: {}", input, max_keys);

      let (mut tree, cache) = new_btree(max_keys);
      for i in 0..input.len() {
        tree = put(&tree, &input[i], &input[i]).unwrap();
      }

      let iter = BTreeIter::new(&tree, None, None);
      let res: Vec<(Vec<u8>, Vec<u8>)> = iter.collect();
      let mut exp: Vec<(Vec<u8>, Vec<u8>)> = input.iter().map(|i| (i.clone(), i.clone())).collect();
      exp.sort();
      assert_eq!(res, exp);

      shuffle(&mut input);

      for i in 0..input.len() {
        assert!(get(&tree, &input[i]).unwrap().is_some());
      }

      for i in 0..input.len() {
        tree = del(&tree, &input[i]).unwrap();
      }

      assert_page_consistency(&cache);
      assert_eq!(get_page(&cache, tree.root_page_id).keys.len(), 0);
    }
  }

  #[test]
  fn test_fuzz_byte_put_range() {
    let mut input = random_byte_key_seq(200);
    shuffle(&mut input);

    let mut exp: Vec<(Vec<u8>, Vec<u8>)> = input.iter().map(|i| (i.clone(), vec![])).collect();

    let (mut tree, cache) = new_btree(10);
    for (key, val) in &exp[..] {
      tree = put(&tree, &key, &val).unwrap();
    }

    exp.sort();

    for i in 0..exp.len() {
      for j in 0..exp.len() {
        let mut iter = BTreeIter::new(&tree, Some(&exp[i].0), Some(&exp[j].0));
        if i > j {
          assert_eq!(iter.next(), None);
        } else {
          let res: Vec<(Vec<u8>, Vec<u8>)> = iter.collect();
          assert_eq!(&res[..], &exp[i..j + 1]);
        }
      }
    }

    assert_page_consistency(&cache);
  }
}
