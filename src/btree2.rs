use std::cell::RefCell;
use std::rc::Rc;
use crate::error::Res;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum PageType {
  Leaf,
  Internal,
}

#[derive(Debug)]
pub struct Page {
  id: u64, // unique page id
  tpe: PageType, // type of the page
  prev: Option<u64>, // optional ptr to the previous page
  next: Option<u64>, // optional ptr to the next page
  keys: Vec<Vec<u8>>,
  vals: Vec<Vec<u8>>,
  ptrs: Vec<u64>,
}

impl Page {
  pub fn is_leaf(&self) -> bool {
    self.tpe == PageType::Leaf
  }

  pub fn num_keys(&self) -> usize {
    self.keys.len()
  }

  // Copies the content of this page into the new page except page id
  pub fn copy(&self, page: &mut Page) {
    // TODO: check if page type is the same
    unimplemented!();
  }
}

// Page manager that maintains pages on disk or in memory.
pub trait PageManager {
  // Creates new page and returns it.
  fn new_page(&mut self, page_type: PageType, page_size: usize) -> Res<Page>;
  // Returns a clone of the page for the provided page id.
  fn cln_page(&mut self, page_id: u64) -> Res<Page>;
  // Returns a page for the page id.
  fn get_page(&mut self, page_id: u64) -> Res<Rc<Page>>;
  // Updates the page.
  fn put_page(&mut self, page: Page) -> Res<()>;
  // Deletes the page for the page id.
  fn del_page(&mut self, page_id: u64) -> Res<()>;
}

// A simple B+tree implementation
pub struct BTree {
  cache: Rc<RefCell<dyn PageManager>>, // shared mutability for the cache
  root_page_id: u64, // page id that BTree starts with
  page_size: usize,
  min_keys: usize,
  max_keys: usize,
}

impl BTree {
  // Cache helpers

  fn cache_new(&self, tpe: PageType) -> Res<Page> {
    self.cache.borrow_mut().new_page(tpe, self.page_size)
  }

  fn cache_clone(&self, page_id: u64) -> Res<Page> {
    self.cache.borrow_mut().cln_page(page_id)
  }

  fn cache_get(&self, page_id: u64) -> Res<Rc<Page>> {
    self.cache.borrow_mut().get_page(page_id)
  }

  fn cache_put(&self, page: Page) -> Res<()> {
    self.cache.borrow_mut().put_page(page)
  }

  fn cache_del(&self, page_id: u64) -> Res<()> {
    self.cache.borrow_mut().del_page(page_id)
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

// Puts key and value into the btree.
//
// If the key already exists, the value is updated, otherwise a new pair of key and value is
// inserted.
// The method always returns a new BTree that contains the modification.
pub fn put(btree: &mut BTree, key: &[u8], value: &[u8]) -> Res<BTree> {
  let new_root = match recur_put(btree, btree.root_page_id, key, value)? {
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
  Ok(BTree {
    cache: btree.cache.clone(),
    root_page_id: new_root,
    page_size: btree.page_size,
    min_keys: btree.min_keys,
    max_keys: btree.max_keys,
  })
}

enum PutResult {
  // Update or insert (page_id)
  Update(u64),
  // Split + update (left_id, right_id, key)
  Split(u64, u64, Vec<u8>),
}

fn recur_put(btree: &mut BTree, curr_id: u64, key: &[u8], value: &[u8]) -> Res<PutResult> {
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
      let spos = page.num_keys() / 2 + 1; // split point
      let skey = page.keys[spos].clone(); // split key to propagate to the parent

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

      // Update prev/next pointers for the set of pages
      if let Some(page_id) = page.next {
        let mut next_page = btree.cache_clone(page_id)?;
        next_page.prev = Some(right_page.id);
        btree.cache_put(next_page)?;
      }
      right_page.next = page.next;
      right_page.prev = Some(page.id);
      page.next = Some(right_page.id);

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
// If the key does not exist, we still return a modified tree
// TODO: optimise this case
pub fn del(btree: &mut BTree, key: &[u8]) -> Res<BTree> {
  match recur_del(btree, btree.root_page_id, key)? {
    DeleteResult::Update(page, ..) => {
      let page_id = if !page.is_leaf() && page.num_keys() == 0 { page.ptrs[0] } else { page.id };
      btree.cache_put(page)?;

      Ok(BTree {
        cache: btree.cache.clone(),
        root_page_id: page_id,
        page_size: btree.page_size,
        min_keys: btree.min_keys,
        max_keys: btree.max_keys,
      })
    }
  }
}

enum DeleteResult {
  // Delete a key and update smallest (page, next_smallest_key)
  Update(Page, Option<Vec<u8>>),
}

fn recur_del(btree: &mut BTree, curr_id: u64, key: &[u8]) -> Res<DeleteResult> {
  // Clone the page since it will be modified anyway
  let mut page = btree.cache_clone(curr_id)?;
  // Perform search to find the position of the key and whether or not it exists
  let (exists, pos) = bsearch(&page.keys[..], key);

  // Repair requires three nodes: parent and 2 child nodes
  // We do it at the internal node level

  let res = if page.is_leaf() {
    let mut next_smallest_key = None;

    if exists {
      // Delete an existing key
      page.keys.remove(pos);
      page.vals.remove(pos);

      // We are deleting the smallest key, update parents to the next smallest
      next_smallest_key = if pos == 0 && page.num_keys() > 0 {
        Some(page.keys[0].clone())
      } else {
        None
      };
    }

    DeleteResult::Update(page, next_smallest_key)
  } else {
    let ptr = if exists { pos + 1 } else { pos };
    match recur_del(btree, page.ptrs[ptr], key)? {
      DeleteResult::Update(mut child, next_smallest_key) => {
        page.ptrs[ptr] = child.id;
        if let Some(smallest_key) = next_smallest_key.clone() {
          if &page.keys[pos] == &smallest_key {
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
            merge_right(btree, &mut page, ptr, &mut child, &right)?;
          } else {
            // Merge with the left sibling
            let mut left = btree.cache_clone(page.ptrs[ptr - 1])?;
            page.ptrs[ptr - 1] = left.id;
            merge_right(btree, &mut page, ptr - 1, &mut left, &child)?;
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

fn steal_from_left(parent: &mut Page, ptr: usize, left: &mut Page, curr: &mut Page) {
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

fn steal_from_right(parent: &mut Page, ptr: usize, curr: &mut Page, right: &mut Page) {
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

    curr.keys.push(parent.keys[ptr - 1].clone());
    curr.ptrs.push(first_ptr);
    parent.keys[ptr] = first_key;
  }
}

// Merge right into curr
fn merge_right(btree: &mut BTree, parent: &mut Page, ptr: usize, curr: &mut Page, right: &Page) -> Res<()> {
  assert_eq!(curr.is_leaf(), right.is_leaf());

  if curr.is_leaf() {
    for i in 0..right.num_keys() {
      curr.keys.push(right.keys[i].clone());
      curr.vals.push(right.vals[i].clone());
    }
    // Update prev/next pointers

    curr.next = right.next;
    if let Some(right_id) = right.next {
      let mut right_next = btree.cache_clone(right_id)?;
      right_next.prev = Some(curr.id);
      btree.cache_put(right_next)?;
    }
  } else {
    curr.keys.push(parent.keys[ptr].clone());

    for i in 0..right.num_keys() {
      curr.keys.push(right.keys[i].clone());
    }
    for i in 0..right.num_keys() + 1 {
      curr.ptrs.push(right.ptrs[i].clone());
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

  fn display(f: &mut fmt::Formatter<'_>, btree: &BTree, page_id: u64, pad: usize) -> fmt::Result {
    let page = btree.cache_get(page_id).unwrap();
    let shift = " ".repeat(pad);
    if page.is_leaf() {
      writeln!(f, "{}* ({}) keys: {}", shift, page_id, page.keys.len())?;
      for i in 0..page.num_keys() {
        writeln!(f, "{}    k: {:?}, v: {:?}", shift, &page.keys[i], &page.vals[i])?;
      }
    } else {
      writeln!(f, "{}+ ({}) keys: {}", shift, page_id, page.keys.len())?;
      for i in 1..page.num_keys() + 1 {
        if i == 1 {
          writeln!(f, "{} < {:?}", shift, page.keys[i - 1])?;
          display(f, btree, page.ptrs[0], pad + 4)?;
        }
        writeln!(f, "{} >= {:?}", shift, page.keys[i - 1])?;
        display(f, btree, page.ptrs[i], pad + 4)?;
      }
    }
    Ok(())
  }

  impl fmt::Display for BTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      display(f, self, self.root_page_id, 0)
    }
  }

  struct TestPageManager {
    pages: Vec<Option<Rc<Page>>>,
  }

  impl PageManager for TestPageManager {
    fn new_page(&mut self, page_type: PageType, page_size: usize) -> Res<Page> {
      let page = Page {
        id: self.pages.len() as u64,
        tpe: page_type,
        prev: None,
        next: None,
        keys: Vec::new(),
        vals: Vec::new(),
        ptrs: Vec::new(),
      };
      self.pages.push(None);
      Ok(page)
    }

    fn cln_page(&mut self, page_id: u64) -> Res<Page> {
      let page_ref = self.get_page(page_id)?;
      let page = Page {
        id: self.pages.len() as u64,
        tpe: page_ref.tpe,
        prev: page_ref.prev,
        next: page_ref.next,
        keys: page_ref.keys.clone(),
        vals: page_ref.vals.clone(),
        ptrs: page_ref.ptrs.clone(),
      };
      self.pages.push(None);
      Ok(page)
    }

    fn get_page(&mut self, page_id: u64) -> Res<Rc<Page>> {
      Ok(self.pages[page_id as usize].as_ref().expect(&format!("Page {} not found", page_id)).clone())
    }

    fn put_page(&mut self, page: Page) -> Res<()> {
      let page_id = page.id;
      self.pages[page_id as usize] = Some(Rc::new(page));
      Ok(())
    }

    fn del_page(&mut self, page_id: u64) -> Res<()> {
      self.pages[page_id as usize] = None;
      Ok(())
    }
  }

  fn new_btree(max_keys_per_page: usize) -> (BTree, Rc<RefCell<TestPageManager>>) {
    let mut cache = TestPageManager { pages: Vec::new() };
    let page = cache.new_page(PageType::Leaf, max_keys_per_page).unwrap();
    let page_id = page.id;
    cache.put_page(page).unwrap();

    let cache_ref = Rc::new(RefCell::new(cache));
    let tree = BTree {
      cache: cache_ref.clone(),
      root_page_id: page_id,
      page_size: max_keys_per_page,
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

  fn get_page(cache: &RefCell<TestPageManager>, id: u64) -> Rc<Page> {
    cache.borrow_mut().get_page(id).unwrap()
  }

  #[test]
  fn test_btree_put_insert_empty() {
    let (mut tree, cache) = new_btree(5);
    put(&mut tree, &[1], &[10]).unwrap();

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
    tree = put(&mut tree, &[1], &[10]).unwrap();
    tree = put(&mut tree, &[1], &[20]).unwrap();

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
    tree = put(&mut tree, &[1], &[10]).unwrap();
    tree = put(&mut tree, &[2], &[20]).unwrap();
    tree = put(&mut tree, &[3], &[30]).unwrap();

    assert_page_consistency(&cache);
    assert_num_pages(&cache, 4);

    assert_eq!(get_page(&cache, tree.root_page_id).keys, &[vec![1], vec![2], vec![3]]);
    assert_eq!(get_page(&cache, tree.root_page_id).vals, &[vec![10], vec![20], vec![30]]);
  }

  #[test]
  fn test_btree_put_insert_leaf_split() {
    let (mut tree, cache) = new_btree(3);
    tree = put(&mut tree, &[1], &[10]).unwrap();
    tree = put(&mut tree, &[2], &[20]).unwrap();
    tree = put(&mut tree, &[3], &[30]).unwrap();
    tree = put(&mut tree, &[4], &[40]).unwrap();

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
      tree = put(&mut tree, &[i], &[i * 10]).unwrap();
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
      tree = put(&mut tree, &[i], &[i * 10]).unwrap();
    }
    for i in 4..10 {
      tree = del(&mut tree, &[i]).unwrap();
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
      tree = put(&mut tree, &[i], &[i * 10]).unwrap();
    }
    for i in 0..5 {
      tree = del(&mut tree, &[i]).unwrap();
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
      tree = put(&mut tree, &[i], &[i * 10]).unwrap();
    }
    for i in (0..5).rev() {
      tree = del(&mut tree, &[i]).unwrap();
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
      tree = put(&mut tree, &[i], &[i * 10]).unwrap();
    }
    for i in 0..10 {
      tree = del(&mut tree, &[i]).unwrap();
    }

    assert_page_consistency(&cache);
    assert_num_pages(&cache, 39);
    assert_eq!(get_page(&cache, tree.root_page_id).keys.len(), 0);
    assert_eq!(get_page(&cache, tree.root_page_id).vals.len(), 0);
  }

  #[test]
  fn test_btree_del_internal_desc() {
    let (mut tree, cache) = new_btree(5);
    for i in 0..10 {
      tree = put(&mut tree, &[i], &[i * 10]).unwrap();
    }
    for i in (0..10).rev() {
      tree = del(&mut tree, &[i]).unwrap();
    }

    assert_page_consistency(&cache);
    assert_num_pages(&cache, 39);
    assert_eq!(get_page(&cache, tree.root_page_id).keys.len(), 0);
    assert_eq!(get_page(&cache, tree.root_page_id).vals.len(), 0);
  }

  #[test]
  fn test_btree_get_existent_key() {
    let (mut tree, cache) = new_btree(5);
    for i in 0..20 {
      tree = put(&mut tree, &[i], &[i * 10]).unwrap();
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
    let (mut tree, cache) = new_btree(5);
    for i in 0..20 {
      tree = put(&mut tree, &[i], &[i * 10]).unwrap();
    }
    for i in 20..40 {
      assert_eq!(get(&tree, &[i]).unwrap(), None);
    }
    for i in (20..40).rev() {
      assert_eq!(get(&tree, &[i]).unwrap(), None);
    }
  }
}
