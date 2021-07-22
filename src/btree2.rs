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
  capacity: usize, // max number of keys in the page
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

  pub fn capacity(&self) -> usize {
    self.capacity
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
  Ok(BTree { cache: btree.cache.clone(), root_page_id: new_root, page_size: btree.page_size })
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
      page.keys[pos] = value.to_vec();
      btree.cache_put(page)?;
      PutResult::Update(page_id)
    } else if page.num_keys() < page.capacity() {
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
    let ptr_pos = if exists { pos + 1 } else { pos };
    let child_page_id = page.ptrs[ptr_pos];
    match recur_put(btree, child_page_id, key, value)? {
      PutResult::Update(page_id) => {
        page.ptrs[ptr_pos] = page_id;
        let page_id = page.id;
        btree.cache_put(page)?;
        PutResult::Update(page_id)
      },
      PutResult::Split(left_id, right_id, skey) => {
        // Update the current pointer to the new right node
        page.ptrs[pos] = right_id;
        page.keys.insert(pos, skey);
        page.ptrs.insert(pos, left_id);

        if page.num_keys() < page.capacity() {
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
