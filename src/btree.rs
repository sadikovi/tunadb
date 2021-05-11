use crate::cache::PageCache;
use crate::error::Res;
use crate::page::{Page, PageID, PageType};

pub struct BTree<'a> {
  cache: PageCache<'a>,
  root: PageID,
  page_size: usize,
  min_num_keys: usize,
  max_num_keys: usize,
}

impl<'a> BTree<'a> {
  // Creates a new btree with the cache and root node.
  pub fn new(mut cache: PageCache<'a>, page_size: usize) -> Res<Self> {
    // Allocate the first page for the tree
    let page = cache.alloc_page(PageType::Leaf, page_size)?;
    let root = page.id();
    cache.put_page(page)?;

    // Calculate min and max number of keys that a page is supposed to have.
    // Used to decide if we need to split or merge the page.
    let min_num_keys = 6;
    let max_num_keys = 12;

    Ok(Self {
      cache: cache,
      root: root,
      page_size: page_size,
      min_num_keys: min_num_keys,
      max_num_keys: max_num_keys
    })
  }

  // Returns a borrowed leaf page and a vector of traces to the root for the given key.
  fn _find_leaf_stack(&mut self, key: &[u8]) -> Res<(Page, Vec<(PageID, usize)>)> {
    // Use parent stack to trace back the path from root to leaf.
    let mut stack = Vec::new();

    let mut page = self.cache.get_page(self.root)?;
    while !page.is_leaf() {
      // Search for the pointer to the next page
      let (exists, i) = search(&page, key);
      // Find the next page to load
      let next_id = if exists { get_ptr(&page, i + 1) } else { get_ptr(&page, i) };
      // Push onto stack the current page and index to trace back
      stack.push((page.id(), i));
      // Return the page to the cache
      self.cache.put_page(page)?;
      // Load the page from the cache, could be a leaf
      page = self.cache.get_page(next_id)?;
    }

    Ok((page, stack))
  }

  // Returns a borrowed leaf page for the given key.
  fn _find_leaf(&mut self, key: &[u8]) -> Res<Page> {
    let mut page = self.cache.get_page(self.root)?;
    while !page.is_leaf() {
      let (exists, i) = search(&page, key);
      let next_id = if exists { get_ptr(&page, i + 1) } else { get_ptr(&page, i) };
      self.cache.put_page(page)?;
      page = self.cache.get_page(next_id)?;
    }

    Ok(page)
  }

  // Inserts or updates a new key-value pair into the leaf page.
  fn _insert_leaf(page: &mut Page, key: &[u8], value: &[u8]) {
    assert!(page.is_leaf());

    let (exists, pos) = search(page, key);
    if exists {
      set_key_value(page, pos, key, value);
    } else {
      insert_key_value(page, pos, key, value);
    }
  }

  // Inserts or updates key and pointers for an internal page.
  // Both nodes left_id and right_id are children of the provided node.
  fn _insert_internal(page: &mut Page, pos: usize, key: &[u8], left_id: PageID, right_id: PageID) {
    assert!(!page.is_leaf());

    // Update the current pointer to the new right node
    set_ptr(page, pos, right_id);
    // Shift elements (keys and pointers) after pos to the right
    // Insert the new key and pointer at pos
    insert_key(page, pos, key);
    insert_ptr(page, pos, left_id);
  }

  // Splits the keys and values and moves the half to another page starting at pos.
  fn _split_leaf(from: &mut Page, to: &mut Page, pos: usize) {
    assert!(from.is_leaf() && to.is_leaf());
    assert_eq!(to.len(), 0);

    // Move the second half into "to"
    for i in pos..from.len() {
      insert_key_value(to, i - pos, get_key(from, i), get_value(from, i));
    }
    // Remove those keys from "from"
    let from_len = from.len();
    for i in (pos..from_len).rev() {
      delete_key_value(from, i);
    }
  }

  // Splits the keys and pointers and moves the half to another page starting at pos.
  fn _split_internal(from: &mut Page, to: &mut Page, pos: usize) {
    assert!(!from.is_leaf() && !to.is_leaf());
    assert_eq!(to.len(), 0);

    // Internal pages do not include the separator key
    for i in pos + 1..from.len() {
      insert_key(to, i - pos - 1, get_key(from, i));
    }
    // Pointers have +1 length
    for i in pos + 1..from.len() + 1 {
      insert_ptr(to, i - pos - 1, get_ptr(from, i));
    }
    // Delete keys and pointers from "from"
    // Do not include the separate key at "pos"
    let from_len = from.len();
    for i in (pos..from_len).rev() {
      delete_key(from, i);
      delete_ptr(from, i + 1);
    }
  }

  // Moves one key/value/pointer from the left sibling to the current page.
  // For internal nodes, keys are rotated.
  fn _steal_from_left(parent: &mut Page, ptr: usize, curr: &mut Page, left: &mut Page) {
    assert_eq!(curr.is_leaf(), left.is_leaf());

    if curr.is_leaf() {
      // The key will be the smallest key in "curr"
      insert_key_value(curr, 0, get_key(left, left.len() - 1), get_value(left, left.len() - 1));
      set_key(parent, ptr - 1, get_key(left, left.len() - 1));
      delete_key_value(left, left.len() - 1);
    } else {
      // curr[0].key is the same as the parent key for that node
      // parent[ptr - 1].key is the same as the last key in left
      insert_key(curr, 0, get_key(parent, ptr - 1));
      insert_ptr(curr, 0, get_ptr(left, left.len()));
      set_key(parent, ptr - 1, get_key(left, left.len() - 1));
      delete_ptr(left, left.len()); // does not decrement length
      delete_key(left, left.len() - 1);
    }
  }

  // Moves one key/value/pointer from the right sibling to the current page.
  // For internal nodes, keys are rotated.
  fn _steal_from_right(parent: &mut Page, ptr: usize, curr: &mut Page, right: &mut Page) {
    assert_eq!(curr.is_leaf(), right.is_leaf());

    let curr_len = curr.len();

    if curr.is_leaf() {
      // The key will be the largest key in "curr"
      insert_key_value(curr, curr_len, get_key(right, 0), get_value(right, 0));
      set_key(parent, ptr, get_key(right, 1));
      delete_key_value(right, 0);
    } else {
      insert_key(curr, curr_len, get_key(parent, ptr)); // increments curr.len()
      insert_ptr(curr, curr_len + 1, get_ptr(right, 0));
      set_key(parent, ptr, get_key(right, 0));
      delete_key(right, 0);
      delete_ptr(right, 0);
    }
  }

  // Merges "curr" into "left" by moving data from curr page to left page.
  // Page "curr" should be treated as empty and will be deleted afterwards.
  fn _merge_right(parent: &mut Page, ptr: usize, left: &mut Page, curr: &mut Page, right: Option<&mut Page>) {
    assert_eq!(left.is_leaf(), curr.is_leaf());

    let left_len = left.len();

    if left.is_leaf() {
      for i in 0..curr.len() {
        insert_key_value(left, left_len + i, get_key(curr, i), get_value(curr, i));
      }
    } else {
      insert_key(left, left_len, get_key(parent, ptr)); // aligns left keys with ptrs
      for i in 0..curr.len() {
        insert_key(left, left_len + 1 + i, get_key(curr, i));
      }
      for i in 0..curr.len() + 1 {
        insert_ptr(left, left_len + 1 + i, get_ptr(curr, i));
      }

      assert_eq!(left.len(), left_len + curr.len() + 1);
    }

    delete_key(parent, ptr);
    delete_ptr(parent, ptr + 1);

    // Update prev and next pointers
    if let Some(right) = right {
      set_prev_page(right, get_prev_page(curr));
    }
    set_next_page(left, get_next_page(curr));
    set_prev_page(curr, None);
    set_next_page(curr, None);
  }

  // Inserts key and value.
  pub fn insert(&mut self, key: &[u8], value: &[u8]) -> Res<()> {
    let (mut page, mut stack) = self._find_leaf_stack(key)?;

    if page.len() >= self.max_num_keys {
      // Allocate a new leaf page
      let mut right_page = self.cache.alloc_page(PageType::Leaf, self.page_size)?;

      // Find split point and prepare split key, left id and right id for internal nodes
      let split_i = (page.len() >> 1) + 1; // split point
      let mut split_key = get_key(&page, split_i).to_vec(); // split key to propagate to the parent
      let mut left_id = page.id();
      let mut right_id = right_page.id();

      // Move half of the keys into the new page and return the split point
      Self::_split_leaf(&mut page, &mut right_page, split_i);

      // Update prev and next pointers
      set_prev_page(&mut right_page, Some(page.id()));
      set_next_page(&mut right_page, get_next_page(&page));
      set_next_page(&mut page, Some(right_page.id()));
      if let Some(next_id) = get_next_page(&page) {
        let mut next_page = self.cache.get_page(next_id)?;
        set_prev_page(&mut next_page, Some(right_page.id()));
        self.cache.put_page(next_page)?;
      }

      // Return both pages into the cache
      self.cache.put_page(right_page)?;
      self.cache.put_page(page)?;

      // Now we need to split parent stack
      let mut update_root = true;

      while let Some((parent_id, split_i)) = stack.pop() {
        let mut parent = self.cache.get_page(parent_id)?;
        // Page can fit all of the values, we do not need to check the subsequent parents
        Self::_insert_internal(&mut parent, split_i, &split_key, left_id, right_id);

        if parent.len() < self.max_num_keys {
          update_root = false;
          self.cache.put_page(parent)?;
          break;
        }

        // Allocate a new internal page
        let mut right_parent = self.cache.alloc_page(PageType::Internal, self.page_size)?;

        // Find the new split point
        let split_i = (parent.len() >> 1) + 1;
        split_key = get_key(&parent, split_i).to_vec();
        left_id = parent.id();
        right_id = right_parent.id();

        // Move half of the keys into the right parent
        Self::_split_internal(&mut parent, &mut right_parent, split_i);

        // Return both pages into the cache
        self.cache.put_page(right_parent)?;
        self.cache.put_page(parent)?;
      }

      if update_root {
        // Once we have reached this point, it means root is full and we need to grow the tree.
        let mut new_root = self.cache.alloc_page(PageType::Internal, self.page_size)?;
        Self::_insert_internal(&mut new_root, 0, &split_key, left_id, right_id);
        // Update the root pointer
        self.root = new_root.id();
        // Return the page into the cache
        self.cache.put_page(new_root)?;
      }

      page = self._find_leaf(key)?;
    }

    // Insert directly into the page
    Self::_insert_leaf(&mut page, key, value);
    Ok(())
  }

  pub fn delete(&mut self, key: &[u8]) -> Res<()> {
    let (mut page, mut stack) = self._find_leaf_stack(key)?;
    let (exists, i) = search(&page, key);
    // Return the page if the key does not exist
    if !exists {
      return self.cache.put_page(page);
    }

    delete_key_value(&mut page, i);

    // Fix the parent links because we are deleting the smallest key
    // We can only fix parent links if the next smallest key exists
    if i == 0 && page.len() > 0 {
      let next_smallest_key = get_key(&page, 0);
      // Restore pointers
      for k in (0..stack.len()).rev() {
        let (parent_id, pos) = stack[k];
        let mut parent = self.cache.get_page(parent_id)?;
        if get_key(&parent, pos) == key {
          set_key(&mut parent, pos, next_smallest_key);
        }
        self.cache.put_page(parent)?;
      }
    }

    self.cache.put_page(page)?;

    // Restore parents after delete

    let mut stop_early = false;
    while let Some((parent_id, ptr)) = stack.pop() {
      let mut parent = self.cache.get_page(parent_id)?;
      let mut curr = self.cache.get_page(get_ptr(&parent, ptr))?;

      let mut page_id_to_delete: Option<PageID> = None;

      if curr.len() >= self.min_num_keys {
        stop_early = true;
      } else {
        let mut left = if ptr > 0 {
          Some(self.cache.get_page(get_ptr(&parent, ptr - 1))?)
        } else {
          None
        };
        let mut right = if ptr < parent.len() {
          Some(self.cache.get_page(get_ptr(&parent, ptr + 1))?)
        } else {
          None
        };

        if left.is_some() && left.as_ref().unwrap().len() > self.min_num_keys {
          Self::_steal_from_left(&mut parent, ptr, &mut curr, left.as_mut().unwrap());
          stop_early = true;
        } else if right.is_some() && right.as_ref().unwrap().len() > self.min_num_keys {
          Self::_steal_from_right(&mut parent, ptr, &mut curr, right.as_mut().unwrap());
          stop_early = true;
        } else if right.is_some() {
          let mut right_next = if let Some(right_next_id) = get_next_page(right.as_ref().unwrap()) {
            Some(self.cache.get_page(right_next_id)?)
          } else {
            None
          };
          Self::_merge_right(&mut parent, ptr, &mut curr, right.as_mut().unwrap(), right_next.as_mut());
          if let Some(right_next) = right_next {
            self.cache.put_page(right_next)?;
          }
          page_id_to_delete = right.as_ref().map(|p| p.id());
        } else if left.is_some() {
          Self::_merge_right(&mut parent, ptr - 1, left.as_mut().unwrap(), &mut curr, right.as_mut());
          page_id_to_delete = Some(curr.id());
        } else {
          // TODO: Should never happen
          panic!("Invalid case, cannot find siblings");
        }

        if let Some(left_page) = left {
          self.cache.put_page(left_page)?;
        }
        if let Some(right_page) = right {
          self.cache.put_page(right_page)?;
        }
      }

      self.cache.put_page(curr)?;
      self.cache.put_page(parent)?;

      if let Some(page_id_to_delete) = page_id_to_delete {
        self.cache.free_page(page_id_to_delete)?;
      }

      if stop_early {
        break;
      }
    }

    // Check if we need to update root
    if !stop_early {
      // At this point we have reached the parent node
      let root = self.cache.get_page(self.root)?;
      // If root is leaf and empty, do nothing
      if root.len() == 0 && !root.is_leaf() {
        self.root = get_ptr(&root, 0);
        // Delete the old root page
        let old_root_id = root.id();
        self.cache.put_page(root)?;
        self.cache.free_page(old_root_id)?;
      }
    }

    Ok(())
  }
}

////////////////////////////////////////////////////////////////
// Page methods
////////////////////////////////////////////////////////////////

fn search(_page: &Page, _key: &[u8]) -> (bool, usize) {
  unimplemented!()
}

fn get_key(_page: &Page, _pos: usize) -> &[u8] {
  unimplemented!()
}

fn get_value(_page: &Page, _pos: usize) -> &[u8] {
  unimplemented!()
}

fn get_ptr(_page: &Page, _pos: usize) -> PageID {
  unimplemented!()
}

// Does not shift elements if it is the last element
fn insert_key(_page: &mut Page, _pos: usize, _key: &[u8]) {
  unimplemented!()
}

// Does not shift elements if it is the last element
fn insert_key_value(_page: &mut Page, _pos: usize, _key: &[u8], _value: &[u8]) {
  unimplemented!()
}

// Does not shift elements if it is the last element
fn insert_ptr(_page: &mut Page, _pos: usize, _ptr: PageID) {
  unimplemented!()
}

fn set_key(_page: &mut Page, _pos: usize, _key: &[u8]) {
  unimplemented!()
}

fn set_key_value(_page: &mut Page, _pos: usize, _key: &[u8], _value: &[u8]) {
  unimplemented!()
}

fn set_ptr(_page: &mut Page, _pos: usize, _ptr: PageID) {
  unimplemented!()
}

fn delete_key(_page: &mut Page, _pos: usize) {
  unimplemented!()
}

// Does not shift elements if it is the last element
fn delete_key_value(_page: &mut Page, _pos: usize) {
  unimplemented!()
}

fn delete_ptr(_page: &mut Page, _pos: usize) {
  unimplemented!()
}

fn get_prev_page(_page: &Page) -> Option<PageID> {
  unimplemented!()
}

fn get_next_page(_page: &Page) -> Option<PageID> {
  unimplemented!()
}

fn set_prev_page(_page: &mut Page, _ptr: Option<PageID>) {
  unimplemented!()
}

fn set_next_page(_page: &mut Page, _ptr: Option<PageID>) {
  unimplemented!()
}
