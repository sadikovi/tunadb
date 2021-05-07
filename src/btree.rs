use crate::cache::PageCache;
use crate::error::Res;
use crate::page::{Page, PageID, PageType};

pub struct BTree<'a> {
  cache: PageCache<'a>,
  root: Option<PageID>,
  page_size: usize,
}

// find (vec, page)
// split
// search + insert

impl<'a> BTree<'a> {
  // Creates a new btree with the cache and root node.
  pub fn new(cache: PageCache<'a>, page_size: usize) -> Self {
    Self { cache: cache, root: None, page_size: page_size }
  }

  // Returns max number of keys that page is supposed to have.
  // Used to decide if we need to split the page.
  fn max_num_keys(&self) -> usize {
    unimplemented!()
  }

  // Returns a leaf node and a vector of traces to the root.
  fn _find_leaf_stack(&mut self, key: &[u8]) -> Res<(Page, Vec<(PageID, usize)>)> {
    // Use parent stack to trace back the path from root to leaf.
    let mut stack = Vec::new();

    let mut page = self.cache.get_page(self.root.expect("Root is not set"))?;
    while !page.is_leaf() {
      // Search for the pointer to the next page
      let (exists, i) = search(&page, key);
      // Find the next page to load
      let next_id = if exists { get_pointer(&page, i + 1)? } else { get_pointer(&page, i)? };
      // Push onto stack the current page and index to trace back
      stack.push((page.id(), i));
      // Return the page to the cache
      self.cache.put_page(page)?;
      // Load the page from the cache, could be a leaf
      page = self.cache.get_page(next_id)?;
    }

    Ok((page, stack))
  }

  fn _find_leaf(&mut self, key: &[u8]) -> Res<Page> {
    let mut page = self.cache.get_page(self.root.expect("Root is not set"))?;
    while !page.is_leaf() {
      let (exists, i) = search(&page, key);
      let next_id = if exists { get_pointer(&page, i + 1)? } else { get_pointer(&page, i)? };
      self.cache.put_page(page)?;
      page = self.cache.get_page(next_id)?;
    }

    Ok(page)
  }

  // Inserts key and value and returns the previous value for the key if exists.
  pub fn insert(&mut self, key: &[u8], value: &[u8]) -> Res<()> {
    // If root is empty, create a node and insert the key.
    if self.root.is_none() {
      let mut page = self.cache.alloc_page(PageType::Leaf, self.page_size)?;
      self.root = Some(page.id());
      insert_leaf(&mut page, key, value)?;
      return self.cache.put_page(page);
    }

    // Root is not empty, we need to find a leaf node to insert
    let (mut page, mut stack) = self._find_leaf_stack(key)?;

    if page.len() >= self.max_num_keys() {
      // Allocate a new leaf page
      let mut right_page = self.cache.alloc_page(PageType::Leaf, self.page_size)?;

      // Find split point and prepare split key, left id and right id for internal nodes
      let split_i = (page.len() >> 1) + 1; // split point
      let mut split_key = get_key(&page, split_i).to_vec(); // split key to propagate to the parent
      let mut left_id = page.id();
      let mut right_id = right_page.id();

      // Move half of the keys into the new page and return the split point
      split_leaf(&mut page, &mut right_page, split_i);

      // Return both pages into the cache
      self.cache.put_page(right_page)?;
      self.cache.put_page(page)?;

      // Now we need to split parent stack
      let mut update_root = true;

      while let Some((parent_id, split_i)) = stack.pop() {
        let mut parent = self.cache.get_page(parent_id)?;
        // Page can fit all of the values, we do not need to check the subsequent parents
        insert_internal(&mut parent, split_i, &split_key, left_id, right_id);

        if parent.len() < self.max_num_keys() {
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
        split_internal(&mut parent, &mut right_parent, split_i);

        // Return both pages into the cache
        self.cache.put_page(right_parent)?;
        self.cache.put_page(parent)?;
      }

      if update_root {
        // Once we have reached this point, it means root is full and we need to grow the tree.
        let mut new_root = self.cache.alloc_page(PageType::Internal, self.page_size)?;
        insert_internal(&mut new_root, 0, &split_key, left_id, right_id);
        // Update the root pointer
        self.root = Some(new_root.id());
        // Return the page into the cache
        self.cache.put_page(new_root)?;
      }

      page = self._find_leaf(key)?;
    }

    // Insert directly into the page
    insert_leaf(&mut page, key, value)
  }

  pub fn delete(&mut self, key: &[u8]) -> Res<()> {
    // If root is empty, the delete is no-op.
    if self.root.is_none() {
      return Ok(());
    }

    let (mut page, mut stack) = self._find_leaf_stack(key)?;

    // The current page is a leaf.

    let (exists, i) = search(&page, key);
    // Return the page if the key does not exist
    if !exists {
      return self.cache.put_page(page);
    }

    delete_leaf(&mut page, i)?;

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
    while let Some((parent_id, ptr)) = stack.pop() {
      let parent = self.cache.get_page(parent_id)?;
      let curr = self.cache.get_page(get_pointer(&parent, ptr)?)?;

      let min_num_keys = self.max_num_keys() / 2;

      if curr.len() < min_num_keys {
        // TODO: the logic here is different from the original btree
        if let Ok(left_id) = get_pointer(&curr, ptr - 1) {
          let left = self.cache.get_page(left_id)?;
          if left.len() > min_num_keys {
            self._steal_from_left()?;
          } else {
            self._merge_sibling()?;
          }
          self.cache.put_page(left)?;
        } else if let Ok(right_id) = get_pointer(&curr, ptr + 1) {
          let right = self.cache.get_page(right_id)?;
          if right.len() > min_num_keys {
            self._steal_from_right()?;
          } else {
            self._merge_sibling()?;
          }
          self.cache.put_page(right)?;
        } else {
          // TODO: Should never happen
          return Err(err!("Invalid case, cannot find siblings"));
        }
      }

      self.cache.put_page(curr)?;
      self.cache.put_page(parent)?;
    }

    // At this point we have reached the parent node
    let root = &mut self.cache.get_page(self.root.unwrap())?;
    // TODO: handle empty root leaf page
    if root.len() == 0 {
      // TODO: delete root page
      self.root = Some(get_pointer(&root, 0)?);
    }

    Ok(())
  }

  fn _steal_from_left(&mut self) -> Res<()> {
    unimplemented!()
  }

  fn _steal_from_right(&mut self) -> Res<()> {
    unimplemented!()
  }

  fn _merge_sibling(&mut self) -> Res<()> {
    unimplemented!()
  }
}

fn search(_page: &Page, _key: &[u8]) -> (bool, usize) {
  unimplemented!()
}

fn get_pointer(_page: &Page, _i: usize) -> Res<PageID> {
  unimplemented!()
}

fn get_key(_page: &Page, _i: usize) -> &[u8] {
  unimplemented!()
}

fn set_key(_page: &mut Page, _i: usize, _key: &[u8]) {
  // this is only for internal nodes to restore keys
  unimplemented!()
}

fn split_leaf(_from: &mut Page, _to: &mut Page, _i: usize) {
  unimplemented!()
}

fn insert_leaf(_page: &mut Page, _key: &[u8], _value: &[u8]) -> Res<()> {
  unimplemented!()
}

fn insert_internal(_page: &mut Page, _i: usize, _key: &[u8], _left_id: PageID, _right_id: PageID) {
  unimplemented!()
}

fn split_internal(_from: &mut Page, _to: &mut Page, _i: usize) {
  unimplemented!()
}

fn delete_leaf(_page: &mut Page, _i: usize) -> Res<()> {
  unimplemented!()
}
