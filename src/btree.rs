use crate::cache::PageCache;
use crate::error::Res;
use crate::page::{Page, PageID, PageType};

pub struct BTree<'a> {
  cache: PageCache<'a>,
  root: Option<PageID>,
  page_size: usize,
}

impl<'a> BTree<'a> {
  // Creates a new btree with the cache and root node.
  pub fn new(cache: PageCache<'a>, page_size: usize) -> Self {
    Self { cache: cache, root: None, page_size: page_size }
  }

  // Returns max number of keys that page is supposed to have.
  // Used to decide if we need to split the page.
  fn max_allowed_keys(&self) -> usize {
    unimplemented!()
  }

  // Inserts key and value and returns the previous value for the key if exists.
  pub fn insert(&mut self, key: &[u8], value: &[u8]) -> Res<()> {
    // If root is empty, create a node and insert the key.
    if self.root.is_none() {
      let mut page = self.cache.alloc_page(PageType::Leaf, self.page_size)?;
      self.root = Some(page.id());
      insert_key_value(&mut page, key, value);
      return self.cache.put_page(page);
    }

    // Root is not empty, we need to find a leaf node to insert.

    // Use parent stack to trace back the path from root to leaf.
    let mut stack = Vec::new();

    let mut page = self.cache.get_page(self.root.unwrap())?; // root always exists at this point
    while !page.is_leaf() {
      // Search for the pointer to the next page
      let (exists, i) = search(&page, &key);
      // Find the next page to load
      let next_id = if exists { get_pointer(&page, i + 1) } else { get_pointer(&page, i) };
      // Push onto stack the current page and index to trace back
      stack.push((page.id(), i));
      // Return the page to the cache
      self.cache.put_page(page)?;
      // Load the page from the cache, could be a leaf
      page = self.cache.get_page(next_id)?;
    }

    // Insert directly into the page
    insert_key_value(&mut page, key, value);

    // We have space in the page, return.
    if page.len() < self.max_allowed_keys() {
      return self.cache.put_page(page);
    }

    // Page is full, we need to split it.

    // Allocate a new leaf page
    let mut right_page = self.cache.alloc_page(PageType::Leaf, self.page_size)?;

    // Find split point and prepare split key, left id and right id for internal nodes
    let split_i = (page.len() >> 1) + 1; // split point
    let mut split_key = get_key(&page, split_i).to_vec(); // split key to propagate to the parent
    let mut left_id = page.id();
    let mut right_id = right_page.id();

    // Move half of the keys into the new page and return the split point
    split(&mut page, &mut right_page, split_i);

    // Return both pages into the cache
    self.cache.put_page(right_page)?;
    self.cache.put_page(page)?;

    // Now we need to split parent stack
    while let Some((parent_id, split_i)) = stack.pop() {
      let mut parent = self.cache.get_page(parent_id)?;
      // Page can fit all of the values, we do not need to check the subsequent parents
      insert_internal(&mut parent, split_i, &split_key, left_id, right_id);

      if parent.len() < self.max_allowed_keys() {
        return self.cache.put_page(parent);
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

    // Once we have reached this point, it means root is full and we need to grow the tree.

    let mut new_root = self.cache.alloc_page(PageType::Internal, self.page_size)?;
    insert_internal(&mut new_root, 0, &split_key, left_id, right_id);
    // Update the root pointer
    self.root = Some(new_root.id());
    // Return the page into the cache
    self.cache.put_page(new_root)
  }
}

fn search(_page: &Page, _key: &[u8]) -> (bool, usize) {
  unimplemented!()
}

fn get_key(_page: &Page, _i: usize) -> &[u8] {
  unimplemented!()
}

fn get_pointer(_page: &Page, _i: usize) -> PageID {
  unimplemented!()
}

fn split(_from: &mut Page, _to: &mut Page, _i: usize) {
  unimplemented!()
}

fn insert_key_value(_page: &mut Page, _key: &[u8], _value: &[u8]) {
  unimplemented!()
}

fn insert_internal(_page: &mut Page, _i: usize, _key: &[u8], _left_id: PageID, _right_id: PageID) {
  unimplemented!()
}

fn split_internal(_from: &mut Page, _to: &mut Page, _i: usize) {
  unimplemented!()
}
