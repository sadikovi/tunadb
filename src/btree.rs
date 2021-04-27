use crate::cache::PageCache;
use crate::error::Res;
use crate::page::PageID;

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

  // Searches for the provided key and returns value if the key exists.
  pub fn find(&mut self, key: &[u8]) -> Res<Option<&[u8]>> {
    unimplemented!()
  }

  // Inserts key and value and returns the previous value for the key if exists.
  pub fn insert(&mut self, key: &[u8], value: &[u8]) -> Res<Option<&[u8]>> {
    unimplemented!()
  }

  // Deletes the key and returns the previous value for the key.
  pub fn delete(&mut self, key: &[u8]) -> Res<Option<&[u8]>> {
    unimplemented!()
  }
}
