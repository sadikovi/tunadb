//! Module for page definition.
use std::collections::HashMap;
use std::sync::RwLock;
use crate::error::Res;

type PageID = u32;

pub struct Page {
  id: PageID,
}

/// Page manager that maintains pages on disk or in memory
pub trait PageManager {
  fn alloc_page(&mut self) -> Res<Page>;
  fn read_page(&mut self, page_id: PageID) -> Res<Page>;
  fn write_page(&mut self, page: &Page) -> Res<()>;
  fn free_page(&mut self, page_id: PageID) -> Res<()>;
}

// pub struct PageCache<'a> {
//   capacity: usize,
//   cache: HashMap<PageID, RwLock<Page>>,
//   page_mngr: &'a mut dyn PageManager,
// }
//
// impl<'a> PageCache<'a> {
//   pub fn new() -> Self {
//     unimplemented!()
//   }
// }
//
// struct LFU {
//   // Heap to maintain LFU policy
//   heap: Vec<(usize, PageID)>,
// }
//
// impl LFU {
//   pub fn new(capacity: usize) -> Self {
//     Self { heap: Vec::with_capacity(capacity) }
//   }
//
//   pub fn
// }
