use crate::error::Res;

// Page id alias.
pub type PageID = u32;

// Page type.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum PageType {
  Leaf,
  Internal,
}

impl From<u8> for PageType {
  fn from(tpe: u8) -> Self {
    match tpe {
      0 => PageType::Leaf,
      1 => PageType::Internal,
      _ => panic!("Invalid page type {}", tpe),
    }
  }
}

impl From<PageType> for u8 {
  fn from(page_type: PageType) -> Self {
    match page_type {
      PageType::Leaf => 0,
      PageType::Internal => 1,
    }
  }
}

// Page is a fundamental unit of data in memory and on disk.
#[derive(Clone, Debug, PartialEq)]
pub struct Page {
  // Page header
  page_type: PageType,
  page_id: PageID,
  prev: Option<PageID>,
  next: Option<PageID>,
  overflow: Option<PageID>,
  count: u16,
  free_space_ptr: u16,
  // Data
  data: Vec<u8>,
  // In-memory flags
  pub is_dirty: bool,
}

impl Page {
  // Creates a new in-memory page.
  pub fn new(
    page_type: PageType,
    page_id: PageID,
    prev: Option<PageID>,
    next: Option<PageID>,
    overflow: Option<PageID>,
    count: u16,
    free_space_ptr: u16,
    data: Vec<u8>,
    is_dirty: bool,
  ) -> Self {
    Self { page_type, page_id, prev, next, overflow, count, free_space_ptr, data, is_dirty }
  }

  // Creates a new empty page with id and page size.
  pub fn empty(page_type: PageType, page_id: PageID, page_size: usize) -> Self {
    Self::new(page_type, page_id, None, None, None, 0, 0, vec![0; page_size], false)
  }

  // Returns true if the page is leaf.
  pub fn is_leaf(&self) -> bool {
    self.page_type == PageType::Leaf
  }

  // Returns page id.
  pub fn id(&self) -> PageID {
    self.page_id
  }

  // Returns number of tuples in the page.
  pub fn len(&self) -> usize {
    self.count as usize
  }
}

// Page manager that maintains pages on disk or in memory.
pub trait PageManager {
  // Creates new page and returns the page or a copy.
  fn alloc_page(&mut self, page_type: PageType, page_size: usize) -> Res<Page>;
  // Returns a copy of the page for the page id.
  fn read_page(&mut self, page_id: PageID) -> Res<Page>;
  // Updates the page.
  fn write_page(&mut self, page: Page) -> Res<()>;
  // Deletes the page for the page id.
  fn free_page(&mut self, page_id: PageID) -> Res<()>;
}

#[cfg(test)]
mod tests {
  use super::*;

  const PAGE_SIZE_4KB: usize = 4 * 1024;

  #[test]
  fn test_page_type_conversion() {
    assert_eq!(PageType::from(0), PageType::Leaf);
    assert_eq!(PageType::from(1), PageType::Internal);
    assert_eq!(PageType::from(u8::from(PageType::Leaf)), PageType::Leaf);
    assert_eq!(PageType::from(u8::from(PageType::Internal)), PageType::Internal);
  }

  #[test]
  fn test_page_empty() {
    let page = Page::empty(PageType::Leaf, 1, PAGE_SIZE_4KB);
    assert_eq!(page.page_type, PageType::Leaf);
    assert_eq!(page.page_id, 1);
    assert_eq!(page.prev, None);
    assert_eq!(page.next, None);
    assert_eq!(page.overflow, None);
    assert_eq!(page.count, 0);
    assert_eq!(page.free_space_ptr, 0);
    assert_eq!(page.data.len(), PAGE_SIZE_4KB);
    assert_eq!(page.is_dirty, false);
  }

  #[test]
  fn test_page_new() {
    let data = vec![0; PAGE_SIZE_4KB];
    let page = Page::new(PageType::Internal, 1, Some(2), Some(3), None, 10, 11, data, true);
    assert_eq!(page.page_type, PageType::Internal);
    assert_eq!(page.page_id, 1);
    assert_eq!(page.prev, Some(2));
    assert_eq!(page.next, Some(3));
    assert_eq!(page.overflow, None);
    assert_eq!(page.count, 10);
    assert_eq!(page.free_space_ptr, 11);
    assert_eq!(page.data.len(), PAGE_SIZE_4KB);
    assert_eq!(page.is_dirty, true);
  }
}
