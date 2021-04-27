use crate::error::Res;

/// Page id alias.
pub type PageID = u32;

const PAGE_HEADER_SIZE: usize = 24;
const EMPTY_PAGE_ID: PageID = u32::max_value();

/// Page type.
/// Add new page types for index pages.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum PageType {
  Leaf,
  Internal,
}

impl PageType {
  fn from(tpe: u8) -> Self {
    match tpe {
      0 => PageType::Leaf,
      1 => PageType::Internal,
      _ => panic!("Invalid page type {}", tpe),
    }
  }

  fn into(self) -> u8 {
    match self {
      PageType::Leaf => 0,
      PageType::Internal => 1,
    }
  }
}

/// Returns a valid page id if page id is set, otherwise None.
fn read_page_id(buf: &[u8], pos: &mut usize) -> Option<PageID> {
  let id = u32::from_le_bytes([buf[*pos], buf[*pos + 1], buf[*pos + 2], buf[*pos + 3]]);
  *pos += 4;
  if id == EMPTY_PAGE_ID { None } else { Some(id) }
}

/// Writes a page id into the provided buffer.
fn write_page_id(id: Option<PageID>, buf: &mut [u8], pos: &mut usize) {
  let id = match id {
    Some(value) => value,
    None => EMPTY_PAGE_ID,
  };

  let bytes = id.to_le_bytes();
  buf[*pos] = bytes[0];
  buf[*pos + 1] = bytes[1];
  buf[*pos + 2] = bytes[2];
  buf[*pos + 3] = bytes[3];
  *pos += 4;
}

/// Page is a fundamental unit of data in memory and on disk.
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
  /// Creates a new in-memory page.
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

  /// Reads page from a provided vector of bytes.
  pub fn from(data: Vec<u8>) -> Self {
    assert!(data.len() >= PAGE_HEADER_SIZE);

    let mut ptr = 0;
    // 1. Page type
    let page_type = PageType::from(data[ptr]);
    ptr += 1;
    // 2. Reserved bytes
    ptr += 3;
    // 3. Page id
    let page_id = read_page_id(&data, &mut ptr).expect(&format!("Page id was not set"));
    // 4. Prev page
    let prev = read_page_id(&data, &mut ptr);
    // 5. Next page
    let next = read_page_id(&data, &mut ptr);
    // 6. Overflow page
    let overflow = read_page_id(&data, &mut ptr);
    // 7. Tuple count
    let count = u16::from_le_bytes([data[ptr], data[ptr + 1]]);
    ptr += 2;
    // 8. Free space ptr
    let free_space_ptr = u16::from_le_bytes([data[ptr], data[ptr + 1]]);
    ptr += 2;

    assert_eq!(ptr, PAGE_HEADER_SIZE);

    Self::new(page_type, page_id, prev, next, overflow, count, free_space_ptr, data, false)
  }

  /// Writes all page data into a vector of bytes.
  pub fn into(mut self) -> Vec<u8> {
    let mut ptr = 0;
    // 1. Page type
    self.data[ptr] = self.page_type.into();
    ptr += 1;
    // 2. Reserved bytes
    ptr += 3;
    // 3. Page id
    write_page_id(Some(self.page_id), &mut self.data, &mut ptr);
    // 4. Prev page
    write_page_id(self.prev, &mut self.data, &mut ptr);
    // 5. Next page
    write_page_id(self.next, &mut self.data, &mut ptr);
    // 6. Overflow page
    write_page_id(self.overflow, &mut self.data, &mut ptr);
    // 7. Tuple count
    let count_bytes = self.count.to_le_bytes();
    self.data[ptr] = count_bytes[0];
    self.data[ptr + 1] = count_bytes[1];
    ptr += 2;
    // 8. Free space ptr
    let free_space_ptr_bytes = self.free_space_ptr.to_le_bytes();
    self.data[ptr] = free_space_ptr_bytes[0];
    self.data[ptr + 1] = free_space_ptr_bytes[1];
    ptr += 2;

    assert_eq!(ptr, PAGE_HEADER_SIZE);

    self.data
  }

  /// Creates a new empty page with id for testing.
  pub fn empty(page_id: PageID) -> Self {
    Self::new(PageType::Leaf, page_id, None, None, None, 0, 0, vec![0; PAGE_HEADER_SIZE], false)
  }

  /// Returns page id.
  pub fn id(&self) -> PageID {
    self.page_id
  }
}

/// Page manager that maintains pages on disk or in memory.
pub trait PageManager {
  /// Creates new page and returns the page or a copy.
  fn alloc_page(&mut self) -> Res<Page>;
  /// Returns a copy of the page for the page id.
  fn read_page(&mut self, page_id: PageID) -> Res<Page>;
  /// Updates the page.
  fn write_page(&mut self, page: Page) -> Res<()>;
  /// Deletes the page for the page id.
  fn free_page(&mut self, page_id: PageID) -> Res<()>;
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_page_type_conversion() {
    assert_eq!(PageType::from(0), PageType::Leaf);
    assert_eq!(PageType::from(1), PageType::Internal);
    assert_eq!(PageType::Leaf, PageType::from(PageType::Leaf.into()));
    assert_eq!(PageType::Internal, PageType::from(PageType::Internal.into()));
  }

  #[test]
  fn test_page_conversion_empty_buf() {
    let page = Page::from(vec![0; 32]);
    assert_eq!(page.into(), vec![0; 32]);
  }

  #[test]
  fn test_page_conversion() {
    for &is_dirty in &[true, false] {
      let data = vec![0; 32];
      let page1 = Page::new(PageType::Internal, 1, Some(2), Some(3), None, 10, 11, data, is_dirty);
      let page2 = Page::from(page1.clone().into());
      assert_eq!(page1.page_type, page2.page_type);
      assert_eq!(page1.page_id, page2.page_id);
      assert_eq!(page1.prev, page2.prev);
      assert_eq!(page1.next, page2.next);
      assert_eq!(page1.overflow, page2.overflow);
      assert_eq!(page1.count, page2.count);
      assert_eq!(page1.free_space_ptr, page2.free_space_ptr);
    }
  }
}
