/*

Page size is 4KB, 8KB, 16KB, 32KB, 64KB.
Page keys are integer, long, float, double, byte array.

0           1          4         8           12          16              20            22               24
+-----------+----------+---------+-----------+-----------+---------------+-------------+----------------+
| page type | reserved | page id | prev page | next page | overflow page | tuple count | free space ptr |
+-----------+----------+---------+-----------+-----------+---------------+-------------+----------------+
+-------------------------------+-------------------------------+---------------------------------------+
| slot 1 (2) | slot 2 (2) | ... | free space                    | key x value | key x value | ...       |
+-------------------------------+-------------------------------+---------------------------------------+
                                                 free space ptr ^

Page id always starts with 1. If page id is 0, it is treated as undefined.

Slot offset is 0 based, i.e. from the beginning of the page.
Slots are represented as u16 values encoded as bytes (little endian).

Keys and values are stored together (i.e. their binary representations are concatenated).

Fixed type is stored as bytes, e.g. 4 bytes for integer, 8 bytes for long.

Variable type (non-overflow) is stored as 2 bytes size + bytes.

Variable type (overflow) is stored as overflow bit + overflow page id + overflow page offset +
  4 bytes size + partial bytes (payload_size).

0           1               5                9
+-----------+---------------+----------------+
| page type | overflow page | free space ptr |
+-----------+---------------+----------------+
+--------------------------------------------+
| payload 1 | payload 2 | payload 3 | ...    |
+--------------------------------------------+

Overflow payload format:
- 2 bytes size + bytes
- overflow bit + overflow page id + overflow page offset + 2 bytes size + partial bytes

Given the page size and data type, we will calculate how many values we can store.
*/

const HEADER_SIZE: usize = 24;
const SLOT_SIZE: usize = 2;

#[derive(Copy, Clone, Debug)]
pub enum PageType {
  Internal,
  Leaf,
}

pub struct Page {
  page_type: PageType,
  page_id: u32,
  prev_page_id: Option<u32>,
  next_page_id: Option<u32>,
  overflow_page_id: Option<u32>,
  tuple_count: u16,
  free_space_ptr: u16,
  page_bytes: Vec<u8>, // full page data
}

impl Page {
  // Creates a new leaf page.
  pub fn new_leaf_page(
    page_size: usize,
    page_id: u32,
    prev_page_id: Option<u32>,
    next_page_id: Option<u32>
  ) -> Self {
    new_page(PageType::Leaf, page_size, page_id, prev_page_id, next_page_id)
  }

  // Creates a new internal page.
  pub fn new_internal_page(page_size: usize, page_id: u32) -> Self {
    new_page(PageType::Internal, page_size, page_id, None, None)
  }

  pub fn from(page_bytes: Vec<u8>) -> Self {
    unimplemented!()
  }

  pub fn into(self) -> Vec<u8> {
    unimplemented!()
  }

  // Page type.
  pub fn page_type(&self) -> PageType {
    self.page_type
  }

  // Unique page id.
  pub fn page_id(&self) -> u32 {
    self.page_id
  }

  // Page id of the previous page if this page is a leaf.
  pub fn prev_page_id(&self) -> Option<u32> {
    self.prev_page_id
  }

  // Page id of the next page if this page is a leaf.
  pub fn next_page_id(&self) -> Option<u32> {
    self.next_page_id
  }

  // Optional overflow page id.
  pub fn overflow_page_id(&self) -> Option<u32> {
    self.overflow_page_id
  }

  // Number of cells (key-value pairs) in this page.
  pub fn tuple_count(&self) -> u16 {
    self.tuple_count
  }

  // Pointer to the free space chunk where we can write data.
  pub fn free_space_ptr(&self) -> u16 {
    self.free_space_ptr
  }

  // The amount of free space in the page.
  pub fn free_space(&self) -> usize {
    self.free_space_ptr as usize + 1 - HEADER_SIZE - self.tuple_count as usize * SLOT_SIZE
  }

  // Page size in bytes, either 4KB, 8KB, 16KB, 32KB, 64KB.
  pub fn size(&self) -> usize {
    self.page_bytes.len()
  }

  // Returns reference to page data.
  pub fn page_bytes(&self) -> &[u8] {
    &self.page_bytes
  }

  // Returns mutable reference to page data.
  pub fn page_bytes_mut(&mut self) -> &mut [u8] {
    &mut self.page_bytes
  }
}

#[inline]
fn new_page(
  page_type: PageType,
  page_size: usize,
  page_id: u32,
  prev_page_id: Option<u32>,
  next_page_id: Option<u32>
) -> Page {
  assert!(
    page_size == 4 * 1024 ||
    page_size == 8 * 1024 ||
    page_size == 16 * 1024 ||
    page_size == 32 * 1024 ||
    page_size == 64 * 1024
  );
  assert!(page_id > 0);
  prev_page_id.map(|id| assert!(id > 0));
  next_page_id.map(|id| assert!(id > 0));

  Page {
    page_type: page_type,
    page_id: page_id,
    prev_page_id: prev_page_id,
    next_page_id: next_page_id,
    overflow_page_id: None,
    tuple_count: 0,
    free_space_ptr: (page_size - 1) as u16,
    page_bytes: vec![0; page_size],
  }
}
