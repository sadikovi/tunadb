use std::io::Write;
use crate::storage::{INVALID_PAGE_ID, StorageManager};

// Max page header size (in bytes).
const PAGE_HEADER_SIZE: usize = 20;
// Minimal number of slots per page (mostly for leaf pages).
const PAGE_MIN_SLOTS: usize = 4;
// Max prefix size allowed for the key (in bytes).
const PAGE_MAX_PREFIX_SIZE: usize = 64;

const FLAG_IS_LEAF: u32 = 0x1;
const FLAG_IS_OVERFLOW: u32 = 0x2;
const FLAG_IS_INTERNAL: u32 = 0x4;
const FLAG_IS_KEY_OVERFLOW: u32 = 0x80000000;

//============
// Page header
//============

// Page header:
// - flags (4 bytes)
// - num slots (4 bytes)
// - free ptr (4 bytes)
// - prev page (4 bytes)
// - next page (4 bytes)

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum PageType {
  Leaf,
  Overflow,
  Internal,
}

// Returns page type for the page.
#[inline]
pub fn page_type(page: &[u8]) -> PageType {
  let header = &page[..PAGE_HEADER_SIZE];
  let flags = u8_u32!(&header[..4]);
  if flags & FLAG_IS_LEAF != 0 {
    PageType::Leaf
  } else if flags & FLAG_IS_OVERFLOW != 0 {
    PageType::Overflow
  } else if flags & FLAG_IS_INTERNAL != 0 {
    PageType::Internal
  } else {
    panic!("Invalid page type");
  }
}

#[inline]
pub fn num_slots(page: &[u8]) -> usize {
  let header = &page[..PAGE_HEADER_SIZE];
  u8_u32!(&header[4..8]) as usize
}

#[inline]
fn free_ptr(page: &[u8]) -> usize {
  let header = &page[..PAGE_HEADER_SIZE];
  u8_u32!(&header[8..12]) as usize
}

#[inline]
fn prev_page(page: &[u8]) -> u32 {
  let header = &page[..PAGE_HEADER_SIZE];
  u8_u32!(&header[12..16])
}

#[inline]
fn next_page(page: &[u8]) -> u32 {
  let header = &page[..PAGE_HEADER_SIZE];
  u8_u32!(&header[16..20])
}

#[inline]
fn set_flags(page: &mut [u8], flags: u32) {
  let header = &mut page[..PAGE_HEADER_SIZE];
  write_u32!(&mut header[0..4], flags);
}

#[inline]
fn set_num_slots(page: &mut [u8], value: usize) {
  let header = &mut page[..PAGE_HEADER_SIZE];
  write_u32!(&mut header[4..8], value as u32);
}

#[inline]
fn set_free_ptr(page: &mut [u8], ptr: usize) {
  let header = &mut page[..PAGE_HEADER_SIZE];
  write_u32!(&mut header[8..12], ptr as u32);
}

#[inline]
fn set_prev_page(page: &mut [u8], page_id: u32) {
  let header = &mut page[..PAGE_HEADER_SIZE];
  write_u32!(&mut header[12..16], page_id);
}

#[inline]
fn set_next_page(page: &mut [u8], page_id: u32) {
  let header = &mut page[..PAGE_HEADER_SIZE];
  write_u32!(&mut header[16..20], page_id);
}

//==========
// Leaf page
//==========

#[inline]
pub fn leaf_init(page: &mut [u8]) {
  set_flags(page, FLAG_IS_LEAF);
  set_num_slots(page, 0);
  set_free_ptr(page, page.len());
  set_prev_page(page, INVALID_PAGE_ID);
  set_next_page(page, INVALID_PAGE_ID);
}

#[inline]
fn leaf_free_space(page: &[u8]) -> usize {
  free_ptr(page) - PAGE_HEADER_SIZE - num_slots(page) * 4 /* slot size */
}

// Whether or not we can insert key + val pair.
// 1. If key + val fit in the page, insert fully.
// 2. If key + val do not fit in the page, calculate overflow size and check.
#[inline]
pub fn leaf_can_insert(page: &[u8], key: &[u8], val: &[u8]) -> bool {
  let target_len = 4 /* slot */ + 4 /* key len */ + key.len() + 4 /* val len */ + val.len();
  let overflow_len = 4 /* slot */ + 4 /* prefix len */ + key.len().min(PAGE_MAX_PREFIX_SIZE) +
    4 /* key len */ + 4 /* val len */ + 4 /* overflow page */;
  // Allowed max cell size.
  let max_cell_len = leaf_free_space(page).min((page.len() - PAGE_HEADER_SIZE) / PAGE_MIN_SLOTS);
  target_len <= max_cell_len || overflow_len <= max_cell_len
}

#[inline]
pub fn leaf_insert(page: &mut [u8], pos: usize, key: &[u8], val: &[u8], mngr: &mut StorageManager) {
  let num_slots = num_slots(&page);
  assert!(pos <= num_slots, "Invalid position {}, len {}", pos, num_slots);

  let max_cell_len = leaf_free_space(page).min((page.len() - PAGE_HEADER_SIZE) / PAGE_MIN_SLOTS);
  let cell_len = 4 /* key len */ + key.len() + 4 /* val len */ + val.len();
  let prefix_len = key.len().min(PAGE_MAX_PREFIX_SIZE);
  let overflow_len = 4 /* prefix len */ + prefix_len + 4 /* key len */ + 4 /* val len */ + 4 /* overflow page */;

  let mut ptr = free_ptr(page) - cell_len;
  let mut key_flags = 0;
  if 4 /* slot len */ + cell_len <= max_cell_len {
    let mut off = ptr;
    write_u32!(&mut page[off..off + 4], key.len() as u32);
    off += 4;
    write_bytes!(&mut page[off..off + key.len()], key);
    off += key.len();
    write_u32!(&mut page[off..off + 4], val.len() as u32);
    off += 4;
    write_bytes!(&mut page[off..off + val.len()], val);
  } else if 4 /* slot len */ + overflow_len <= max_cell_len {
    let overflow_page = overflow_write(mngr, key, val);
    ptr = free_ptr(page) - overflow_len;
    key_flags |= FLAG_IS_KEY_OVERFLOW;
    let mut off = ptr;
    write_u32!(&mut page[off..off + 4], prefix_len as u32);
    off += 4;
    write_bytes!(&mut page[off..off + prefix_len], &key[..prefix_len]);
    off += prefix_len;
    write_u32!(&mut page[off..off + 4], key.len() as u32);
    off += 4;
    write_u32!(&mut page[off..off + 4], val.len() as u32);
    off += 4;
    write_u32!(&mut page[off..off + 4], overflow_page);
  } else {
    panic!("Not enough space to insert");
  }

  let slot_arr = &mut page[PAGE_HEADER_SIZE..PAGE_HEADER_SIZE + (num_slots + 1) * 4];
  for i in (pos..num_slots).rev() {
    let off = i * 4;
    let curr = u8_u32!(slot_arr[off..off + 4]);
    write_u32!(&mut slot_arr[off + 4..off + 8], curr);
  }
  write_u32!(&mut slot_arr[pos * 4..pos * 4 + 4], key_flags | ptr as u32);

  set_num_slots(page, num_slots + 1);
  set_free_ptr(page, ptr);
}

#[inline]
pub fn leaf_delete(page: &mut [u8], pos: usize, mngr: &mut StorageManager) {
  let num_slots = num_slots(&page);
  assert!(pos < num_slots, "Invalid position {}, len {}", pos, num_slots);

  let free_ptr = free_ptr(&page);
  let slot_arr = &page[PAGE_HEADER_SIZE..PAGE_HEADER_SIZE + num_slots * 4];
  let ptr = u8_u32!(&slot_arr[pos * 4..pos * 4 + 4]);

  let is_overflow = ptr & FLAG_IS_KEY_OVERFLOW != 0;
  let start = (ptr & !FLAG_IS_KEY_OVERFLOW) as usize;
  let mut end = start;

  if !is_overflow {
    let key_len = u8_u32!(&page[end..end + 4]) as usize;
    end += 4;
    end += key_len;
    let val_len = u8_u32!(&page[end..end + 4]) as usize;
    end += 4;
    end += val_len;
  } else {
    let prefix_len = u8_u32!(&page[end..end + 4]) as usize;
    end += 4;
    end += prefix_len;
    end += 4; // key length
    end += 4; // val length
    let overflow_page = u8_u32!(&page[end..end + 4]);
    end += 4;
    overflow_delete(mngr, overflow_page);
  }

  let len = end - start;
  page.copy_within(free_ptr..start, free_ptr + len);

  // Update all of the slots that have offset < ptr.
  let slot_arr = &mut page[PAGE_HEADER_SIZE..PAGE_HEADER_SIZE + num_slots * 4];
  for i in 0..num_slots {
    let curr_ptr = u8_u32!(&slot_arr[i * 4..i * 4 + 4]);
    if curr_ptr < ptr {
      write_u32!(&mut slot_arr[i * 4..i * 4 + 4], curr_ptr + len as u32);
    }
  }
  // Delete the slot at position `pos`.
  for i in pos + 1..num_slots {
    let off = i * 4;
    let curr = u8_u32!(slot_arr[off..off + 4]);
    write_u32!(&mut slot_arr[off - 4..off], curr);
  }

  set_free_ptr(page, free_ptr + len);
  set_num_slots(page, num_slots - 1);
}

#[inline]
fn overflow_init(page: &mut [u8]) {
  set_flags(page, FLAG_IS_OVERFLOW);
  set_num_slots(page, 0); // it is always 0 for overflow
  set_free_ptr(page, 0); // free ptr for overflow pages starts at the beginning of the page
  set_prev_page(page, INVALID_PAGE_ID);
  set_next_page(page, INVALID_PAGE_ID);
}

#[inline]
fn overflow_write(mngr: &mut StorageManager, key: &[u8], val: &[u8]) -> u32 {
  let free_len = mngr.page_size() - PAGE_HEADER_SIZE;
  let mut curr_id = INVALID_PAGE_ID;
  let mut page = vec![0u8; mngr.page_size()];

  // Start with the value.
  let mut buf = val;
  let mut len = val.len();

  // Write value in page size chunks.
  while len >= free_len {
    overflow_init(&mut page);
    write_bytes!(&mut page[PAGE_HEADER_SIZE..], &buf[len - free_len..len]);
    set_next_page(&mut page, curr_id);
    set_free_ptr(&mut page, free_len);
    curr_id = mngr.write_next(&page);
    len -= free_len;
  }

  // Check if there are any remaining bytes from the value.
  // If there are any, firstly, pad with the key and then write the rest of the value.
  let mut left = 0;
  if len > 0 {
    left = (free_len - len).min(key.len());
    overflow_init(&mut page);
    write_bytes!(&mut page[PAGE_HEADER_SIZE..], &key[key.len() - left..key.len()]);
    write_bytes!(&mut page[PAGE_HEADER_SIZE + left..], &buf[0..len]);
    set_next_page(&mut page, curr_id);
    set_free_ptr(&mut page, left + len);
    curr_id = mngr.write_next(&page);
  }

  buf = key;
  len = key.len() - left;

  while len > 0 {
    overflow_init(&mut page);
    let min_len = free_len.min(len);
    write_bytes!(&mut page[PAGE_HEADER_SIZE..], &buf[len - min_len..len]);
    set_next_page(&mut page, curr_id);
    set_free_ptr(&mut page, min_len);
    curr_id = mngr.write_next(&page);
    len -= min_len;
  }

  curr_id
}

#[inline]
fn overflow_read(mngr: &mut StorageManager, mut page_id: u32, buf: &mut [u8]) {
  let mut page = vec![0u8; mngr.page_size()];
  let mut off = 0;
  let len = buf.len();

  while off < len && page_id != INVALID_PAGE_ID {
    mngr.read(page_id, &mut page);
    assert_eq!(page_type(&page), PageType::Overflow, "Invalid page type for overflow data");
    let read_len = free_ptr(&page).min(len - off);
    write_bytes!(&mut buf[off..off + read_len], &page[PAGE_HEADER_SIZE..PAGE_HEADER_SIZE + read_len]);
    off += read_len;
    page_id = next_page(&page);
  }
  assert!(off == len, "Could not read requested data: off {}, len {}", off, len);
}

#[inline]
fn overflow_delete(mngr: &mut StorageManager, mut page_id: u32) {
  let mut page = vec![0u8; mngr.page_size()];
  while page_id != INVALID_PAGE_ID {
    mngr.read(page_id, &mut page);
    assert_eq!(page_type(&page), PageType::Overflow, "Invalid page type for overflow data");
    mngr.mark_as_free(page_id);
    page_id = next_page(&page);
  }
}

pub fn debug(page: &[u8]) {
  let page_type = page_type(page);
  let num_slots = num_slots(page);
  let prev_page = prev_page(page);
  let next_page = next_page(page);
  println!("Page Header:");
  println!("  page type: {:?}", page_type);
  println!("  num slots: {}", num_slots);
  println!("  free ptr: {}", free_ptr(page));
  if prev_page == INVALID_PAGE_ID {
    println!("  prev page: N/A");
  } else {
    println!("  prev page: {}", prev_page);
  }
  if next_page == INVALID_PAGE_ID {
    println!("  next page: N/A");
  } else {
    println!("  next page: {}", next_page);
  }
  println!("Page Body:");
  match page_type {
    PageType::Overflow => {
      println!("  Bytes written: {}", free_ptr(page));
      println!(
        "  Percentage: {0:.1$}%",
        free_ptr(page) as f64 * 100f64 / (page.len() - PAGE_HEADER_SIZE) as f64,
        2
      );
      println!("  Buf: {:?}", page);
    },
    PageType::Leaf => {
      let slot_arr = &page[PAGE_HEADER_SIZE..PAGE_HEADER_SIZE + num_slots * 4];
      for i in 0..num_slots {
        let ptr = u8_u32!(&slot_arr[i * 4..i * 4 + 4]);
        let mut off = (ptr & !FLAG_IS_KEY_OVERFLOW) as usize;
        if ptr & FLAG_IS_KEY_OVERFLOW == 0 {
          let key_len = u8_u32!(&page[off..off + 4]) as usize;
          off += 4;
          let key = &page[off..off + key_len];
          off += key_len;
          let val_len = u8_u32!(&page[off..off + 4]) as usize;
          off += 4;
          let val = &page[off..off + val_len];
          println!("  [{}] ({}) {:?} = ({}) {:?}", i, key_len, key, val_len, val);
        } else {
          // It is an overflow key.
          let prefix_len = u8_u32!(&page[off..off + 4]) as usize;
          off += 4;
          let prefix = &page[off..off + prefix_len];
          off += prefix_len;
          let key_len = u8_u32!(&page[off..off + 4]);
          off += 4;
          let val_len = u8_u32!(&page[off..off + 4]);
          off += 4;
          let overflow_page = u8_u32!(&page[off..off + 4]);
          println!(
            "  [{}] ({}) {:?} = (k {}, v {}) page {}",
            i, prefix_len, prefix, key_len, val_len, overflow_page
          );
        }
      }
    },
    _ => {
      println!("  Unsupported");
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::storage::Options;

  #[test]
  fn test_page_overflow_write_read() {
    let page_size = 128;
    let opts = Options::new().as_mem(0).with_page_size(page_size).build();
    let mut mngr = StorageManager::new(&opts);

    let max_size = (page_size * 10) as usize;
    for i in 0..max_size {
      let key = vec![6u8; i];
      let val = vec![7u8; max_size - i];

      let page_id = overflow_write(&mut mngr, &key, &val);

      let mut expected = vec![0u8; key.len() + val.len()];
      overflow_read(&mut mngr, page_id, &mut expected);

      assert_eq!(&expected[..key.len()], &key);
      assert_eq!(&expected[key.len()..key.len() + val.len()], &val);
    }
  }

  #[test]
  fn test_page_leaf_insert() {
    let page_size = 128;
    let opts = Options::new().as_mem(0).with_page_size(page_size).build();
    let mut mngr = StorageManager::new(&opts);

    let mut page = vec![0u8; page_size as usize];
    leaf_init(&mut page);

    for i in 0..3 {
      let k = vec![(i + 1) as u8; 7];
      let v = vec![(i + 1) as u8 * 10; 10];
      if leaf_can_insert(&page, &k, &v) {
        leaf_insert(&mut page, i, &k, &v, &mut mngr);
      }
    }
    leaf_insert(&mut page, 3, &[9, 9], &[9, 9, 9], &mut mngr);

    for _ in 0..4 {
      leaf_delete(&mut page, 0, &mut mngr);
    }

    mngr.write_next(&page);

    for page_id in 0..mngr.num_pages() as u32 {
      if mngr.is_accessible(page_id) {
        mngr.read(page_id, &mut page);
        debug(&page);
      }
    }

    assert!(false, "OK");
  }
}
