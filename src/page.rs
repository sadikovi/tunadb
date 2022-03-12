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
const FLAG_IS_KEY_OVERFLOW_2: u8 = 0x1;

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

// Returns the maximum number of bytes available for a cell.
// This takes 4 bytes of slot into account.
#[inline]
fn leaf_max_cell_len(page: &[u8]) -> usize {
  leaf_free_space(page).min((page.len() - PAGE_HEADER_SIZE) / PAGE_MIN_SLOTS)
}

// Calculates cell length based on the key and value.
// This does not include slot bytes in the slot array.
#[inline]
fn leaf_cell_len(key: &[u8], val: &[u8]) -> usize {
  1 /* flags */ +
  4 /* key len */ + key.len() +
  4 /* val len */ + val.len()
}

// Returns the prefix length of the key for overflow.
#[inline]
fn leaf_prefix_len(key: &[u8]) -> usize {
  key.len().min(PAGE_MAX_PREFIX_SIZE)
}

// Calculates overflow cell length based on the key.
// This does not include slot bytes in the slot array.
#[inline]
fn leaf_cell_overflow_len(key: &[u8]) -> usize {
  1 /* flags */ +
  4 /* prefix len */ + leaf_prefix_len(key) +
  4 /* key len */ +
  4 /* val len */ +
  4 /* overflow page */
}

// Returns slot for the given position.
#[inline]
fn leaf_get_slot(page: &[u8], pos: usize) -> u32 {
  let cnt = num_slots(page);
  assert!(pos < cnt, "Invalid position {}, len {}", pos, cnt);
  let slots = &page[PAGE_HEADER_SIZE..PAGE_HEADER_SIZE + cnt * 4];
  u8_u32!(&slots[pos * 4..pos * 4 + 4])
}

#[inline]
fn leaf_set_slot(page: &mut [u8], pos: usize, slot: u32) {
  let cnt = num_slots(page);
  assert!(pos < cnt, "Invalid position {}, len {}", pos, cnt);
  let slots = &mut page[PAGE_HEADER_SIZE..PAGE_HEADER_SIZE + cnt * 4];
  write_u32!(&mut slots[pos * 4..pos * 4 + 4], slot);
}

// Returns the cell's length depending whether or not it is an overflow from the page.
#[inline]
fn leaf_get_cell_len(page: &[u8], off: usize) -> usize {
  let start = off;
  let mut end = start;

  // The first byte is always flags.
  let flags = page[end];
  end += 1;

  if flags & FLAG_IS_KEY_OVERFLOW_2 == 0 {
    let key_len = u8_u32!(&page[end..end + 4]) as usize;
    end += 4;
    end += key_len;
    let val_len = u8_u32!(&page[end..end + 4]) as usize;
    end += 4;
    end += val_len;
  } else {
    let prefix_len = u8_u32!(&page[end..end + 4]) as usize;
    end += 4; // prefix length
    end += prefix_len;
    end += 4; // key length
    end += 4; // val length
    end += 4; // overflow page
  }

  end - start
}

// // Returns the cell's slice.
#[inline]
fn leaf_get_cell(page: &[u8], pos: usize) -> &[u8] {
  let off = leaf_get_slot(page, pos) as usize;
  let len = leaf_get_cell_len(page, off);
  &page[off..off + len]
}

// Inserts the cell at the position potentially shifting elements.
#[inline]
fn leaf_ins_cell(page: &mut [u8], pos: usize, buf: &[u8]) {
  assert!(buf.len() <= leaf_free_space(&page), "Not enough space to insert the cell");

  // Update the count to reflect insertion.
  let cnt = num_slots(&page) + 1;
  assert!(pos < cnt, "Invalid insertion slot {}", pos);
  set_num_slots(page, cnt);

  // Copy all slots to clear the space for the insertion.
  for i in pos..cnt - 1 {
    let off = leaf_get_slot(&page, i);
    leaf_set_slot(page, i + 1, off);
  }

  // Write data into the page.
  let mut free_ptr = free_ptr(&page);
  free_ptr -= buf.len();
  write_bytes!(&mut page[free_ptr..free_ptr + buf.len()], buf);

  leaf_set_slot(page, pos, free_ptr as u32);
  set_free_ptr(page, free_ptr);
}

// Deletes the cell and rearranges the space.
#[inline]
fn leaf_del_cell(page: &mut [u8], pos: usize) {
  let cnt = num_slots(&page);
  let free_ptr = free_ptr(&page);

  let off = leaf_get_slot(&page, pos) as usize;
  let len = leaf_get_cell_len(&page, off);

  // Copy the data to cover the deleted cell.
  page.copy_within(free_ptr..off, free_ptr + len);

  // Update all of the slots that have offset < ptr.
  for i in 0..cnt {
    let curr_off = leaf_get_slot(&page, i) as usize;
    if curr_off < off {
      leaf_set_slot(page, i, (curr_off + len) as u32);
    }
  }

  // Delete the slot at position `pos`.
  for i in pos + 1..cnt {
    let off = leaf_get_slot(&page, i);
    leaf_set_slot(page, i - 1, off);
  }

  set_free_ptr(page, free_ptr + len);
  set_num_slots(page, cnt - 1);
}

// Whether or not we can insert key + val pair.
// 1. If key + val fit in the page, insert fully.
// 2. If key + val do not fit in the page, calculate overflow size and check.
#[inline]
pub fn leaf_can_insert(page: &[u8], key: &[u8], val: &[u8]) -> bool {
  let max_cell_len = leaf_max_cell_len(page);
  leaf_cell_len(key, val) <= max_cell_len || leaf_cell_overflow_len(key) <= max_cell_len
}

pub fn leaf_insert(page: &mut [u8], pos: usize, key: &[u8], val: &[u8], mngr: &mut StorageManager) {
  assert!(pos <= num_slots(&page), "Cannot insert at position {}", pos);

  // Insert the bytes into the page.
  let max_cell_len = leaf_max_cell_len(&page);
  let start;
  let mut end;
  if 4 /* slot */ + leaf_cell_len(key, val) <= max_cell_len {
    start = free_ptr(page) - leaf_cell_len(key, val);
    end = start;
    page[end] = 0; // no flags
    end += 1;
    write_u32!(&mut page[end..end + 4], key.len() as u32);
    end += 4;
    write_bytes!(&mut page[end..end + key.len()], key);
    end += key.len();
    write_u32!(&mut page[end..end + 4], val.len() as u32);
    end += 4;
    write_bytes!(&mut page[end..end + val.len()], val);
  } else if 4 /* slot len */ + leaf_cell_overflow_len(key) <= max_cell_len {
    let overflow_page = overflow_write(mngr, key, val);
    let prefix_len = leaf_prefix_len(key);
    start = free_ptr(page) - leaf_cell_overflow_len(key);
    end = start;
    page[end] = FLAG_IS_KEY_OVERFLOW_2; // overflow flag
    end += 1;
    write_u32!(&mut page[end..end + 4], prefix_len as u32);
    end += 4;
    write_bytes!(&mut page[end..end + prefix_len], &key[..prefix_len]);
    end += prefix_len;
    write_u32!(&mut page[end..end + 4], key.len() as u32);
    end += 4;
    write_u32!(&mut page[end..end + 4], val.len() as u32);
    end += 4;
    write_u32!(&mut page[end..end + 4], overflow_page);
  } else {
    panic!("Not enough space to insert");
  }

  // Clear the space for position and insert new slot.
  let cnt = num_slots(&page) + 1;
  set_num_slots(page, cnt);

  // Clear the space for position.
  for i in (pos..cnt - 1).rev() {
    let slot = leaf_get_slot(&page, i);
    leaf_set_slot(page, i + 1, slot);
  }
  // Insert new slot.
  leaf_set_slot(page, pos, start as u32);
  set_free_ptr(page, start);
}

// Moves keys and values based on the provided position.
// All values after the position are moved to the right page.
pub fn leaf_split(left: &mut [u8], right: &mut [u8], pos: usize) {
  assert_eq!(num_slots(&right), 0, "Right page is not empty");

  let cnt = num_slots(&left);
  let mut j = 0;

  // Insert cells into the right page starting from `pos`.
  for i in pos..cnt {
    let buf = leaf_get_cell(&left, i);
    leaf_ins_cell(right, j, buf);
    j += 1;
  }

  // Delete all of the cells after `pos`.
  for i in (pos..cnt).rev() {
    leaf_del_cell(left, i);
  }
}

pub fn leaf_delete(page: &mut [u8], pos: usize, mngr: &mut StorageManager) {
  let buf = leaf_get_cell(&page, pos);
  let flags = buf[0];

  if flags & FLAG_IS_KEY_OVERFLOW_2 != 0 {
    // Get overflow page.
    let len = buf.len();
    let overflow_pid = u8_u32!(buf[len - 4..len]);
    overflow_delete(mngr, overflow_pid);
  }
  leaf_del_cell(page, pos);
}

// Returns true if prefix == key.
#[inline]
pub fn leaf_is_full_key(page: &[u8], pos: usize) -> bool {
  let buf = leaf_get_cell(page, pos);
  buf[0] & FLAG_IS_KEY_OVERFLOW_2 == 0
}

pub fn leaf_get_prefix(page: &[u8], pos: usize) -> &[u8] {
  let buf = leaf_get_cell(page, pos);
  let off = 1; // account for flags
  let prefix_len = u8_u32!(buf[off..off + 4]) as usize;
  &buf[off + 4..off + 4 + prefix_len]
}

pub fn leaf_get_key(page: &[u8], pos: usize, mngr: &mut StorageManager) -> Vec<u8> {
  let buf = leaf_get_cell(page, pos);
  let flags = buf[0];
  let off = 1;
  let len = u8_u32!(buf[off..off + 4]) as usize;

  if flags & FLAG_IS_KEY_OVERFLOW_2 == 0 {
    // There is no overflow.
    (&buf[off + 4..off + 4 + len]).to_vec()
  } else {
    // We need to figure out if the key fits within the page.
    let key_len = u8_u32!(&buf[off + 4 + len..off + 4 + len + 4]) as usize;
    if len == key_len {
      // The key is the same as prefix and fits within the page, return as is.
      (&buf[off + 4..off + 4 + len]).to_vec()
    } else {
      let mut key = vec![0u8; key_len];
      let overflow_page = u8_u32!(&buf[off + 4 + len + 8..off + 4 + len + 8 + 4]);
      overflow_read(mngr, overflow_page, 0, &mut key);
      key
    }
  }
}

pub fn leaf_get_value(page: &[u8], pos: usize, mngr: &mut StorageManager) -> Vec<u8> {
  let buf = leaf_get_cell(page, pos);
  let flags = buf[0];
  let mut off = 1;
  let len = u8_u32!(buf[off..off + 4]) as usize;

  if flags & FLAG_IS_KEY_OVERFLOW_2 == 0 {
    // There is no overflow.
    off += 4;
    off += len;
    let val_len = u8_u32!(&buf[off..off + 4]) as usize;
    off += 4;
    (&buf[off..off + val_len]).to_vec()
  } else {
    // We need to figure out if the key fits within the page.
    off += 4;
    off += len;
    let key_len = u8_u32!(&buf[off..off + 4]) as usize;
    off += 4;
    let val_len = u8_u32!(&buf[off..off + 4]) as usize;
    off += 4;
    let overflow_page = u8_u32!(&buf[off..off + 4]);
    let mut val = vec![0u8; val_len];
    overflow_read(mngr, overflow_page, key_len, &mut val);
    val
  }
}

pub fn bsearch(page: &[u8], key: &[u8], mngr: &mut StorageManager) -> (usize, bool) {
  assert_eq!(page_type(page), PageType::Leaf, "Invalid page type for bsearch");
  let mut start = 0;
  let mut end = num_slots(page);
  // "start" would point to the insertion point where keys[start] >= key
  while start < end {
    let pivot = (start + end - 1) >> 1;
    let pkey = leaf_get_prefix(page, pivot);
    if key < pkey {
      end = pivot;
    } else if key > pkey {
      start = pivot + 1;
    } else if leaf_is_full_key(page, pivot) {
      // At this point, we are done since the keys match fully
      return (pivot, true);
    } else {
      let pkey = leaf_get_key(page, pivot, mngr);
      if key < &pkey {
        end = pivot;
      } else if key > &pkey {
        start = pivot + 1;
      } else {
        return (pivot, true);
      }
    }
  }
  (start, false)
}

#[inline]
fn overflow_init(page: &mut [u8]) {
  set_flags(page, FLAG_IS_OVERFLOW);
  set_num_slots(page, 0); // it is always 0 for overflow
  set_free_ptr(page, 0); // free ptr for overflow pages does not include the page header
  set_prev_page(page, INVALID_PAGE_ID);
  set_next_page(page, INVALID_PAGE_ID);
}

#[inline]
fn overflow_free_space(page: &[u8]) -> usize {
  page.len() - PAGE_HEADER_SIZE - free_ptr(page)
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
fn overflow_read(mngr: &mut StorageManager, mut page_id: u32, mut start: usize, buf: &mut [u8]) {
  let mut page = vec![0u8; mngr.page_size()];
  let mut off = 0;
  let len = buf.len();

  while off < len && page_id != INVALID_PAGE_ID {
    mngr.read(page_id, &mut page);
    assert_eq!(page_type(&page), PageType::Overflow, "Invalid page type for overflow data");
    let ptr = free_ptr(&page);
    if ptr > start {
      let page_off = PAGE_HEADER_SIZE + start;
      let read_len = (ptr - start).min(len - off);
      write_bytes!(&mut buf[off..off + read_len], &page[page_off..page_off + read_len]);
      off += read_len;
      start = 0;
    } else {
      start -= ptr;
    }
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

pub fn debug(pid: u32, page: &[u8]) {
  let max_print_len = 16;

  let page_type = page_type(page);
  let num_slots = num_slots(page);
  let prev_page = prev_page(page);
  let next_page = next_page(page);
  println!("=============");
  println!("PAGE {}", pid);
  println!("=============");
  println!("Page Header:");
  println!("  page type: {:?}", page_type);
  println!("  num slots: {}", num_slots);
  println!("  free ptr: {}", free_ptr(page));
  match page_type {
    PageType::Leaf => {
      println!("  free space left: {}", leaf_free_space(page));
    },
    PageType::Overflow => {
      println!("  free space left: {}", overflow_free_space(page));
    },
    _ => {
      println!("  ! Unsupported");
    },
  }
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
      let free_ptr = free_ptr(page);
      println!("  Bytes written: {}", free_ptr);
      println!(
        "  Percentage: {0:.1$}%",
        free_ptr as f64 * 100f64 / (page.len() - PAGE_HEADER_SIZE) as f64,
        2
      );
      if free_ptr > max_print_len {
        println!("  Buf: {:?}...", &page[..max_print_len]);
      } else {
        println!("  Buf: {:?}", &page[..free_ptr]);
      }
    },
    PageType::Leaf => {
      for i in 0..num_slots {
        let buf = leaf_get_cell(page, i);
        let flags = buf[0];
        let mut off = 1;
        if flags & FLAG_IS_KEY_OVERFLOW_2 == 0 {
          let key_len = u8_u32!(&buf[off..off + 4]) as usize;
          off += 4;
          let key = &buf[off..off + key_len];
          off += key_len;
          let val_len = u8_u32!(&buf[off..off + 4]) as usize;
          off += 4;
          let val = &buf[off..off + val_len];
          println!("  [{}] ({}) {:?} = ({}) {:?}",
            i,
            key_len,
            if key_len > max_print_len { &key[..max_print_len] } else { &key[..key_len] },
            val_len,
            if val_len > max_print_len { &val[..max_print_len] } else { &val[..val_len] },
          );
        } else {
          // It is an overflow key.
          let prefix_len = u8_u32!(&buf[off..off + 4]) as usize;
          off += 4;
          let prefix = &buf[off..off + prefix_len];
          off += prefix_len;
          let key_len = u8_u32!(&buf[off..off + 4]);
          off += 4;
          let val_len = u8_u32!(&buf[off..off + 4]);
          off += 4;
          let overflow_page = u8_u32!(&buf[off..off + 4]);
          println!(
            "  [{}] ({}) {:?} = overflow {{ key len {}, val len {}, page {} }}",
            i,
            prefix_len,
            if prefix_len > max_print_len {
              &prefix[..max_print_len]
            } else {
              &prefix[..prefix_len]
            },
            key_len,
            val_len,
            overflow_page
          );
        }
      }
    },
    _ => {
      println!("  ! Unsupported");
    }
  }
  println!();
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_page_overflow_write_read() {
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(128).build();

    let max_size = mngr.page_size() * 10;
    for i in 0..max_size {
      let key = vec![6u8; i];
      let val = vec![7u8; max_size - i];

      let page_id = overflow_write(&mut mngr, &key, &val);

      let mut expected = vec![0u8; key.len() + val.len()];
      overflow_read(&mut mngr, page_id, 0, &mut expected);

      assert_eq!(&expected[..key.len()], &key);
      assert_eq!(&expected[key.len()..key.len() + val.len()], &val);
    }
  }

  #[test]
  fn test_page_leaf_insert_delete() {
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    let mut page = vec![0u8; mngr.page_size()];
    leaf_init(&mut page);

    for i in 0..3 {
      let k = vec![(i + 1) as u8; 7];
      let v = vec![(i + 1) as u8 * 10; 10];
      if leaf_can_insert(&page, &k, &v) {
        leaf_insert(&mut page, i, &k, &v, &mut mngr);
      }
    }
    leaf_insert(&mut page, 3, &[9, 9], &[9, 9, 9], &mut mngr);

    assert_eq!(num_slots(&page), 4);
    assert_eq!(free_ptr(&page), 164);

    for _ in 0..4 {
      leaf_delete(&mut page, 0, &mut mngr);
    }

    assert_eq!(num_slots(&page), 0);
    assert_eq!(free_ptr(&page), mngr.page_size());

    mngr.write_next(&page);
  }

  #[test]
  fn test_page_insert_reverse_order() {
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    let mut page = vec![0u8; mngr.page_size()];
    leaf_init(&mut page);

    for i in 0..10 {
      let key = vec![i as u8; i];
      let val = vec![i as u8; i];
      leaf_insert(&mut page, 0, &key, &val, &mut mngr);
    }

    for i in 0..10 {
      let key = vec![(9 - i) as u8; 9 - i];
      let val = vec![(9 - i) as u8; 9 - i];
      assert_eq!(leaf_get_key(&page, i, &mut mngr), key);
      assert_eq!(leaf_get_value(&page, i, &mut mngr), val);
    }
  }

  #[test]
  fn test_page_leaf_insert_get_overflow() {
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(4096).build();
    let mut page = vec![0u8; mngr.page_size()];
    leaf_init(&mut page);

    leaf_insert(&mut page, 0, &[1, 1, 1], &[10, 10, 10], &mut mngr);
    leaf_insert(&mut page, 1, &vec![2; 100], &vec![20; 10000], &mut mngr);
    leaf_insert(&mut page, 2, &[3], &vec![30; 10], &mut mngr);
    leaf_insert(&mut page, 3, &vec![4; 10000], &vec![40], &mut mngr);

    assert_eq!(leaf_get_prefix(&page, 0), &[1, 1, 1]);
    assert_eq!(leaf_get_prefix(&page, 1), &vec![2; PAGE_MAX_PREFIX_SIZE]);
    assert_eq!(leaf_get_prefix(&page, 2), &[3]);
    assert_eq!(leaf_get_prefix(&page, 3), &vec![4; PAGE_MAX_PREFIX_SIZE]);

    assert_eq!(leaf_get_key(&page, 0, &mut mngr), vec![1, 1, 1]);
    assert_eq!(leaf_get_key(&page, 1, &mut mngr), vec![2; 100]);
    assert_eq!(leaf_get_key(&page, 2, &mut mngr), vec![3; 1]);
    assert_eq!(leaf_get_key(&page, 3, &mut mngr), vec![4; 10000]);

    assert_eq!(leaf_get_value(&page, 0, &mut mngr), vec![10, 10, 10]);
    assert_eq!(leaf_get_value(&page, 1, &mut mngr), vec![20; 10000]);
    assert_eq!(leaf_get_value(&page, 2, &mut mngr), vec![30; 10]);
    assert_eq!(leaf_get_value(&page, 3, &mut mngr), vec![40]);
  }

  #[test]
  fn test_page_leaf_split() {
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();
    let mut page = vec![0u8; mngr.page_size()];
    leaf_init(&mut page);

    leaf_insert(&mut page, 0, &[1; 3], &[10; 10], &mut mngr);
    leaf_insert(&mut page, 1, &[2; 3], &[20; 10], &mut mngr);
    leaf_insert(&mut page, 2, &[3; 3], &[30; 10], &mut mngr);
    leaf_insert(&mut page, 3, &[4; 3], &[40; 128], &mut mngr);
    leaf_insert(&mut page, 4, &[5; 3], &[50; 128], &mut mngr);

    debug(100, &page);

    let mut right = vec![0u8; mngr.page_size()];
    leaf_init(&mut right);

    leaf_split(&mut page, &mut right, 0);

    debug(200, &page);
    debug(300, &right);

    assert!(false, "OK");
  }
}
