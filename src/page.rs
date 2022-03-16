use std::io::Write;
use crate::storage::{INVALID_PAGE_ID, StorageManager};

// Max page header size (in bytes).
const PAGE_HEADER_SIZE: usize = 20;
// Minimal number of slots per page (mostly for leaf pages).
const PAGE_MIN_SLOTS: usize = 4;
// Max prefix size allowed for the key (in bytes).
const PAGE_MAX_PREFIX_SIZE: usize = 32;

const FLAG_PAGE_IS_LEAF: u32 = 0x1;
const FLAG_PAGE_IS_OVERFLOW: u32 = 0x2;
const FLAG_PAGE_IS_INTERNAL: u32 = 0x4;

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
  if flags & FLAG_PAGE_IS_LEAF != 0 {
    PageType::Leaf
  } else if flags & FLAG_PAGE_IS_OVERFLOW != 0 {
    PageType::Overflow
  } else if flags & FLAG_PAGE_IS_INTERNAL != 0 {
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

//==========================
// Shared page functionality
//==========================

// Returns slot for the given position.
#[inline]
fn get_slot(page: &[u8], pos: usize) -> u32 {
  let cnt = num_slots(page);
  assert!(pos < cnt, "Invalid position {}, len {}", pos, cnt);
  let slots = &page[PAGE_HEADER_SIZE..PAGE_HEADER_SIZE + cnt * 4];
  u8_u32!(&slots[pos * 4..pos * 4 + 4])
}

// Sets slot for the given position.
#[inline]
fn set_slot(page: &mut [u8], pos: usize, slot: u32) {
  let cnt = num_slots(page);
  assert!(pos < cnt, "Invalid position {}, len {}", pos, cnt);
  let slots = &mut page[PAGE_HEADER_SIZE..PAGE_HEADER_SIZE + cnt * 4];
  write_u32!(&mut slots[pos * 4..pos * 4 + 4], slot);
}

#[inline]
fn free_space(page: &[u8]) -> usize {
  free_ptr(page) - PAGE_HEADER_SIZE - num_slots(page) * 4 /* slot size */
}

// Returns the maximum number of bytes available for a cell.
// This takes 4 bytes of slot into account.
#[inline]
fn max_cell_len(page: &[u8]) -> usize {
  free_space(page).min((page.len() - PAGE_HEADER_SIZE) / PAGE_MIN_SLOTS)
}

// Returns the prefix length of the key for overflow.
#[inline]
fn key_prefix_len(key: &[u8]) -> usize {
  key.len().min(PAGE_MAX_PREFIX_SIZE)
}

//==========
// Leaf page
//==========

#[inline]
pub fn leaf_init(page: &mut [u8]) {
  set_flags(page, FLAG_PAGE_IS_LEAF);
  set_num_slots(page, 0);
  set_free_ptr(page, page.len());
  set_prev_page(page, INVALID_PAGE_ID);
  set_next_page(page, INVALID_PAGE_ID);
}

// Calculates cell length based on the key and value.
// This does not include slot bytes in the slot array.
#[inline]
fn leaf_cell_len(key: &[u8], val: &[u8]) -> usize {
  4 /* prefix len == key len */ +
  4 /* key len */ +
  4 /* val len */ +
  4 /* overflow page */ +
  key.len() +
  val.len()
}

// Calculates overflow cell length based on the key.
// This does not include slot bytes in the slot array.
#[inline]
fn leaf_cell_overflow_len(key: &[u8]) -> usize {
  4 /* prefix len <= key len */ +
  4 /* key len */ +
  4 /* val len */ +
  4 /* overflow page */ +
  key_prefix_len(key)
}

// Returns the cell's length depending whether or not it is an overflow from the page.
#[inline]
fn leaf_get_cell_len(page: &[u8], off: usize) -> usize {
  let start = off;
  let mut end = start;

  // The fixed part of the page is the same for overflow and non-overflow cells.
  let prefix_len = u8_u32!(&page[end..end + 4]) as usize;
  end += 4;
  let key_len = u8_u32!(&page[end..end + 4]) as usize;
  end += 4;
  let val_len = u8_u32!(&page[end..end + 4]) as usize;
  end += 4;
  let overflow_page = u8_u32!(&page[end..end + 4]);
  end += 4;

  if overflow_page == INVALID_PAGE_ID {
    end += key_len + val_len;
  } else {
    end += prefix_len;
  }

  end - start
}

// Returns the cell's slice.
#[inline]
fn leaf_get_cell(page: &[u8], pos: usize) -> &[u8] {
  let off = get_slot(page, pos) as usize;
  let len = leaf_get_cell_len(page, off);
  &page[off..off + len]
}

// Inserts the cell at the position potentially shifting elements.
#[inline]
fn leaf_ins_cell(page: &mut [u8], pos: usize, buf: &[u8]) {
  assert!(buf.len() <= free_space(&page), "Not enough space to insert the cell");

  // Update the count to reflect insertion.
  let cnt = num_slots(&page) + 1;
  assert!(pos < cnt, "Invalid insertion slot {}", pos);
  set_num_slots(page, cnt);

  // Copy all slots to clear the space for the insertion.
  for i in pos..cnt - 1 {
    let off = get_slot(&page, i);
    set_slot(page, i + 1, off);
  }

  // Write data into the page.
  let mut free_ptr = free_ptr(&page);
  free_ptr -= buf.len();
  write_bytes!(&mut page[free_ptr..free_ptr + buf.len()], buf);

  set_slot(page, pos, free_ptr as u32);
  set_free_ptr(page, free_ptr);
}

// Deletes the cell and rearranges the space.
#[inline]
fn leaf_del_cell(page: &mut [u8], pos: usize) {
  let cnt = num_slots(&page);
  let free_ptr = free_ptr(&page);

  let off = get_slot(&page, pos) as usize;
  let len = leaf_get_cell_len(&page, off);

  // Copy the data to cover the deleted cell.
  page.copy_within(free_ptr..off, free_ptr + len);

  // Update all of the slots that have offset < ptr.
  for i in 0..cnt {
    let curr_off = get_slot(&page, i) as usize;
    if curr_off < off {
      set_slot(page, i, (curr_off + len) as u32);
    }
  }

  // Delete the slot at position `pos`.
  for i in pos + 1..cnt {
    let off = get_slot(&page, i);
    set_slot(page, i - 1, off);
  }

  set_free_ptr(page, free_ptr + len);
  set_num_slots(page, cnt - 1);
}

// Whether or not we can insert key + val pair.
// 1. If key + val fit in the page, insert fully.
// 2. If key + val do not fit in the page, calculate overflow size and check.
#[inline]
pub fn leaf_can_insert(page: &[u8], key: &[u8], val: &[u8]) -> bool {
  let max_cell_len = max_cell_len(page);
  4 /* slot len */ + leaf_cell_len(key, val) <= max_cell_len ||
    4 /* slot len */ + leaf_cell_overflow_len(key) <= max_cell_len
}

pub fn leaf_insert(page: &mut [u8], pos: usize, key: &[u8], val: &[u8], mngr: &mut StorageManager) {
  assert!(pos <= num_slots(&page), "Cannot insert at position {}", pos);

  // Insert the bytes into the page.
  let max_cell_len = max_cell_len(&page);
  let start;
  let mut end;
  if 4 /* slot */ + leaf_cell_len(key, val) <= max_cell_len {
    start = free_ptr(page) - leaf_cell_len(key, val);
    end = start;
    write_u32!(&mut page[end..end + 4], key.len() as u32); // prefix len
    end += 4;
    write_u32!(&mut page[end..end + 4], key.len() as u32); // key len
    end += 4;
    write_u32!(&mut page[end..end + 4], val.len() as u32); // val len
    end += 4;
    write_u32!(&mut page[end..end + 4], INVALID_PAGE_ID); // overflow page
    end += 4;
    write_bytes!(&mut page[end..end + key.len()], key); // key
    end += key.len();
    write_bytes!(&mut page[end..end + val.len()], val); // val
  } else if 4 /* slot len */ + leaf_cell_overflow_len(key) <= max_cell_len {
    let prefix_len = key_prefix_len(key);

    let overflow_page = if prefix_len == key.len() {
      // We only need to write the value as overflow because the key fully fits within the page.
      overflow_write(mngr, val)
    } else {
      // Write both key and value to the overflow pages.
      let mut data = Vec::with_capacity(key.len() + val.len());
      data.extend_from_slice(key);
      data.extend_from_slice(val);
      overflow_write(mngr, &data)
    };

    start = free_ptr(page) - leaf_cell_overflow_len(key);
    end = start;
    write_u32!(&mut page[end..end + 4], prefix_len as u32); // prefix len
    end += 4;
    write_u32!(&mut page[end..end + 4], key.len() as u32); // key len
    end += 4;
    write_u32!(&mut page[end..end + 4], val.len() as u32); // val len
    end += 4;
    write_u32!(&mut page[end..end + 4], overflow_page); // overflow page
    end += 4;
    write_bytes!(&mut page[end..end + prefix_len], &key[..prefix_len]);
  } else {
    panic!("Leaf page: not enough space to insert");
  }

  // Clear the space for position and insert new slot.
  let cnt = num_slots(&page) + 1;
  set_num_slots(page, cnt);

  // Clear the space for position.
  for i in (pos..cnt - 1).rev() {
    let slot = get_slot(&page, i);
    set_slot(page, i + 1, slot);
  }
  // Insert new slot.
  set_slot(page, pos, start as u32);
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
  let overflow_pid = u8_u32!(&buf[12..16]);
  if overflow_pid != INVALID_PAGE_ID {
    overflow_delete(mngr, overflow_pid);
  }
  leaf_del_cell(page, pos);
}

// Returns true if prefix == key.
#[inline]
pub fn leaf_is_full_key(page: &[u8], pos: usize) -> bool {
  let off = get_slot(page, pos) as usize;
  let prefix_len = u8_u32!(&page[off..off + 4]);
  let key_len = u8_u32!(&page[off + 4..off + 8]);
  // If prefix == key, then the full key is written regardless the overflow page.
  prefix_len == key_len
}

pub fn leaf_get_prefix(page: &[u8], pos: usize) -> &[u8] {
  let buf = leaf_get_cell(page, pos);
  let prefix_len = u8_u32!(buf[0..4]) as usize;
  &buf[16..16 + prefix_len]
}

pub fn leaf_get_key(page: &[u8], pos: usize, mngr: &mut StorageManager) -> Vec<u8> {
  let buf = leaf_get_cell(page, pos);
  let prefix_len = u8_u32!(&buf[0..4]) as usize;
  let key_len = u8_u32!(&buf[4..8]) as usize;
  let overflow_pid = u8_u32!(&buf[12..16]);

  if overflow_pid == INVALID_PAGE_ID || prefix_len == key_len {
    (&buf[16..16 + prefix_len]).to_vec()
  } else {
    let mut key = vec![0u8; key_len];
    overflow_read(mngr, overflow_pid, 0, &mut key);
    key
  }
}

pub fn leaf_get_val(page: &[u8], pos: usize, mngr: &mut StorageManager) -> Vec<u8> {
  let buf = leaf_get_cell(page, pos);
  let prefix_len = u8_u32!(&buf[0..4]) as usize;
  let key_len = u8_u32!(&buf[4..8]) as usize;
  let val_len = u8_u32!(&buf[8..12]) as usize;
  let overflow_pid = u8_u32!(&buf[12..16]);

  if overflow_pid == INVALID_PAGE_ID {
    // No overflow, value follows the key.
    (&buf[16 + key_len..16 + key_len + val_len]).to_vec()
  } else {
    let mut val = vec![0u8; val_len];
    let off = if prefix_len == key_len { 0 } else { key_len };
    overflow_read(mngr, overflow_pid, off, &mut val);
    val
  }
}

// Runs binary search on the page's keys.
// Returns position of the match or position where the key is greater than the target and a
// boolean to indicate whether the key exists or not.
pub fn bsearch(page: &[u8], key: &[u8], mngr: &mut StorageManager) -> (usize, bool) {
  let mut start = 0;
  let mut end = num_slots(page);

  match page_type(page) {
    PageType::Leaf => {
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
    },
    PageType::Internal => {
      // "start" would point to the insertion point where keys[start] >= key
      while start < end {
        let pivot = (start + end - 1) >> 1;
        let pkey = internal_get_prefix(page, pivot);
        if key < pkey {
          end = pivot;
        } else if key > pkey {
          start = pivot + 1;
        } else if internal_is_full_key(page, pivot) {
          // At this point, we are done since the keys match fully
          return (pivot, true);
        } else {
          let pkey = internal_get_key(page, pivot, mngr);
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
    },
    PageType::Overflow => {
      panic!("Unsupported page type for bsearch");
    },
  }
}

//==============
// Overflow page
//==============

#[inline]
fn overflow_init(page: &mut [u8]) {
  set_flags(page, FLAG_PAGE_IS_OVERFLOW);
  set_num_slots(page, 0); // it is always 0 for overflow
  set_free_ptr(page, 0); // free ptr for overflow pages does not include the page header
  set_prev_page(page, INVALID_PAGE_ID);
  set_next_page(page, INVALID_PAGE_ID);
}

#[inline]
fn overflow_free_space(page: &[u8]) -> usize {
  page.len() - PAGE_HEADER_SIZE - free_ptr(page)
}

// Writes data into 1 or more overflow pages and returns the starting page id.
// If data does not fit into one overflow page, the chain is created and the root is returned.
#[inline]
fn overflow_write(mngr: &mut StorageManager, buf: &[u8]) -> u32 {
  let free_len = mngr.page_size() - PAGE_HEADER_SIZE;
  let mut page = vec![0u8; mngr.page_size()];
  let mut curr_id = INVALID_PAGE_ID;
  let mut len = buf.len();

  // Write value in page size chunks.
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
fn overflow_read(mngr: &mut StorageManager, mut page_id: u32, mut off: usize, buf: &mut [u8]) {
  let mut page = vec![0u8; mngr.page_size()];
  let mut boff = 0;
  let blen = buf.len();

  while page_id != INVALID_PAGE_ID && boff < blen {
    mngr.read(page_id, &mut page);
    assert_eq!(page_type(&page), PageType::Overflow, "Invalid page type for overflow data");
    let len = free_ptr(&page);
    if off >= len {
      off -= len;
    } else {
      // Offset is within the current page.
      let read_len = (len - off).min(blen - boff);
      write_bytes!(
        &mut buf[boff..boff + read_len],
        &page[PAGE_HEADER_SIZE + off..PAGE_HEADER_SIZE + off + read_len]
      );
      boff += read_len;
      off = 0;
    }
    page_id = next_page(&page);
  }

  assert!(boff == blen, "Could not read requested data: off {}, len {}", boff, blen);
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

//==============
// Internal page
//==============

// Internal page structure is as follows:
// [page header]
// [slot0][slot1][slot2]...
// [ptr1][key0][ptr2][key1][ptr3][key2]...
// [ptr0] - end of the page
// Each key is [ptr][prefix len][key len][overflow page][prefix/key]

#[inline]
pub fn internal_init(page: &mut [u8]) {
  set_flags(page, FLAG_PAGE_IS_INTERNAL);
  set_num_slots(page, 0);
  set_free_ptr(page, page.len() - 4); // the last 4 bytes are for ptr0
  set_prev_page(page, INVALID_PAGE_ID);
  set_next_page(page, INVALID_PAGE_ID);
  // Also, set ptr0 to invalid page
  internal_set_ptr(page, 0, INVALID_PAGE_ID);
}

#[inline]
fn internal_key_len(key: &[u8]) -> usize {
  4 /* ptr */ +
  4 /* prefix len */ +
  4 /* key len */ +
  4 /* overflow pid */ +
  key.len()
}

#[inline]
fn internal_overflow_key_len(key: &[u8]) -> usize {
  4 /* ptr */ +
  4 /* prefix len */ +
  4 /* key len */ +
  4 /* overflow pid */ +
  key_prefix_len(key)
}

// Returns the cell's slice.
#[inline]
fn internal_get_cell(page: &[u8], pos: usize) -> &[u8] {
  let off = get_slot(page, pos) as usize;
  let prefix_len = u8_u32!(&page[off + 4..off + 8]) as usize;
  &page[off..off + 16 + prefix_len]
}

#[inline]
fn internal_del_cell(page: &mut [u8], pos: usize) {
  let cnt = num_slots(&page);
  let free_ptr = free_ptr(&page);

  let off = get_slot(&page, pos) as usize;
  let len = internal_get_cell(&page, pos).len();

  // Copy the data to cover the deleted cell.
  page.copy_within(free_ptr..off, free_ptr + len);

  // Update all of the slots that have offset < ptr.
  for i in 0..cnt {
    let curr_off = get_slot(&page, i) as usize;
    if curr_off < off {
      set_slot(page, i, (curr_off + len) as u32);
    }
  }

  // Delete the slot at position `pos`.
  for i in pos + 1..cnt {
    let off = get_slot(&page, i);
    set_slot(page, i - 1, off);
  }

  set_free_ptr(page, free_ptr + len);
  set_num_slots(page, cnt - 1);
}

#[inline]
pub fn internal_can_insert(page: &[u8], key: &[u8]) -> bool {
  let max_cell_len = max_cell_len(page);
  4 /* slot len */ + internal_key_len(key) <= max_cell_len ||
    4 /* slot len */ + internal_overflow_key_len(key) <= max_cell_len
}

pub fn internal_insert(page: &mut [u8], pos: usize, key: &[u8], mngr: &mut StorageManager) {
  assert!(pos <= num_slots(&page), "Cannot insert at position {}", pos);

  let avail_len = max_cell_len(&page);
  let start;
  let mut end;
  if 4 /* slot len */ + internal_key_len(key) <= avail_len {
    start = free_ptr(page) - internal_key_len(key);
    end = start;
    write_u32!(&mut page[end..end + 4], INVALID_PAGE_ID); // ptr
    end += 4;
    write_u32!(&mut page[end..end + 4], key.len() as u32); // prefix len == key len
    end += 4;
    write_u32!(&mut page[end..end + 4], key.len() as u32); // key len
    end += 4;
    write_u32!(&mut page[end..end + 4], INVALID_PAGE_ID); // overflow pid
    end += 4;
    write_bytes!(&mut page[end..end + key.len()], key);
  } else if 4 /* slot len */ + internal_overflow_key_len(key) <= avail_len {
    let prefix_len = key_prefix_len(key);
    let overflow_page = overflow_write(mngr, key);

    start = free_ptr(page) - internal_overflow_key_len(key);
    end = start;
    write_u32!(&mut page[end..end + 4], INVALID_PAGE_ID); // ptr
    end += 4;
    write_u32!(&mut page[end..end + 4], prefix_len as u32); // prefix len <= key len
    end += 4;
    write_u32!(&mut page[end..end + 4], key.len() as u32); // key len
    end += 4;
    write_u32!(&mut page[end..end + 4], overflow_page); // overflow pid
    end += 4;
    write_bytes!(&mut page[end..end + prefix_len], key);
  } else {
    panic!("Internal page: not enough space to insert");
  }

  // Clear the space for position and insert new slot.
  let cnt = num_slots(&page) + 1;
  set_num_slots(page, cnt);

  // Clear the space for position.
  for i in (pos..cnt - 1).rev() {
    let slot = get_slot(&page, i);
    set_slot(page, i + 1, slot);
  }
  // Insert new slot.
  set_slot(page, pos, start as u32);
  set_free_ptr(page, start);
}

pub fn internal_delete(page: &mut [u8], pos: usize, mngr: &mut StorageManager) {
  let buf = internal_get_cell(page, pos);
  let overflow_pid = u8_u32!(&buf[12..16]);
  if overflow_pid != INVALID_PAGE_ID {
    overflow_delete(mngr, overflow_pid);
  }
  internal_del_cell(page, pos);
}

#[inline]
pub fn internal_is_full_key(page: &[u8], pos: usize) -> bool {
  let off = get_slot(page, pos) as usize;
  let prefix_len = u8_u32!(&page[off + 4..off + 8]);
  let key_len = u8_u32!(&page[off + 8..off + 12]);
  // If prefix == key, then the full key is written regardless the overflow page.
  prefix_len == key_len
}

pub fn internal_get_prefix(page: &[u8], pos: usize) -> &[u8] {
  let buf = internal_get_cell(page, pos);
  let prefix_len = u8_u32!(&buf[4..8]) as usize;
  &buf[16..16 + prefix_len]
}

pub fn internal_get_key(page: &[u8], pos: usize, mngr: &mut StorageManager) -> Vec<u8> {
  let buf = internal_get_cell(page, pos);
  let prefix_len = u8_u32!(&buf[4..8]) as usize;
  let key_len = u8_u32!(&buf[8..12]) as usize;
  let overflow_pid = u8_u32!(&buf[12..16]);

  if overflow_pid == INVALID_PAGE_ID || prefix_len == key_len {
    (&buf[16..16 + prefix_len]).to_vec()
  } else {
    let mut key = vec![0u8; key_len];
    overflow_read(mngr, overflow_pid, 0, &mut key);
    key
  }
}

pub fn internal_set_ptr(page: &mut [u8], pos: usize, pid: u32) {
  // Position 0 is a special position, we store the page id for it at the end of the page.
  if pos == 0 {
    let len = page.len();
    write_u32!(&mut page[len - 4..len], pid);
  } else {
    let off = get_slot(&page, pos - 1) as usize; // ptrN is in slot N-1
    write_u32!(&mut page[off..off + 4], pid);
  }
}

pub fn internal_get_ptr(page: &[u8], pos: usize) -> u32 {
  // Position 0 is a special position, we store the page id for it at the end of the page.
  if pos == 0 {
    let len = page.len();
    u8_u32!(&page[len - 4..len])
  } else {
    let off = get_slot(&page, pos - 1) as usize; // ptrN is in slot N-1
    u8_u32!(&page[off..off + 4])
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
    PageType::Leaf | PageType::Internal => {
      println!("  free space left: {}", free_space(page));
    },
    PageType::Overflow => {
      println!("  free space left: {}", overflow_free_space(page));
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
        println!("  Buf: {:?}...", &page[..PAGE_HEADER_SIZE + max_print_len]);
      } else {
        println!("  Buf: {:?}", &page[..PAGE_HEADER_SIZE + free_ptr]);
      }
    },
    PageType::Leaf => {
      for i in 0..num_slots {
        let buf = leaf_get_cell(page, i);
        let prefix_len = u8_u32!(&buf[0..4]) as usize;
        let key_len = u8_u32!(&buf[4..8]) as usize;
        let val_len = u8_u32!(&buf[8..12]) as usize;
        let overflow_pid = u8_u32!(&buf[12..16]);

        if overflow_pid == INVALID_PAGE_ID {
          let key = &buf[16..16 + key_len];
          let val = &buf[16 + key_len..16 + key_len + val_len];
          println!("  [{}] ({}) {:?} = ({}) {:?}",
            i,
            key_len,
            if key_len > max_print_len { &key[..max_print_len] } else { &key[..key_len] },
            val_len,
            if val_len > max_print_len { &val[..max_print_len] } else { &val[..val_len] },
          );
        } else {
          // It is an overflow key.
          let prefix = &buf[16..16 + prefix_len];
          println!(
            "  [{}] ({}) {:?} = overflow (k: {}, v: {}, pid: {})",
            i,
            prefix_len,
            if prefix_len > max_print_len {
              &prefix[..max_print_len]
            } else {
              &prefix[..prefix_len]
            },
            key_len,
            val_len,
            overflow_pid
          );
        }
      }
    },
    PageType::Internal => {
      for i in 0..num_slots + 1 {
        if i > 0 {
          let buf = internal_get_cell(page, i - 1);
          let prefix_len = u8_u32!(&buf[4..8]) as usize;
          let key_len = u8_u32!(&buf[8..12]) as usize;
          let overflow_pid = u8_u32!(&buf[12..16]);

          if overflow_pid == INVALID_PAGE_ID {
            println!(
              "    [{}] ({}) {:?}",
              i - 1,
              key_len,
              &buf[16..16 + key_len]
            );
          } else {
            println!(
              "    [{}] ({}) {:?}",
              i - 1,
              prefix_len,
              if prefix_len > max_print_len {
                &buf[16..16 + max_print_len]
              } else {
                &buf[16..16 + prefix_len]
              }
            );
          }
        }
        let ptri = match internal_get_ptr(&page, i) {
          INVALID_PAGE_ID => "INVALID".to_owned(),
          other => format!("{}", other),
        };
        println!("  * ptr {} = {}", i, ptri);
      }
    }
  }
  println!();
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_page_overflow_write_read() {
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(32).build();

    let max_size = mngr.page_size() * 3;
    for i in 0..max_size {
      let data = vec![6u8; i];
      let len = data.len();
      let page_id = overflow_write(&mut mngr, &data);

      let mut expected = vec![0u8; len];

      for off in 0..len {
        overflow_read(&mut mngr, page_id, off, &mut expected[..len - off]);
        assert_eq!(&expected[..len - off], &data[off..]);
      }
    }
  }

  #[test]
  fn test_page_leaf_equal_cell_length() {
    // The fixed part of the cell must have the same length for non-overflow and overflow
    // so the replacement can fit.
    assert_eq!(leaf_cell_len(&[], &[]), leaf_cell_overflow_len(&[]));
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
    assert_eq!(free_ptr(&page), 136);

    for _ in 0..4 {
      leaf_delete(&mut page, 0, &mut mngr);
    }

    assert_eq!(num_slots(&page), 0);
    assert_eq!(free_ptr(&page), mngr.page_size());
  }

  #[test]
  fn test_page_leaf_insert_overflow() {
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    let mut page = vec![0u8; mngr.page_size()];
    leaf_init(&mut page);

    // Insert small key and small value.
    leaf_insert(&mut page, 0, &[1; 1], &[10; 1], &mut mngr);

    assert_eq!(num_slots(&page), 1);
    let buf = leaf_get_cell(&page, 0);
    assert_eq!(u8_u32!(&buf[12..16]), INVALID_PAGE_ID); // no overflow
    assert_eq!(&leaf_get_key(&page, 0, &mut mngr), &[1; 1]);
    assert_eq!(&leaf_get_val(&page, 0, &mut mngr), &[10; 1]);

    // Insert small key and large value.
    leaf_insert(&mut page, 1, &[2; 1], &[20; 128], &mut mngr);

    assert_eq!(num_slots(&page), 2);
    let buf = leaf_get_cell(&page, 1);
    assert_ne!(u8_u32!(&buf[12..16]), INVALID_PAGE_ID); // overflow
    assert_eq!(&leaf_get_key(&page, 1, &mut mngr), &[2; 1]);
    assert_eq!(&leaf_get_val(&page, 1, &mut mngr), &[20; 128]);

    // Insert large key and large value.
    leaf_insert(&mut page, 2, &[3; 128], &[30; 128], &mut mngr);

    assert_eq!(num_slots(&page), 3);
    let buf = leaf_get_cell(&page, 2);
    assert_ne!(u8_u32!(&buf[12..16]), INVALID_PAGE_ID); // overflow
    assert_eq!(&leaf_get_key(&page, 2, &mut mngr), &[3; 128]);
    assert_eq!(&leaf_get_val(&page, 2, &mut mngr), &[30; 128]);
  }

  #[test]
  fn test_page_insert_reverse_order() {
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(512).build();

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
      assert_eq!(leaf_get_val(&page, i, &mut mngr), val);
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

    assert_eq!(leaf_get_val(&page, 0, &mut mngr), vec![10, 10, 10]);
    assert_eq!(leaf_get_val(&page, 1, &mut mngr), vec![20; 10000]);
    assert_eq!(leaf_get_val(&page, 2, &mut mngr), vec![30; 10]);
    assert_eq!(leaf_get_val(&page, 3, &mut mngr), vec![40]);
  }

  #[test]
  fn test_page_leaf_update_same_key() {
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(128).build();
    let mut page = vec![0u8; mngr.page_size()];
    leaf_init(&mut page);

    for i in 0..4 {
      let key = vec![i as u8; 1];
      let val = vec![i as u8; 2];
      leaf_insert(&mut page, i, &key, &val, &mut mngr);
    }

    let key = vec![1; 1]; // key must be the same
    let val = vec![111; 128]; // value causes an overflow

    leaf_delete(&mut page, 1, &mut mngr);
    leaf_insert(&mut page, 1, &key, &val, &mut mngr);

    // Assert that the cell is an overflow cell.
    let buf = leaf_get_cell(&page, 1);
    let overflow_pid = u8_u32!(&buf[12..16]);
    assert!(overflow_pid != INVALID_PAGE_ID);

    assert_eq!(num_slots(&page), 4);
    assert_eq!(leaf_get_key(&page, 1, &mut mngr), key);
    assert_eq!(leaf_get_val(&page, 1, &mut mngr), val);
  }

  #[test]
  fn test_page_leaf_update_extreme() {
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(128).build();
    let mut page = vec![0u8; mngr.page_size()];
    leaf_init(&mut page);

    for i in 0..5 {
      leaf_insert(&mut page, i, &[], &[], &mut mngr);
    }

    // At this point, only this many bytes is left which is less than what overflow cell needs.
    let free_space_left = free_space(&page);
    assert_eq!(free_space_left, 8);

    leaf_delete(&mut page, 0, &mut mngr);
    leaf_insert(&mut page, 0, &[], &vec![2u8; 8], &mut mngr);

    assert_eq!(free_space(&page), free_space_left);
    assert_eq!(leaf_get_val(&page, 0, &mut mngr), vec![2u8; 8]);

    leaf_delete(&mut page, 0, &mut mngr);
    leaf_insert(&mut page, 0, &[], &vec![2u8; 128], &mut mngr);

    assert_eq!(free_space(&page), free_space_left);
    assert_eq!(leaf_get_val(&page, 0, &mut mngr), vec![2u8; 128]);
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

    let mut right = vec![0u8; mngr.page_size()];
    leaf_init(&mut right);
    leaf_split(&mut page, &mut right, 2);

    assert_eq!(num_slots(&page), 2);
    assert_eq!(num_slots(&right), 3);
    assert_eq!(&leaf_get_key(&page, 0, &mut mngr), &[1; 3]);
    assert_eq!(&leaf_get_key(&page, 1, &mut mngr), &[2; 3]);
    assert_eq!(&leaf_get_key(&right, 0, &mut mngr), &[3; 3]);
    assert_eq!(&leaf_get_key(&right, 1, &mut mngr), &[4; 3]);
    assert_eq!(&leaf_get_key(&right, 2, &mut mngr), &[5; 3]);
  }

  #[test]
  fn test_page_internal_init() {
    let mut page = vec![0u8; 128];
    internal_init(&mut page);

    assert_eq!(num_slots(&page), 0);
    assert_eq!(free_ptr(&page), 124);
    assert_eq!(internal_get_ptr(&page, 0), INVALID_PAGE_ID);
  }

  #[test]
  fn test_page_internal_insert() {
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();
    let mut page = vec![0u8; mngr.page_size()];
    internal_init(&mut page);

    internal_insert(&mut page, 0, &[1, 2, 3], &mut mngr);

    assert_eq!(num_slots(&page), 1);
    assert_eq!(internal_get_prefix(&page, 0), &[1, 2, 3]);
    assert_eq!(internal_get_key(&page, 0, &mut mngr), vec![1, 2, 3]);
  }

  #[test]
  fn test_page_internal_insert_overflow() {
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();
    let mut page = vec![0u8; mngr.page_size()];
    internal_init(&mut page);

    internal_insert(&mut page, 0, &[1, 2, 3], &mut mngr);
    internal_insert(&mut page, 1, &[4; 128], &mut mngr);

    assert_eq!(num_slots(&page), 2);

    assert_eq!(internal_get_prefix(&page, 0), &[1, 2, 3]);
    assert_eq!(internal_get_key(&page, 0, &mut mngr), vec![1, 2, 3]);

    assert_eq!(internal_get_prefix(&page, 1), &[4; PAGE_MAX_PREFIX_SIZE]);
    assert_eq!(internal_get_key(&page, 1, &mut mngr), vec![4; 128]);
  }

  #[test]
  fn test_page_internal_delete() {
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();
    let mut page = vec![0u8; mngr.page_size()];
    internal_init(&mut page);

    internal_insert(&mut page, 0, &[1; 128], &mut mngr);
    internal_insert(&mut page, 1, &[2; 128], &mut mngr);
    internal_insert(&mut page, 2, &[3; 128], &mut mngr);
    internal_insert(&mut page, 3, &[4; 128], &mut mngr);
    internal_insert(&mut page, 4, &[5; 4], &mut mngr);

    assert_eq!(free_space(&page), 0);
    assert_eq!(num_slots(&page), 5);

    for i in 0..5 {
      internal_delete(&mut page, 0, &mut mngr);
      assert_eq!(num_slots(&page), 4 - i);
    }

    assert_eq!(num_slots(&page), 0);
    assert_eq!(free_ptr(&page), page.len() - 4);
  }
}
