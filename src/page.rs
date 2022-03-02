use std::fmt::{Write as FmtWrite};
use std::io::Write;
use crate::storage::{INVALID_PAGE_ID, StorageManager};

// Max page header size (fixed).
const PAGE_HEADER_SIZE: usize = 16;
// Size of the varlen fixed part.
const VARLEN_SIZE: usize = 16;
// Max size of varlen data before overflow.
const VARLEN_MAX_LEN: usize = VARLEN_SIZE - 4 /* length */;
// Size of the overflow slot (fixed).
const OVERFLOW_SLOT_SIZE: usize = 20;

const FLAG_LEAF_PAGE: u32 = 0x1;
const FLAG_OVERFLOW_PAGE: u32 = 0x2;
const FLAG_INTERNAL_PAGE: u32 = 0x4;

//===============
// Page structure
//===============
// leaf page
// + header (32 bytes):
//   |-- flags (4 bytes)
//   |-- num slots (4 bytes)
//   |-- overflow page (4 bytes)
//   |-- reserved (4 bytes)
// + body (remaining bytes)
//   |-- varlen data (16 bytes)
//     |-- length (4 bytes, no overflow flag is needed)
//     |-- varlen body (1)
//       |-- data (12 bytes)
//     |-- varlen body (2)
//       |-- prefix (4 bytes)
//       |-- overflow page (4 bytes)
//       |-- slot (4 bytes)
//
// overflow page
// + header (16 bytes):
//   |-- flags (4 bytes)
//   |-- num slots (4 bytes)
//   |-- overflow page (4 bytes)
//   |-- used space (4 bytes, counted from the end of the page)
// + body (remaining bytes)
//   |-- slots
//     |-- slot id (4 bytes), unique identifier
//     |-- slot off (4 bytes), absolute location to the beginning of the data
//     |-- slot len (4 bytes), length of the slot
//       |-- overflow flag (1 bit)
//       |-- length up to 2GB (31 bits)
//     |-- slot next page id (4 bytes)
//     |-- slot next slot id (4 bytes)
//   |-- body (length bytes)

// Number of keys that a leaf page can hold.
// Since internal page takes less space for values, it can hold as many keys as a leaf page.
#[inline]
pub fn max_keys(page_size: usize) -> usize {
  (page_size - PAGE_HEADER_SIZE) / (2 /* key + value */ * VARLEN_SIZE)
}

//============
// Page header
//============

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum PageType {
  Leaf,
  Internal,
  Overflow,
}

// Returns page type.
#[inline]
pub fn page_type(page: &[u8]) -> PageType {
  let flags = u8_u32!(&page[0..4]);
  if flags & FLAG_LEAF_PAGE != 0 {
    PageType::Leaf
  } else if flags & FLAG_OVERFLOW_PAGE != 0 {
    PageType::Overflow
  } else {
    PageType::Internal
  }
}

// Returns number of slots in the page.
#[inline]
pub fn num_slots(page: &[u8]) -> usize {
  u8_u32!(&page[4..8]) as usize
}

// Sets number of slots in the page.
#[inline]
pub fn set_num_slots(page: &mut [u8], num_slots: usize) {
  write_u32!(&mut page[4..8], num_slots as u32);
}

// Returns the overflow page stored in the header.
#[inline]
pub fn overflow_page(page: &[u8]) -> u32 {
  u8_u32!(&page[8..12])
}

// Sets overflow page in the header.
#[inline]
pub fn set_overflow_page(page: &mut [u8], page_id: u32) {
  write_u32!(&mut page[8..12], page_id);
}

// Returns used space for the overflow page.
#[inline]
pub fn used_space(page: &[u8]) -> usize {
  assert_eq!(page_type(page), PageType::Overflow);
  u8_u32!(&page[12..16]) as usize
}

// Sets used space for the overflow page.
#[inline]
pub fn set_used_space(page: &mut [u8], value: usize) {
  assert_eq!(page_type(page), PageType::Overflow);
  write_u32!(&mut page[12..16], value as u32);
}

// Free space in bytes in the overflow page.
#[inline]
pub fn free_space(page: &[u8]) -> usize {
  assert_eq!(page_type(page), PageType::Overflow);
  let num_slots = num_slots(page);
  let used_space = used_space(page);
  page.len() - PAGE_HEADER_SIZE - num_slots * OVERFLOW_SLOT_SIZE - used_space
}

// Returns the next largest slot id for insertion into overflow page.
#[inline]
pub fn next_slot_id(page: &[u8]) -> u32 {
  let num_slots = num_slots(page);
  let mut next_slot_id = 0;
  for i in 0..num_slots {
    let ptr = PAGE_HEADER_SIZE + i * OVERFLOW_SLOT_SIZE;
    next_slot_id = next_slot_id.max(u8_u32!(&page[ptr..ptr + 4]));
  }
  next_slot_id + 1
}

// Overflow slot information
#[derive(Clone, Copy, Debug, PartialEq)]
struct Slot {
  pos: usize, // index within slot array
  id: u32, // monotonically increasing slot id
  off: usize, // absolute offset in the page to the beginning of the slot data
  len: usize, // slot data length
  is_overflow: bool, // whether or not the slot is overflow
  next_page: u32, // if overflow, points to the next page
  next_slot: u32, // if overflow, points to the next slot
}

// Returns slot information by position in the slots array.
#[inline]
fn slot_info_by_pos(page: &[u8], pos: usize) -> Slot {
  let ptr = PAGE_HEADER_SIZE + pos * OVERFLOW_SLOT_SIZE;
  Slot {
    pos: pos,
    id: u8_u32!(&page[ptr..ptr + 4]),
    off: u8_u32!(&page[ptr + 4..ptr + 8]) as usize,
    len: (u8_u32!(&page[ptr + 8..ptr + 12]) & !(1 << 31)) as usize,
    is_overflow: u8_u32!(&page[ptr + 8..ptr + 12]) & (1 << 31) != 0,
    next_page: u8_u32!(&page[ptr + 12..ptr + 16]),
    next_slot: u8_u32!(&page[ptr + 16..ptr + 20]),
  }
}

#[inline]
fn slot_info(page: &[u8], slot_id: u32) -> Slot {
  let num_slots = num_slots(page);
  for i in 0..num_slots {
    let ptr = PAGE_HEADER_SIZE + i * OVERFLOW_SLOT_SIZE;
    if slot_id == u8_u32!(&page[ptr..ptr + 4]) {
      return slot_info_by_pos(page, i);
    }
  }
  panic!("Could not locate slot {}", slot_id);
}

#[inline]
pub fn init_overflow_page(page: &mut[u8]) {
  let tmp = &mut page[0..PAGE_HEADER_SIZE];
  write_u32!(&mut tmp[0..4], FLAG_OVERFLOW_PAGE);
  set_num_slots(tmp, 0);
  set_overflow_page(tmp, INVALID_PAGE_ID);
  set_used_space(tmp, 0);
}

#[inline]
pub fn init_leaf_page(page: &mut [u8]) {
  let tmp = &mut page[0..PAGE_HEADER_SIZE];
  write_u32!(&mut tmp[0..4], FLAG_LEAF_PAGE);
  set_num_slots(tmp, 0); // number of keys
  set_overflow_page(tmp, INVALID_PAGE_ID);
  // The last 4 bytes are reserved for leaf page
  write_u32!(&mut tmp[12..16], 0u32);
}

//==================
// Varlen management
//==================

// Writes data into varlen buffer.
// If data does not fit, overflow pages are created.
// Updates the input overflow page if that has changed, e.g. new page was created.
fn set_varlen(buf: &mut [u8], data: &[u8], overflow_page: &mut u32, mngr: &mut StorageManager) {
  assert_eq!(buf.len(), VARLEN_SIZE, "Invalid varlen length: {}", buf.len());
  let len = data.len();
  if len <= VARLEN_MAX_LEN {
    write_u32!(&mut buf[0..4], len as u32);
    write_bytes!(&mut buf[4..4 + len], data);
  } else {
    // We write 4 bytes prefix in this case.
    let remaining = &data[4..];
    let (slot_overflow_page, slot_id) =
      set_varlen_overflow(*overflow_page, remaining, mngr);

    write_u32!(&mut buf[0..4], len as u32);
    write_bytes!(&mut buf[4..8], &data[0..4]);
    write_u32!(&mut buf[8..12], slot_overflow_page);
    write_u32!(&mut buf[12..16], slot_id);

    // Update the overflow page reference.
    // Point overflow page to the first overflow slot page.
    if *overflow_page == INVALID_PAGE_ID {
      *overflow_page = slot_overflow_page;
    }
  }
}

// Writes the remaining data into overflow pages.
// Returns slot overflow page id and slot id in the page.
//
// if the input page_id is INVALID_PAGE_ID, new overflow page is created.
fn set_varlen_overflow(mut page_id: u32, data: &[u8], mngr: &mut StorageManager) -> (u32, u32) {
  let len = data.len();

  if len == 0 {
    return (INVALID_PAGE_ID, 0);
  }

  let page_size = mngr.page_size();
  let mut page = vec![0u8; page_size];

  // If overflow page does not exist, create it.
  if page_id == INVALID_PAGE_ID {
    init_overflow_page(&mut page);
  } else {
    mngr.read(page_id, &mut page);
  }

  let free_len = free_space(&page);
  let num_slots = num_slots(&page);
  let next_slot_id = next_slot_id(&page);
  let slot_ptr = PAGE_HEADER_SIZE + num_slots * OVERFLOW_SLOT_SIZE;
  // Pointer to the free space from the beginning of the page.
  let mut free_ptr = page_size - used_space(&page);

  if free_len >= OVERFLOW_SLOT_SIZE + len {
    // All data fits in the page.
    write_bytes!(&mut page[free_ptr - len..free_ptr], data);
    free_ptr -= len;

    // Write the slot.
    write_u32!(&mut page[slot_ptr..slot_ptr + 4], next_slot_id);
    write_u32!(&mut page[slot_ptr + 4..slot_ptr + 8], free_ptr as u32);
    write_u32!(&mut page[slot_ptr + 8..slot_ptr + 12], len as u32);
    write_u32!(&mut page[slot_ptr + 12..slot_ptr + 16], INVALID_PAGE_ID);
    write_u32!(&mut page[slot_ptr + 16..slot_ptr + 20], 0u32);

    // Update metadata.
    set_num_slots(&mut page, num_slots + 1);
    set_used_space(&mut page, page_size - free_ptr);

    // Write the page.
    if page_id == INVALID_PAGE_ID {
      page_id = mngr.write_next(&page)
    } else {
      mngr.write(page_id, &page);
    }

    (page_id, next_slot_id)
  } else if free_len > OVERFLOW_SLOT_SIZE {
    // Data fits partially.
    let actual_len = (free_len - OVERFLOW_SLOT_SIZE).min(len);
    let next_page_id = overflow_page(&page);
    let (res_page, res_slot) = set_varlen_overflow(next_page_id, &data[actual_len..], mngr);

    // Write as much data as we can.
    write_bytes!(&mut page[free_ptr - actual_len..free_ptr], &data[..actual_len]);
    free_ptr -= actual_len;

    // Write the slot.
    write_u32!(&mut page[slot_ptr..slot_ptr + 4], next_slot_id);
    write_u32!(&mut page[slot_ptr + 4..slot_ptr + 8], free_ptr as u32);
    write_u32!(&mut page[slot_ptr + 8..slot_ptr + 12], actual_len as u32 | (1 << 31));
    write_u32!(&mut page[slot_ptr + 12..slot_ptr + 16], res_page);
    write_u32!(&mut page[slot_ptr + 16..slot_ptr + 20], res_slot);

    // Update metadata.
    set_num_slots(&mut page, num_slots + 1);
    set_used_space(&mut page, page_size - free_ptr);
    if next_page_id == INVALID_PAGE_ID {
      set_overflow_page(&mut page, res_page);
    }

    // Write the page.
    if page_id == INVALID_PAGE_ID {
      page_id = mngr.write_next(&page)
    } else {
      mngr.write(page_id, &page);
    }

    (page_id, next_slot_id)
  } else {
    assert_ne!(page_id, INVALID_PAGE_ID, "Allocated page does not have enough space");
    // Data does not fit, move to the next page.
    let next_page_id = overflow_page(&page);
    let (res_page, res_slot) = set_varlen_overflow(next_page_id, data, mngr);
    if next_page_id == INVALID_PAGE_ID {
      set_overflow_page(&mut page, res_page);
      mngr.write(page_id, &page);
    }
    (res_page, res_slot)
  }
}

// Deletes varlen and overflow data.
fn del_varlen(buf: &[u8], overflow_page: u32, mngr: &mut StorageManager) {
  assert_eq!(buf.len(), VARLEN_SIZE, "Invalid varlen length: {}", buf.len());
  let len = u8_u32!(&buf[0..4]) as usize;

  // If data fits within varlen buffer, we don't need to do anything
  // as there is no overflow data to clean up.
  if len > VARLEN_MAX_LEN {
    let target_page = u8_u32!(&buf[8..12]);
    let target_slot = u8_u32!(&buf[12..16]);
    del_overflow(overflow_page, target_page, target_slot, mngr);
  }
}

// Helper method to recursively delete the remaining overflow data.
fn del_overflow(mut page_id: u32, tpage_id: u32, tslot_id: u32, mngr: &mut StorageManager) -> u32 {
  if page_id == INVALID_PAGE_ID {
    return INVALID_PAGE_ID;
  }

  let page_size = mngr.page_size();
  let mut page = vec![0u8; page_size];

  loop {
    assert_ne!(page_id, INVALID_PAGE_ID, "Invalid overflow page in the chain");
    mngr.read(page_id, &mut page);
    if page_id == tpage_id {
      break;
    }
    page_id = overflow_page(&page);
  }

  // Find the slot to delete.
  let num_slots = num_slots(&page);

  let slot = slot_info(&page, tslot_id);
  let free_ptr = page_size - used_space(&page);

  // Delete blob.
  // | ....... | <-- len --> | ... |
  // ^         ^
  // free_ptr  slot.off
  page.copy_within(free_ptr..slot.off, free_ptr + slot.len);

  // Delete slot and update the next slots.
  for i in slot.pos + 1..num_slots {
    let ptr = PAGE_HEADER_SIZE + i * OVERFLOW_SLOT_SIZE;
    let new_off = u8_u32!(&page[ptr + 4..ptr + 8]) as usize + slot.len;
    write_u32!(&mut page[ptr + 4..ptr + 8], new_off as u32);
    page.copy_within(ptr..ptr + OVERFLOW_SLOT_SIZE, ptr - OVERFLOW_SLOT_SIZE);
  }

  let is_empty = num_slots - 1 == 0;

  // Update metadata.
  set_num_slots(&mut page, num_slots - 1);
  set_used_space(&mut page, page_size - free_ptr - slot.len);

  let mut next_overflow_page = overflow_page(&page);

  if slot.is_overflow {
    assert_ne!(next_overflow_page, INVALID_PAGE_ID, "Invalid overflow page for slot {}", slot.id);
    next_overflow_page = del_overflow(next_overflow_page, slot.next_page, slot.next_slot, mngr);
    set_overflow_page(&mut page, next_overflow_page);
  }

  mngr.write(page_id, &page);

  if is_empty {
    mngr.mark_as_free(page_id);
    next_overflow_page
  } else {
    page_id
  }
}

// Returns prefix and is_overflow flag.
// If `is_overflow` is true, then there is more data available in the overflow page.
fn get_varlen_prefix(buf: &[u8]) -> (&[u8], bool) {
  assert_eq!(buf.len(), VARLEN_SIZE, "Invalid varlen length: {}", buf.len());
  let len = u8_u32!(&buf[0..4]) as usize;
  if len <= VARLEN_MAX_LEN {
    (&buf[4..4 + len], false)
  } else {
    (&buf[4..8], true)
  }
}

// Returns full varlen data as a vector.
fn get_varlen(buf: &[u8], mngr: &mut StorageManager) -> Vec<u8> {
  assert_eq!(buf.len(), VARLEN_SIZE, "Invalid varlen length: {}", buf.len());
  let len = u8_u32!(&buf[0..4]) as usize;
  let mut data = Vec::with_capacity(len);
  if len <= VARLEN_MAX_LEN {
    data.extend_from_slice(&buf[4..4 + len]);
  } else {
    // Fetch data from overflow pages.
    data.extend_from_slice(&buf[4..8]);
    let mut page_id = u8_u32!(&buf[8..12]);
    let mut slot_id = u8_u32!(&buf[12..16]);

    let mut page = vec![0u8; mngr.page_size()];
    while page_id != INVALID_PAGE_ID {
      mngr.read(page_id, &mut page);
      let slot = slot_info(&page, slot_id);
      data.extend_from_slice(&page[slot.off..slot.off + slot.len]);
      page_id = slot.next_page;
      slot_id = slot.next_slot;
    }
  }
  data
}

//==========
// Leaf page
//==========

// Private method to return slot (key + value) for the position `pos` in the leaf page.
fn get_slot(page: &[u8], pos: usize) -> &[u8] {
  assert_eq!(page_type(page), PageType::Leaf);
  let num_slots = num_slots(page);
  assert!(pos < num_slots, "Index {} is out of bounds for {} slots", pos, num_slots);
  let off = pos * (2 /* key + value */ * VARLEN_SIZE); // offset into page buffer
  &page[PAGE_HEADER_SIZE + off..PAGE_HEADER_SIZE + off + 2 * VARLEN_SIZE]
}

// Returns key prefix and `is_overflow` flag for position `pos`.
pub fn get_key_prefix(page: &[u8], pos: usize) -> (&[u8], bool) {
  let slot = get_slot(page, pos);
  get_varlen_prefix(&slot[..VARLEN_SIZE])
}

// Returns full key stored at position `pos`.
pub fn get_key(page: &[u8], pos: usize, mngr: &mut StorageManager) -> Vec<u8> {
  let slot = get_slot(page, pos);
  get_varlen(&slot[..VARLEN_SIZE], mngr)
}

// Returns full value stored at position `pos`.
pub fn get_val(page: &[u8], pos: usize, mngr: &mut StorageManager) -> Vec<u8> {
  let slot = get_slot(page, pos);
  get_varlen(&slot[VARLEN_SIZE..], mngr)
}

fn set_slot(page: &mut [u8], pos: usize) -> &mut [u8] {
  let num_slots = num_slots(page);
  assert!(pos < num_slots, "Index {} is out of bounds for {} slots", pos, num_slots);
  let off = pos * (2 /* key + value */ * VARLEN_SIZE); // offset into page buffer
  &mut page[PAGE_HEADER_SIZE + off..PAGE_HEADER_SIZE + off + 2 * VARLEN_SIZE]
}

// Sets the key for the position.
pub fn set_key(page: &mut [u8], pos: usize, data: &[u8], mngr: &mut StorageManager) {
  let mut overflow_page = overflow_page(page);
  let buf = set_slot(page, pos);
  set_varlen(&mut buf[..VARLEN_SIZE], data, &mut overflow_page, mngr);
  set_overflow_page(page, overflow_page);
}

// Sets the value for the position.
pub fn set_val(page: &mut [u8], pos: usize, data: &[u8], mngr: &mut StorageManager) {
  let mut overflow_page = overflow_page(page);
  let buf = set_slot(page, pos);
  set_varlen(&mut buf[VARLEN_SIZE..], data, &mut overflow_page, mngr);
  set_overflow_page(page, overflow_page);
}

// Print debug information of the page.
pub fn debug_page(page_id: u32, page: &[u8]) {
  let mut output = String::new();
  res!(writeln!(&mut output, "PAGE {}", page_id));
  let tpe = page_type(page);
  res!(writeln!(&mut output, "  page size: {}", page.len()));
  res!(writeln!(&mut output, "  type: {:?}", tpe));

  match tpe {
    PageType::Overflow => {
      let num_slots = num_slots(page);
      res!(writeln!(&mut output, "  num slots: {}", num_slots));
      let overflow_page = overflow_page(page);
      if overflow_page == INVALID_PAGE_ID {
        res!(writeln!(&mut output, "  overflow page: N/A"));
      } else {
        res!(writeln!(&mut output, "  overflow page: {}", overflow_page));
      }
      res!(writeln!(&mut output, "  used space: {}", used_space(page)));

      for i in 0..num_slots {
        let slot = slot_info_by_pos(page, i);
        if slot.is_overflow {
          res!(
            writeln!(
              &mut output,
              "  [{}] slot {}: off = {}, len = {}, next page = {}, next slot = {}",
              slot.pos, slot.id, slot.off, slot.len, slot.next_page, slot.next_slot
            )
          );
        } else {
          res!(
            writeln!(
              &mut output,
              "  [{}] slot {}: off = {}, len = {}",
              slot.pos, slot.id, slot.off, slot.len
            )
          );
        }
      }
    },
    _ => {
      res!(writeln!(&mut output, "Unsupported"));
    }
  }
  println!("{}", output);
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::storage::Options;

  fn get_storage(page_size: u32) -> StorageManager {
    let opts = Options::new().as_mem(1024).with_page_size(page_size).build();
    StorageManager::new(&opts)
  }

  fn print_pages(mngr: &mut StorageManager) {
    println!("num pages: {}", mngr.num_pages());
    println!("mem usage: {}", mngr.estimated_mem_usage());
    println!();
    let mut tmp = vec![0u8; mngr.page_size()];
    for page_id in 0..mngr.num_pages() {
      let page_id = page_id as u32;
      if mngr.is_accessible(page_id) {
        mngr.read(page_id, &mut tmp);
        debug_page(page_id, &tmp);
      }
    }
  }

  #[test]
  fn test_page_set_varlen_with_overflow() {
    let mut mngr = get_storage(1024);
    let mut data = Vec::new();
    for i in 1..2000 {
      data.push(i as u8);
    }

    let mut buf = Vec::new();
    for _ in 0..1 {
      buf.push(vec![0u8; VARLEN_SIZE]);
    }

    let mut overflow_page = INVALID_PAGE_ID;

    println!("== Setting varlen ==");
    for arr in &mut buf {
      set_varlen(arr, &data, &mut overflow_page, &mut mngr);
    }
    print_pages(&mut mngr);

    for arr in &buf {
      println!("== Deleting varlen ==");
      del_varlen(&arr, overflow_page, &mut mngr);
      print_pages(&mut mngr);
    }

    assert!(false, "OK");
  }

  #[test]
  fn test_page_max_keys() {
    assert_eq!(max_keys(128), 3);
    assert_eq!(max_keys(4 * 1024), 127);
    assert_eq!(max_keys(8 * 1024), 255);
  }
}
