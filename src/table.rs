use std::io::Write;
use crate::error::Res;
use crate::storage::StorageManager;

// Block id representing an empty slot.
const EMPTY: u32 = 0;
// Block id representing a deleted entry in the table.
const TOMBSTONE: u32 = u32::MAX;
// Block id representing a reserved key-value pair (header info).
const RESERVED: u32 = u32::MAX - 1;

const TABLE_MAX_LOAD: f64 = 0.75;
const MAX_DATA_PAGES: usize = 6;

const FLAG_IS_DATA_PAGE: u32 = 0x1;
const FLAG_HAS_OVERFLOW: u32 = 0x2;
const FLAG_META_HASH_FUNC_1: u32 = 0x4;
const FLAG_META_HASH_FUNC_2: u32 = 0x8;
const FLAG_META_HASH_FUNC_3: u32 = 0x10;
const FLAG_META_HASH_FUNC_4: u32 = 0x20;

const HASH_FUNC_CNT: usize = 4; // Must be a power of 2
const HASH_FUNC_CNT_MINUS_1: usize = HASH_FUNC_CNT - 1;
const HASH_FUNC: [fn(u32) -> u32; HASH_FUNC_CNT] = [hash_func1, hash_func2, hash_func3, hash_func4];

//===============
// Hash functions
//===============

// https://burtleburtle.net/bob/hash/integer.html
// Full avalanche.
#[inline]
fn hash_func1(mut a: u32) -> u32 {
  a = a.wrapping_add(0x7ed55d16).wrapping_add(a << 12);
  a = (a ^ 0xc761c23c) ^ (a >> 19);
  a = a.wrapping_add(0x165667b1).wrapping_add(a << 5);
  a = (a.wrapping_add(0xd3a2646c)) ^ (a << 9);
  a = a.wrapping_add(0xfd7046c5).wrapping_add(a << 3);
  a = (a ^ 0xb55a4f09) ^ (a >> 16);
  return a;
}

// Full avalanche.
#[inline]
fn hash_func2(mut a: u32) -> u32 {
  a = a.wrapping_add(0x7fb9b1ee).wrapping_add(a << 12);
  a = (a ^ 0xab35dd63) ^ (a >> 19);
  a = a.wrapping_add(0x41ed960d).wrapping_add(a << 5);
  a = (a.wrapping_add(0xc7d0125e)) ^ (a << 9);
  a = a.wrapping_add(0x071f9f8f).wrapping_add(a << 3);
  a = (a ^ 0x55ab55b9) ^ (a >> 16);
  return a;
}

// Full avalanche.
#[inline]
fn hash_func3(mut a: u32) -> u32 {
  a = a.wrapping_sub(a << 6);
  a = a ^ (a >> 17);
  a = a.wrapping_sub(a << 9);
  a = a ^ (a << 4);
  a = a.wrapping_sub(a << 3);
  a = a ^ (a << 10);
  a = a ^ (a >> 15);
  return a;
}

// Half avalanche.
#[inline]
fn hash_func4(mut a: u32) -> u32 {
  a = a.wrapping_add(0x479ab41d).wrapping_add(a << 8);
  a = (a ^ 0xe4aa10ce) ^ (a >> 5);
  a = a.wrapping_add(0x9942f0a6).wrapping_sub(a << 14);
  a = (a ^ 0x5aedd67d) ^ (a >> 3);
  a = a.wrapping_add(0x17bea992).wrapping_add(a << 7);
  return a;
}

#[inline]
fn valid_key(key: u32) -> bool {
  key != EMPTY && key != TOMBSTONE && key != RESERVED
}

//======================
// Hash table operations
//======================

#[inline]
fn init_data_header(buf: &mut [u8]) {
  (&mut buf[0..4]).write(&u32_u8!(RESERVED)).unwrap();
  (&mut buf[4..8]).write(&u32_u8!(FLAG_IS_DATA_PAGE)).unwrap(); // flags
  (&mut buf[8..12]).write(&u32_u8!(RESERVED)).unwrap();
  (&mut buf[12..16]).write(&u32_u8!(0u32)).unwrap(); // count
  (&mut buf[16..20]).write(&u32_u8!(RESERVED)).unwrap();
  (&mut buf[20..24]).write(&u32_u8!(0u32)).unwrap(); // (data) overflow page | (meta) page length
}

#[inline]
fn init_meta_header(buf: &mut [u8]) {
  (&mut buf[0..4]).write(&u32_u8!(RESERVED)).unwrap();
  (&mut buf[4..8]).write(&u32_u8!(FLAG_IS_DATA_PAGE)).unwrap(); // flags
  (&mut buf[8..12]).write(&u32_u8!(RESERVED)).unwrap();
  (&mut buf[12..16]).write(&u32_u8!(0u32)).unwrap(); // count
  (&mut buf[16..20]).write(&u32_u8!(RESERVED)).unwrap();
  (&mut buf[20..24]).write(&u32_u8!(0u32)).unwrap(); // (data) overflow page | (meta) page length
}

#[inline]
fn is_data_page(buf: &[u8]) -> bool {
  u8_u32!(&buf[4..8]) & FLAG_IS_DATA_PAGE != 0
}

#[inline]
fn set_is_data_page(buf: &mut [u8], value: bool) {
  let flags = (u8_u32!(&buf[4..8]) & !FLAG_IS_DATA_PAGE) | value as u32;
  (&mut buf[4..8]).write(&u32_u8!(flags)).unwrap();
}

#[inline]
fn get_hash_func(buf: &[u8]) -> usize {
  let flags = u8_u32!(&buf[4..8]);
  if flags & FLAG_META_HASH_FUNC_1 != 0 {
    0
  } else if flags & FLAG_META_HASH_FUNC_2 != 0 {
    1
  } else if flags & FLAG_META_HASH_FUNC_3 != 0 {
    2
  } else if flags & FLAG_META_HASH_FUNC_4 != 0 {
    3
  } else {
    panic!("Could not find hash function");
  }
}

#[inline]
fn set_hash_func(buf: &mut [u8], hash_func: usize) {
  let mut flags = u8_u32!(&buf[4..8]);
  flags &= !(FLAG_META_HASH_FUNC_1 | FLAG_META_HASH_FUNC_2 | FLAG_META_HASH_FUNC_3 | FLAG_META_HASH_FUNC_4);
  match hash_func {
    0 => flags |= FLAG_META_HASH_FUNC_1,
    1 => flags |= FLAG_META_HASH_FUNC_2,
    2 => flags |= FLAG_META_HASH_FUNC_3,
    3 => flags |= FLAG_META_HASH_FUNC_4,
    _ => panic!("Invalid hash function {}", hash_func),
  }
  (&mut buf[4..8]).write(&u32_u8!(flags)).unwrap();
}

#[inline]
fn get_count(buf: &[u8]) -> u32 {
  u8_u32!(&buf[12..16])
}

#[inline]
fn set_count(buf: &mut [u8], count: u32) {
  (&mut buf[12..16]).write(&u32_u8!(count)).unwrap();
}

#[inline]
fn get_overflow_page(buf: &[u8]) -> Option<u32> {
  if (u8_u32!(&buf[4..8]) & FLAG_HAS_OVERFLOW) != 0 {
    Some(u8_u32!(&buf[20..24]))
  } else {
    None
  }
}

#[inline]
fn set_overflow_page(buf: &mut [u8], overflow_page_id: u32) {
  let flags = u8_u32!(&buf[4..8]) | FLAG_HAS_OVERFLOW;
  (&mut buf[4..8]).write(&u32_u8!(flags)).unwrap();
  (&mut buf[20..24]).write(&u32_u8!(overflow_page_id)).unwrap();
}

#[inline]
fn unset_overflow_page(buf: &mut [u8]) {
  let flags = u8_u32!(&buf[4..8]) & !FLAG_HAS_OVERFLOW;
  (&mut buf[4..8]).write(&u32_u8!(flags)).unwrap();
}

#[inline]
fn get_meta_page_len(buf: &[u8]) -> usize {
  u8_u32!(&buf[20..24]) as usize
}

#[inline]
fn set_meta_page_len(buf: &mut [u8], len: usize) {
  (&mut buf[20..24]).write(&u32_u8!(len as u32)).unwrap();
}

// Finds position where the key is or the next empty slot in the table.
// Buffer length needs to be a power of 2.
// Buffer needs to have at least u32 + u32 length.
#[inline]
fn find_pos(buf: &[u8], key: u32) -> (usize, Option<u32>) {
  assert!((buf.len() - 1) & buf.len() == 0, "Table length is not power of 2");
  assert!(buf.len() >= 8, "Table length needs to be at least 8 bytes");
  assert!(valid_key(key), "Unsupported key: {}", key);

  let len_minus_1 = buf.len() - 1;
  let size_minus_1 = (buf.len() >> 3) - 1; // len / 8 - 1

  let hash = hash_func1(key);
  let mut pos = (hash as usize & size_minus_1) << 3;
  let mut tombstone: Option<usize> = None;

  loop {
    let entry = u8_u32!(&buf[pos..pos + 4]);
    if entry == key {
      return (pos, Some(u8_u32!(&buf[pos + 4..pos + 8])));
    } else if entry == EMPTY {
      // We found an empty entry, return either previously found tombstone or the position itself.
      return (tombstone.unwrap_or(pos), None);
    } else if entry == TOMBSTONE {
      // We found a tombstone, record the position and keep moving.
      if tombstone.is_none() {
        tombstone = Some(pos);
      }
    }
    pos = (pos + 8) & len_minus_1;
  }
}

// Returns Some(value) if the key exists, None otherwise.
#[inline]
fn data_get(buf: &[u8], key: u32) -> Option<u32> {
  find_pos(buf, key).1
}

// Returns true if the operation was successful, i.e. we could update the key or insert a new one.
// False indicates that the table is full.
#[inline]
fn data_set(buf: &mut [u8], key: u32, value: u32) -> bool {
  let (pos, maybe_value) = find_pos(buf.as_ref(), key);
  // Check if we can insert a new key
  let count = get_count(&buf);
  if maybe_value.is_none() && count as f64 / (buf.len() >> 3) as f64 >= TABLE_MAX_LOAD {
    return false;
  }
  (&mut buf[pos..pos + 4]).write(&u32_u8!(key)).unwrap();
  (&mut buf[pos + 4..pos + 8]).write(&u32_u8!(value)).unwrap();
  if maybe_value.is_none() {
    set_count(buf, count + 1);
  }
  true
}

// Returns true if the operation was successful, i.e. we deleted the key.
#[inline]
fn data_del(buf: &mut [u8], key: u32) -> bool {
  let (pos, maybe_value) = find_pos(buf.as_ref(), key);
  if maybe_value.is_none() {
    return false;
  }
  (&mut buf[pos..pos + 4]).write(&u32_u8!(TOMBSTONE)).unwrap();
  let count = get_count(&buf);
  set_count(buf, count - 1);
  true
}

#[inline]
fn meta_find_pos(buf: &[u8], key: u32, hash_func: usize) -> (usize, Option<u32>) {
  let len = get_meta_page_len(buf);
  assert!((len - 1) & len == 0, "Table length is not power of 2");
  assert!(len >= 8, "Table length needs to be at least 8 bytes");
  assert!(valid_key(key), "Unsupported key: {}", key);

  let len_minus_1 = len - 1;
  let size_minus_1 = (len >> 3) - 1; // len / 8 - 1

  let hash = HASH_FUNC[hash_func](key);
  let mut pos = (hash as usize & size_minus_1) << 3;

  loop {
    let entry = u8_u32!(&buf[pos..pos + 4]);
    if valid_key(entry) {
      return (pos, Some(u8_u32!(&buf[pos + 4..pos + 8])));
    } else if entry == EMPTY {
      return (pos, None);
    }
    pos = (pos + 8) & len_minus_1;
  }
}

#[inline]
fn meta_get(buf: &[u8], key: u32) -> Option<u32> {
  let hash_func = get_hash_func(&buf);
  meta_find_pos(buf, key, hash_func).1
}

#[inline]
fn meta_set(buf: &mut [u8], key: u32, value: u32) -> bool {
  let hash_func = get_hash_func(&buf);
  let (pos, opt) = meta_find_pos(buf.as_ref(), key, hash_func);
  (&mut buf[pos..pos + 4]).write(&u32_u8!(key)).unwrap();
  (&mut buf[pos + 4..pos + 8]).write(&u32_u8!(value)).unwrap();
  if opt.is_none() {
    let count = get_count(&buf);
    set_count(buf, count + 1);
  }
  true
}

#[inline]
fn meta_del(buf: &mut [u8], key: u32) -> bool {
  let hash_func = get_hash_func(&buf);
  let (pos, opt) = meta_find_pos(buf.as_ref(), key, hash_func);
  (&mut buf[pos..pos + 4]).write(&u32_u8!(EMPTY)).unwrap();
  if opt.is_some() {
    let count = get_count(&buf);
    set_count(buf, count - 1);
  }
  true
}

struct KeyValueIter<'a> {
  buf: &'a [u8],
  pos: usize,
  len: usize,
}

impl<'a> Iterator for KeyValueIter<'a> {
  type Item = (u32, u32);

  fn next(&mut self) -> Option<Self::Item> {
    while self.pos + 8 <= self.buf.len() {
      let key = u8_u32!(&self.buf[self.pos..self.pos + 4]);
      let val = u8_u32!(&self.buf[self.pos + 4..self.pos + 8]);
      self.pos += 8;
      if valid_key(key) {
        return Some((key, val));
      }
    }
    None
  }
}

#[inline]
fn key_value_iter<'a>(buf: &'a [u8]) -> KeyValueIter<'a> {
  let page_len = if is_data_page(buf) { buf.len() } else { get_meta_page_len(buf) };
  KeyValueIter { buf, pos: 0, len: page_len }
}

//======================
// Page table operations
//======================

// Creates new data page.
#[inline]
fn create_new(buf: &mut[u8], key: u32, value: u32, mngr: &mut StorageManager) -> u32 {
  init_header(buf);
  set_is_data_page(buf, true);
  data_set(buf, key, value);
  mngr.write_next(&buf)
}

// Method invocation potentially modifies the buffer.
// Input buffer data should have the content of the page_id.
fn insert_data(
  mut page_id: u32,
  buf: &mut [u8],
  key: u32,
  value: u32,
  mngr: &mut StorageManager
) -> bool {
  assert!(is_data_page(&buf));

  let mut num_overflow = 0;
  loop {
    if data_set(buf, key, value) {
      mngr.write(page_id, &buf);
      return true; // the value was inserted into the current page
    } else if let Some(overflow_page_id) = get_overflow_page(&buf) {
      page_id = overflow_page_id;
      mngr.read(page_id, buf);
      num_overflow += 1;
    } else if num_overflow + 1 < MAX_DATA_PAGES {
      // Create a new page, insert the value.
      let mut new_buf = vec![0u8; buf.len()];
      let overflow_page_id = create_new(&mut new_buf, key, value, mngr);
      // Update the current page with the overflow.
      set_overflow_page(buf, overflow_page_id);
      mngr.write(page_id, &buf);
      return true; // the value was inserted into the overflow page
    } else {
      return false;
    }
  }
}

// Rebalances pages and inserts the key-value pair.
// Returns a new page id.
fn rebalance(
  mut root: u32,
  buf: &mut[u8],
  key: u32,
  value: u32,
  hash_func: usize,
  mngr: &mut StorageManager
) -> u32 {
  // Create a new meta page.
  let mut meta_buf = vec![0u8; buf.len()];
  init_header(&mut meta_buf);
  set_is_data_page(&mut meta_buf, false);
  set_hash_func(&mut meta_buf, hash_func);
  set_meta_page_len(&mut meta_buf, buf.len());

  let mut all_keys = Vec::new();
  all_keys.push((key, value));

  loop {
    mngr.read(root, buf);
    mngr.mark_as_free(root); // we are not going to use the page

    let overflow = get_overflow_page(&buf);
    // Iterate over the keys in the page
    let mut iter = key_value_iter(&buf);
    while let Some(pair) = iter.next() {
      all_keys.push(pair);
    }

    for &(k, v) in &all_keys {
      if let Some(next) = meta_get(&meta_buf, k) {
        mngr.read(next, buf);
        assert!(insert_data(next, buf, k, v, mngr));
      } else {
        buf.fill(0);
        let next_page = create_new(buf, k, v, mngr);
        meta_set(&mut meta_buf, k, next_page);
      }
    }

    if let Some(overflow_page) = overflow {
      root = overflow_page;
      all_keys.clear();
    } else {
      break;
    }
  }

  mngr.write_next(&mut meta_buf)
}

// Returns the existing page id if the root has not changed, otherwise a new page id is returned.
fn insert(
  root: u32,
  buf: &mut[u8],
  key: u32,
  value: u32,
  depth: usize,
  mngr: &mut StorageManager
) -> u32 {
  let hash_func = depth & HASH_FUNC_CNT_MINUS_1;

  mngr.read(root, buf);

  if is_data_page(&buf) {
    if insert_data(root, buf, key, value, mngr) {
      root
    } else {
      rebalance(root, buf, key, value, hash_func, mngr)
    }
  } else if let Some(next) = meta_get(&buf, key) {
    let new_next = insert(next, buf, key, value, depth + 1, mngr);
    if new_next != next {
      mngr.read(root, buf);
      meta_set(buf, key, new_next);
      mngr.write(root, &buf);
    }
    root
  } else {
    // There is no such next page in the meta page, so we need to create one and add the key
    // to the meta page.
    let mut new_buf = vec![0u8; buf.len()];
    let next_page = create_new(&mut new_buf, key, value, mngr);
    meta_set(buf, key, next_page);
    mngr.write(root, &buf);
    root // root has not changed
  }
}

fn delete_data(
  root: u32,
  buf: &mut [u8],
  key: u32,
  mngr: &mut StorageManager
) -> (Option<u32>, bool) {
  assert!(is_data_page(&buf));

  let mut maybe_parent = None;
  let mut curr = root;
  let mut delete_ok = false;

  loop {
    if data_del(buf, key) {
      mngr.write(curr, &buf);
      delete_ok = true;
      break;
    }

    if let Some(overflow) = get_overflow_page(&buf) {
      maybe_parent = Some(curr);
      curr = overflow;
      mngr.read(curr, buf);
    } else {
      break;
    }
  };

  // Perform rebalancing for the data page chain.
  if get_count(&buf) > 0 {
    (Some(root), delete_ok)
  } else {
    let maybe_overflow = get_overflow_page(&buf);
    if let Some(parent) = maybe_parent {
      mngr.read(parent, buf);
      if let Some(overflow) = maybe_overflow {
        set_overflow_page(buf, overflow);
      } else {
        unset_overflow_page(buf);
      }
      // Free the current page since the parent has been re-linked.
      mngr.write(parent, buf);
      mngr.mark_as_free(curr);
      (Some(root), delete_ok)
    } else {
      // Delete the first page in the chain of data pages
      // TODO: Free the current page
      mngr.mark_as_free(curr);
      (maybe_overflow, delete_ok)
    }
  }
}

fn delete(root: u32, buf: &mut[u8], key: u32, mngr: &mut StorageManager) -> (Option<u32>, bool) {
  mngr.read(root, buf);

  if is_data_page(&buf) {
    delete_data(root, buf, key, mngr)
  } else if let Some(next) = meta_get(&buf, key) {
    let (maybe_new_page, delete_ok) = delete(next, buf, key, mngr);
    if let Some(new_page) = maybe_new_page {
      if new_page != next {
        mngr.read(root, buf);
        meta_set(buf, key, new_page);
        mngr.write(root, &buf);
      }
      (Some(root), delete_ok)
    } else {
      mngr.read(root, buf);
      meta_del(buf, key);
      mngr.write(root, &buf);
      if get_count(&buf) == 0 {
        // Free the current page.
        mngr.mark_as_free(root);
        (None, delete_ok)
      } else {
        (Some(root), delete_ok)
      }
    }
  } else {
    // No such key.
    (Some(root), false)
  }
}

#[derive(Debug)]
struct Statistics {
  max_block_id: u32,
  num_data_pages: usize,
  num_meta_pages: usize,
  max_depth: usize,
  max_data_len: usize,
}

// Finds the max block id stored in the page table.
fn collect_stats(mut root: u32, buf: &mut [u8], mngr: &mut StorageManager) -> Statistics {
  let mut data_pages = Vec::new(); // vector to keep data pages stored in a meta page

  let mut stats = Statistics {
    max_block_id: 0,
    num_data_pages: 0,
    num_meta_pages: 0,
    max_depth: 0,
    max_data_len: 0,
  };

  mngr.read(root, buf);

  if is_data_page(&buf) {
    loop {
      stats.num_data_pages += 1;
      stats.max_data_len += 1;
      let mut iter = key_value_iter(&buf);
      while let Some((key, _)) = iter.next() {
        stats.max_block_id = stats.max_block_id.max(key);
      }

      if let Some(overflow) = get_overflow_page(&buf) {
        root = overflow;
        mngr.read(root, buf);
      } else {
        break;
      }
    }
  } else {
    stats.num_meta_pages += 1;
    data_pages.clear();
    let mut iter = key_value_iter(&buf);
    while let Some((_, page)) = iter.next() {
      data_pages.push(page);
    }

    for &page in &data_pages {
      let tmp_stats = collect_stats(page, buf, mngr);
      stats.max_block_id = stats.max_block_id.max(tmp_stats.max_block_id);
      stats.num_data_pages += tmp_stats.num_data_pages;
      stats.num_meta_pages += tmp_stats.num_meta_pages;
      stats.max_depth = stats.max_depth.max(tmp_stats.max_depth);
      stats.max_data_len = stats.max_data_len.max(tmp_stats.max_data_len);
    }
    stats.max_depth += 1;
  }

  stats
}

pub struct PageTable {
  mngr: StorageManager,
  root: Option<u32>,
  buf: Vec<u8>,
  max_block_id: u32,
}

impl PageTable {
  pub fn new(mngr: StorageManager) -> Self {
    let page_size = mngr.page_size();
    Self { mngr, root: None, buf: vec![0u8; page_size], max_block_id: 1 }
  }

  pub fn next_block_id(&mut self) -> u32 {
    let next = self.max_block_id;
    self.max_block_id += 1;
    next
  }

  pub fn get(&mut self, key: u32) -> Option<u32> {
    match self.root {
      Some(mut root) => {
        loop {
          self.mngr.read(root, &mut self.buf);
          if is_data_page(&self.buf) {
            let res = data_get(&self.buf, key);
            if res.is_some() {
              return res;
            }
            if let Some(overflow) = get_overflow_page(&self.buf) {
              root = overflow;
            } else {
              return None;
            }
          } else if let Some(next) = meta_get(&self.buf, key) {
            root = next;
          } else {
            return None;
          }
        }
      },
      None => None,
    }
  }

  pub fn put(&mut self, key: u32, value: u32) {
    let new_root = match self.root {
      Some(root) => insert(root, &mut self.buf, key, value, 1, &mut self.mngr),
      None => {
        self.buf.fill(0);
        create_new(&mut self.buf, key, value, &mut self.mngr)
      },
    };

    if Some(new_root) != self.root {
      self.root = Some(new_root);
      self.mngr.update_page_table(self.root);
    }
    self.mngr.sync();
  }

  pub fn del(&mut self, key: u32) -> bool {
    let (new_root, delete_ok) = match self.root {
      Some(root) => delete(root, &mut self.buf, key, &mut self.mngr),
      None => (None, false),
    };

    if new_root != self.root {
      self.root = new_root;
      self.mngr.update_page_table(self.root);
    }
    self.mngr.sync();
    delete_ok
  }

  pub fn mngr(&self) -> &StorageManager {
    &self.mngr
  }
}

// For debugging only
fn fmt0(root: u32, buf: &mut [u8], mngr: &mut StorageManager, off: usize) {
  mngr.read(root, buf);
  if is_data_page(&buf) {
    print!("{:width$}*[{}] ({})", "", root, get_count(&buf), width = off);
    if let Some(overflow) = get_overflow_page(&buf) {
      print!(" ->");
      fmt0(overflow, buf, mngr, 1);
    } else {
      println!();
    }
  } else {
    let mut iter = key_value_iter(&buf);
    let mut values = Vec::new();
    while let Some((_, v)) = iter.next() {
      values.push(v);
    }
    let hash_func = get_hash_func(&buf);
    println!("{:width$}#[{}] ({}) hash({})", "", root, values.len(), hash_func, width = off);
    for &v in &values {
      fmt0(v, buf, mngr, off + 2);
    }
  }
}

pub fn fmt(pt: &mut PageTable) {
  println!("PageTable(root: {:?}, max block: {})", pt.root, pt.max_block_id);
  if let Some(root) = pt.root {
    fmt0(root, &mut pt.buf, &mut pt.mngr, 0);
  }
  println!("Storage: {} pages, {} free pages, {} mem",
    pt.mngr().num_pages(),
    pt.mngr().num_free_pages(),
    pt.mngr().estimated_mem_usage()
  );
  println!();
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::collections::HashSet;
  use rand::prelude::*;
  use crate::storage::Options;
  use std::time::Instant;

  // #[test]
  fn test_table_debug() {
    let opts = Options::new().as_mem(0).with_page_size(128).build();
    let mngr = StorageManager::new(&opts);
    let mut pt = PageTable::new(mngr);

    // 500 values: Storage: 56 pages, 0 free pages, 7200 mem
    for i in 1..501 {
      // let block = pt.next_block_id();
      pt.put(i, i);
    }

    fmt(&mut pt);

    // for i in (1..400).rev() {
    //   // println!();
    //   // println!("Deleting key {}", i);
    //   assert!(pt.del(i));
    //   // fmt(&mut pt);
    // }
    //
    // fmt(&mut pt);

    assert!(false);
  }

  // #[test]
  fn test_table_collect_stats_debug() {
    // TODO: fails with 128 byte pages
    // let opts = Options::new().as_mem(0).with_page_size(128).build();
    let opts = Options::new().as_disk("./test.db").with_page_size(4096).build();
    let mngr = StorageManager::new(&opts);
    let mut pt = PageTable::new(mngr);

    let now = Instant::now();

    for _ in 0..50000 {
      let block = pt.next_block_id();
      pt.put(block, block);
    }

    println!("Insertion took {} ms", now.elapsed().as_millis());

    let now = Instant::now();

    let stats = collect_stats(pt.root.unwrap(), &mut pt.buf, &mut pt.mngr);

    fmt(&mut pt);
    println!("Stats: {:?}, took {} ms", stats, now.elapsed().as_millis());
    // Stats: Statistics { max_block_id: 3000000, num_data_pages: 259077, num_meta_pages: 510, max_depth: 2, max_data_len: 1 }, took 26438 ms

    assert!(false);
  }

  #[test]
  fn test_table_hash_functions() {
    for i in 0..32 {
      let mut hashes = Vec::new();
      for h in 0..HASH_FUNC_CNT {
        hashes.push(HASH_FUNC[h](1 << i));
      }

      hashes.sort();
      for k in 0..hashes.len() - 1 {
        assert_ne!(hashes[k], hashes[k + 1]);
      }
    }
  }

  #[test]
  fn test_table_data_page_init_header() {
    let mut buf = vec![0u8; 128];
    init_header(buf.as_mut());

    assert!(is_data_page(&buf));
    assert_eq!(get_count(&buf), 0);
    assert_eq!(get_overflow_page(&buf), None);
  }

  #[test]
  fn test_table_data_page_is_data_page() {
    let mut buf = vec![0u8; 128];
    init_header(buf.as_mut());

    assert!(is_data_page(&buf));

    for value in [false, true, false, true, false] {
      set_is_data_page(buf.as_mut(), value);
      assert_eq!(is_data_page(&buf), value);
    }
  }

  #[test]
  fn test_table_data_page_count() {
    let mut buf = vec![0u8; 128];
    init_header(buf.as_mut());

    for i in [1, 128, 1000, u32::MAX, 0] {
      set_count(&mut buf, i);
      assert_eq!(get_count(&buf), i);
    }
  }

  #[test]
  fn test_table_data_page_overflow() {
    let mut buf = vec![0u8; 128];
    init_header(buf.as_mut());

    assert_eq!(get_overflow_page(&buf), None);

    set_overflow_page(buf.as_mut(), 123);
    assert_eq!(get_overflow_page(&buf), Some(123));

    set_overflow_page(buf.as_mut(), 1);
    assert_eq!(get_overflow_page(&buf), Some(1));

    set_overflow_page(buf.as_mut(), u32::MAX);
    assert_eq!(get_overflow_page(&buf), Some(u32::MAX));

    unset_overflow_page(buf.as_mut());
    assert_eq!(get_overflow_page(&buf), None);
  }

  #[test]
  #[should_panic(expected = "Table length is not power of 2")]
  fn test_table_data_page_find_pos_not_power_of_2() {
    let buf = vec![0u8; 127];
    find_pos(&buf, 123);
  }

  #[test]
  #[should_panic(expected = "Table length needs to be at least 8 bytes")]
  fn test_table_data_page_find_pos_too_short() {
    let buf = vec![0u8; 4];
    find_pos(&buf, 123);
  }

  #[test]
  #[should_panic(expected = "Unsupported key: 0")]
  fn test_table_data_page_find_pos_unsupported_key_empty() {
    let buf = vec![0u8; 128];
    find_pos(&buf, EMPTY);
  }

  #[test]
  #[should_panic(expected = "Unsupported key: 4294967295")]
  fn test_table_data_page_find_pos_unsupported_key_tombstone() {
    let buf = vec![0u8; 128];
    find_pos(&buf, TOMBSTONE);
  }

  #[test]
  #[should_panic(expected = "Unsupported key: 4294967294")]
  fn test_table_data_page_find_pos_unsupported_key_reserved() {
    let buf = vec![0u8; 128];
    find_pos(&buf, RESERVED);
  }

  #[test]
  fn test_table_data_page_set_smallest_length() {
    let mut buf = vec![0u8; 32];
    init_header(&mut buf);
    assert!(data_set(&mut buf, 100, 200));
    assert_eq!(data_get(&buf, 100), Some(200));
    assert_eq!(get_count(&buf), 1);
  }

  #[test]
  fn test_table_data_page_set_insert_over_capacity() {
    let mut buf = vec![0u8; 128];
    init_header(&mut buf);

    for i in 100..112 {
      assert!(data_set(&mut buf, i, i));
    }
    assert_eq!(get_count(&buf), 12);

    for i in 112..200 {
      assert!(!data_set(&mut buf, i, i));
    }
    assert_eq!(get_count(&buf), 12);
  }

  #[test]
  fn test_table_data_page_set_update_over_capacity() {
    let mut buf = vec![0u8; 128];
    init_header(&mut buf);

    for i in 100..112 {
      assert!(data_set(&mut buf, i, i));
    }

    for i in 100..112 {
      assert!(data_set(&mut buf, i, i));
    }

    assert_eq!(get_count(&buf), 12);
  }

  #[test]
  fn test_table_data_page_set_and_data_get() {
    let mut buf = vec![0u8; 128];
    init_header(&mut buf);
    for i in 100..112 {
      data_set(&mut buf, i, i);
    }
    for i in 100..112 {
      assert_eq!(data_get(&buf, i), Some(i));
    }
  }

  #[test]
  fn test_table_data_page_get_empty_table() {
    let mut buf = vec![0u8; 128];
    init_header(&mut buf);
    for i in 3..1000 {
      assert_eq!(data_get(&buf, i), None);
    }
  }

  #[test]
  fn test_table_data_page_get_non_existent() {
    let mut buf = vec![0u8; 128];
    init_header(&mut buf);
    for i in 100..112 {
      data_set(&mut buf, i, i);
    }
    for i in 3..1000 {
      if i < 100 && i >= 112 {
        assert_eq!(data_get(&buf, i), None);
      }
    }
  }

  #[test]
  fn test_table_data_page_iter() {
    let mut exp = vec![];
    let mut res = vec![];

    let mut buf = vec![0u8; 128];
    init_header(&mut buf);
    for i in 100..112 {
      assert!(data_set(&mut buf, i, i));
      exp.push((i, i));
    }

    let mut iter = key_value_iter(&buf);
    while let Some((key, value)) = iter.next() {
      res.push((key, value));
    }
    res.sort();
    assert_eq!(res, exp);
    assert_eq!(res.len(), get_count(&buf) as usize);
  }

  //================
  // Meta page tests
  //================

  #[test]
  #[should_panic(expected = "Table length is not power of 2")]
  fn test_table_meta_page_find_pos_not_power_of_2() {
    let buf = vec![0u8; 127];
    meta_find_pos(&buf, 123, 1);
  }

  #[test]
  #[should_panic(expected = "Table length needs to be at least 8 bytes")]
  fn test_table_meta_page_find_pos_too_short() {
    let buf = vec![0u8; 4];
    meta_find_pos(&buf, 123, 1);
  }

  #[test]
  #[should_panic(expected = "Unsupported key: 0")]
  fn test_table_meta_page_find_pos_unsupported_key_empty() {
    let buf = vec![0u8; 128];
    meta_find_pos(&buf, EMPTY, 1);
  }

  #[test]
  #[should_panic(expected = "Unsupported key: 4294967295")]
  fn test_table_meta_page_find_pos_unsupported_key_tombstone() {
    let buf = vec![0u8; 128];
    meta_find_pos(&buf, TOMBSTONE, 1);
  }

  #[test]
  #[should_panic(expected = "Unsupported key: 4294967294")]
  fn test_table_meta_page_find_pos_unsupported_key_reserved() {
    let buf = vec![0u8; 128];
    meta_find_pos(&buf, RESERVED, 1);
  }

  #[test]
  fn test_table_meta_page_set_get_hash_func() {
    let mut buf = vec![0u8; 128];
    init_header(&mut buf);
    set_is_data_page(&mut buf, false);

    for i in 0..HASH_FUNC_CNT {
      set_hash_func(&mut buf, i);
      assert_eq!(get_hash_func(&buf), i);
    }
  }

  #[test]
  #[should_panic(expected = "Invalid hash function 4")]
  fn test_table_meta_page_set_hash_func_invalid() {
    let mut buf = vec![0u8; 128];
    init_header(&mut buf);
    set_hash_func(&mut buf, 4);
  }

  #[test]
  #[should_panic(expected = "Could not find hash function")]
  fn test_table_meta_page_get_hash_func_invalid() {
    let mut buf = vec![0x21u8; 128];
    init_header(&mut buf);
    get_hash_func(&buf);
  }

  #[test]
  fn test_table_meta_page_get_empty() {
    let mut buf = vec![0u8; 128];
    init_header(&mut buf);
    set_is_data_page(buf.as_mut(), false);
    set_hash_func(&mut buf, 1);

    for i in 10..1000 {
      assert_eq!(meta_get(&buf, i), None);
    }
    assert_eq!(get_count(&buf), 0);
  }

  #[test]
  fn test_table_meta_page_set_data_get() {
    let mut buf = vec![0u8; 128];
    init_header(buf.as_mut());
    set_is_data_page(buf.as_mut(), false);
    set_hash_func(buf.as_mut(), 1);

    for i in 10..10000 {
      assert!(meta_set(buf.as_mut(), i, i));
      assert_eq!(meta_get(buf.as_mut(), i), Some(i));
    }

    for i in 10..10000 {
      assert!(meta_get(buf.as_mut(), i).is_some());
    }

    assert_eq!(get_count(&buf), 13); // we can only fit 13 key-value pairs in a 128 byte page
  }

  #[test]
  fn test_table_meta_page_set_get_data_del() {
    let mut buf = vec![0u8; 128];
    init_header(buf.as_mut());
    set_is_data_page(buf.as_mut(), false);
    set_hash_func(buf.as_mut(), 1);

    for i in 10..10000 {
      assert!(meta_set(buf.as_mut(), i, i));
      assert_eq!(meta_get(buf.as_mut(), i), Some(i));
      assert!(meta_del(buf.as_mut(), i));
    }

    assert_eq!(get_count(&buf), 0);

    for i in 10..10000 {
      assert_eq!(meta_get(buf.as_mut(), i), None);
    }
  }

  // PageTable tests

  #[test]
  fn test_table_collect_stats() {
    let opts = Options::new().as_mem(0).with_page_size(128).build();
    let mngr = StorageManager::new(&opts);
    let mut pt = PageTable::new(mngr);

    let mut blocks = Vec::new();

    for _ in 0..1000 {
      let block = pt.next_block_id();
      blocks.push(block);
      pt.put(block, block);
    }

    let stats = collect_stats(pt.root.unwrap(), &mut pt.buf, &mut pt.mngr);
    assert_eq!(stats.max_block_id, *blocks.iter().max().unwrap());
    assert_eq!(stats.max_block_id, pt.max_block_id - 1);
    assert_eq!(stats.num_data_pages, 108);
    assert_eq!(stats.num_meta_pages, 4);
    assert_eq!(stats.max_depth, 2);
    assert_eq!(stats.max_data_len, 6);

    for &block in &blocks[..500] {
      pt.del(block);
      let stats = collect_stats(pt.root.unwrap(), &mut pt.buf, &mut pt.mngr);
      assert_eq!(stats.max_block_id, *blocks.iter().max().unwrap());
      assert_eq!(stats.max_block_id, pt.max_block_id - 1);
    }

    let stats = collect_stats(pt.root.unwrap(), &mut pt.buf, &mut pt.mngr);
    assert_eq!(stats.max_block_id, pt.max_block_id - 1);
    assert_eq!(stats.num_data_pages, 82);
    assert_eq!(stats.num_meta_pages, 4);
    assert_eq!(stats.max_depth, 2);
    assert_eq!(stats.max_data_len, 4);

    for &block in blocks[501..1000].iter().rev() {
      pt.del(block);
      let stats = collect_stats(pt.root.unwrap(), &mut pt.buf, &mut pt.mngr);
      assert_eq!(stats.max_block_id, block - 1);
    }

    let stats = collect_stats(pt.root.unwrap(), &mut pt.buf, &mut pt.mngr);
    assert_eq!(stats.max_block_id, 501);
    assert_eq!(stats.num_data_pages, 1);
    assert_eq!(stats.num_meta_pages, 1);
    assert_eq!(stats.max_depth, 1);
    assert_eq!(stats.max_data_len, 1);
  }

  #[test]
  fn test_table_put_get_correctness() {
    let opts = Options::new().as_mem(0).with_page_size(128).build();
    let mngr = StorageManager::new(&opts);
    let mut pt = PageTable::new(mngr);

    for i in 1..1000 {
      pt.put(i, i);
    }

    for i in 1..1000 {
      assert_eq!(pt.get(i), Some(i));
    }

    for i in 1000..2000 {
      assert_eq!(pt.get(i), None);
    }
  }

  #[test]
  fn test_table_put_del_correctness() {
    let opts = Options::new().as_mem(0).with_page_size(128).build();
    let mngr = StorageManager::new(&opts);
    let mut pt = PageTable::new(mngr);

    for i in 1..1000 {
      pt.put(i, i);
    }

    for i in 1000..2000 {
      assert!(!pt.del(i));
    }

    for i in 1..1000 {
      assert!(pt.del(i));
    }

    for i in 1..2000 {
      assert!(!pt.del(i));
    }
  }

  #[test]
  fn test_table_page_allocation() {
    let opts = Options::new().as_mem(0).with_page_size(128).build();
    let mngr = StorageManager::new(&opts);
    let mut pt = PageTable::new(mngr);

    // We can only fit 12 key-value pairs in a 128 byte page.
    // Our chain is MAX_DATA_PAGES long.

    let mut blocks = Vec::new();

    for i in 1..12 * MAX_DATA_PAGES + 1 {
      let block = pt.next_block_id();
      blocks.push(block);
      pt.put(block, block);
      if i % 12 == 0 {
        assert_eq!(pt.mngr().num_pages(), i / 12);
        assert_eq!(pt.mngr().num_free_pages(), 0);
      }
    }

    assert_eq!(pt.mngr().num_pages(), MAX_DATA_PAGES);
    assert_eq!(pt.mngr().num_free_pages(), 0);

    // The next put will result in page rebalancing.
    let block = pt.next_block_id();
    blocks.push(block);
    pt.put(block, block);

    let num_pages = 1 /* meta page */ + 13 /* root data pages */ + 1 /* overflow page */;
    let num_free_pages = 6;
    assert_eq!(pt.mngr().num_pages(), num_pages + num_free_pages);
    assert_eq!(pt.mngr().num_free_pages(), num_free_pages);

    // When we delete pages, those pages need to be reclaimed by the storage manager.

    // Initially, delete all but the last page. This should result in 1 meta page and 1 data page
    // that contains the last block id.
    for &block in blocks[..blocks.len() - 1].iter().rev() {
      assert!(pt.del(block));
    }

    assert_eq!(pt.mngr().num_pages(), num_pages + num_free_pages);
    assert_eq!(
      pt.mngr().num_free_pages(),
      num_pages + num_free_pages - 1 /* meta page */ - 1 /* data page */
    );
    assert_eq!(pt.get(blocks[blocks.len() - 1]), Some(block));

    // Finally, delete the remaining block, storage manager should reclaim all of the pages.
    assert!(pt.del(block));
    assert_eq!(pt.mngr().num_pages(), 0);
    assert_eq!(pt.mngr().num_free_pages(), 0);
  }

  //==============
  // Fuzzing tests
  //==============

  #[test]
  fn test_table_fuzz_data_page_set_get_data_del() {
    let len = 200_000;
    let mut input = Vec::with_capacity(len);

    let mut rng = thread_rng();
    for _ in 0..len {
      let mut value = rng.gen::<u32>();
      while !valid_key(value) {
        value = rng.gen::<u32>();
      }
      input.push(value);
    }

    let mut buf = vec![0u8; 1024 * 1024]; // 1MB page
    init_header(buf.as_mut());

    for &elem in &input[..] {
      data_set(&mut buf, elem, elem);
    }

    assert!(get_count(&buf) as f64 == buf.len() as f64 / 8f64 * TABLE_MAX_LOAD);

    for i in 0..get_count(&buf) as usize {
      assert_eq!(data_get(&buf, input[i]), Some(input[i]));
    }

    for &elem in &input[..] {
      data_del(&mut buf, elem);
    }

    assert_eq!(get_count(&buf), 0);

    for &elem in &input[..] {
      assert_eq!(data_get(&buf, elem), None);
    }
  }

  #[test]
  fn test_table_fuzz_meta_page_set_get_data_del() {
    let len = 200_000;
    let mut input = Vec::with_capacity(len);

    let mut rng = thread_rng();
    for _ in 0..len {
      let mut value = rng.gen::<u32>();
      while !valid_key(value) {
        value = rng.gen::<u32>();
      }
      input.push(value);
    }

    let mut buf = vec![0u8; 1024 * 1024]; // 1MB page
    init_header(&mut buf);
    set_is_data_page(&mut buf, false);
    set_hash_func(&mut buf, 1);

    for &elem in &input[..] {
      meta_set(&mut buf, elem, elem);
    }

    let count = get_count(&buf) as usize;
    assert!(count > 0 && count < input.len());

    for &elem in &input[..] {
      assert!(meta_get(&buf, elem).is_some());
    }

    for &elem in &input[..] {
      meta_del(&mut buf, elem);
    }

    for &elem in &input[..] {
      assert_eq!(meta_get(&buf, elem), None);
    }

    assert_eq!(get_count(&buf), 0);
  }

  #[test]
  fn test_table_fuzz_page_table_set_get_del() {
    let len = 200_000;
    let mut input = Vec::with_capacity(len);

    let mut rng = thread_rng();
    for _ in 0..len {
      let mut value = rng.gen::<u32>();
      while !valid_key(value) {
        value = rng.gen::<u32>();
      }
      input.push(value);
    }

    let opts = Options::new().as_mem(0).with_page_size(4096).build(); // 4KB page
    let mngr = StorageManager::new(&opts);
    let mut pt = PageTable::new(mngr);

    for &elem in &input[..] {
      pt.put(elem, elem);
    }

    assert!(pt.root.is_some());

    for &elem in &input[..] {
      assert_eq!(pt.get(elem), Some(elem));
    }

    let mut deleted = HashSet::new();
    for &elem in &input[..] {
      assert_eq!(pt.del(elem), !deleted.contains(&elem));
      deleted.insert(elem);
    }

    assert!(pt.root.is_none());
  }
}
