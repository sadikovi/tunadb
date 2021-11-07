use std::io::Write;
use crate::error::Res;
use crate::storage::StorageManager;

// Block id representing an empty slot
const EMPTY: u32 = 0;
// Block id representing a deleted entry in the table
const TOMBSTONE: u32 = u32::MAX;
// Block id representing a reserved key-value pair (header info)
const RESERVED: u32 = u32::MAX - 1;

const TABLE_MAX_LOAD: f64 = 0.75;
const MAX_DATA_PAGES: usize = 6;

const FLAG_IS_DATA_PAGE: u32 = 0x1;
const FLAG_HAS_OVERFLOW: u32 = 0x2;

const HASH_FUNC_CNT: usize = 4; // Must be a power of 2
const HASH_FUNC_CNT_MINUS_1: usize = HASH_FUNC_CNT - 1;
const HASH_FUNC: [fn(u32) -> u32; HASH_FUNC_CNT] = [hash_func1, hash_func2, hash_func3, hash_func4];

// Hash functions:

// https://burtleburtle.net/bob/hash/integer.html
// Full avalanche
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

// Full avalanche
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

// Full avalanche
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

// Half avalanche
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

// Hash table operations

#[inline]
fn init_header(buf: &mut [u8]) {
  (&mut buf[0..4]).write(&u32_u8!(RESERVED)).unwrap();
  (&mut buf[4..8]).write(&u32_u8!(FLAG_IS_DATA_PAGE)).unwrap(); // flags
  (&mut buf[8..12]).write(&u32_u8!(RESERVED)).unwrap();
  (&mut buf[12..16]).write(&u32_u8!(0u32)).unwrap(); // count
  (&mut buf[16..20]).write(&u32_u8!(RESERVED)).unwrap();
  (&mut buf[20..24]).write(&u32_u8!(0u32)).unwrap(); // (data) overflow page | (meta) hash func
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
fn get_hash_func(buf: &[u8]) -> usize {
  u8_u32!(&buf[20..24]) as usize
}

#[inline]
fn set_hash_func(buf: &mut [u8], hash_func: usize) {
  (&mut buf[20..24]).write(&u32_u8!(hash_func as u32)).unwrap();
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
      // We found an empty entry, return either previously found tombstone or the position itself
      return (tombstone.unwrap_or(pos), None);
    } else if entry == TOMBSTONE {
      // We found a tombstone, record the position and keep moving
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
  assert!((buf.len() - 1) & buf.len() == 0, "Table length is not power of 2");
  assert!(buf.len() >= 8, "Table length needs to be at least 8 bytes");
  assert!(valid_key(key), "Unsupported key: {}", key);

  let len_minus_1 = buf.len() - 1;
  let size_minus_1 = (buf.len() >> 3) - 1; // len / 8 - 1

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
  pos: usize,
  buf: &'a [u8],
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
  KeyValueIter { pos: 0, buf }
}

// Page table operations

// Creates new data page.
#[inline]
fn create_new(buf: &mut[u8], key: u32, value: u32, mngr: &mut StorageManager) -> Res<u32> {
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
) -> Res<bool> {
  assert!(is_data_page(&buf));

  let mut depth = 0;
  loop {
    if data_set(buf, key, value) {
      mngr.write(page_id, &buf)?;
      return Ok(true); // the value was inserted into the current page
    } else if let Some(overflow_page_id) = get_overflow_page(&buf) {
      page_id = overflow_page_id;
      mngr.read(page_id, buf)?;
      assert!(is_data_page(&buf));
      depth += 1;
    } else if depth + 1 < MAX_DATA_PAGES {
      // Create a new page, insert the value
      let mut new_buf = vec![0u8; buf.len()];
      let overflow_page_id = create_new(&mut new_buf, key, value, mngr)?;
      // Update the current page with the overflow
      set_overflow_page(buf, overflow_page_id);
      mngr.write(page_id, &buf)?;
      return Ok(true); // the value was inserted into the overflow page
    } else {
      return Ok(false);
    }
  }
}

// Rebalances pages and inserts the key-value pair.
// Returns a new page id.
fn rebalance(
  mut root: u32,
  buf: &mut[u8],
  key: u32, value: u32,
  hash_func: usize,
  mngr: &mut StorageManager
) -> Res<u32> {
  let mut meta_buf = vec![0u8; buf.len()];
  // Create a new meta page
  init_header(&mut meta_buf);
  set_is_data_page(&mut meta_buf, false);
  set_hash_func(&mut meta_buf, hash_func);

  let mut all_keys = Vec::new();
  all_keys.push((key, value));

  let mut free_pages = Vec::with_capacity(MAX_DATA_PAGES);

  loop {
    mngr.read(root, buf)?;
    free_pages.push(root);
    let overflow = get_overflow_page(&buf);
    // Iterate over the keys in the page
    let mut iter = key_value_iter(&buf);
    while let Some(pair) = iter.next() {
      all_keys.push(pair);
    }

    for &(k, v) in &all_keys {
      if let Some(next) = meta_get(&meta_buf, k) {
        mngr.read(next, buf)?;
        assert!(insert_data(next, buf, k, v, mngr)?);
      } else {
        buf.fill(0);
        let next_page = create_new(buf, k, v, mngr)?;
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

  let meta_page = mngr.write_next(&mut meta_buf)?;

  // TODO: We don't particularly care if free calls fail, maybe we can ignore the Res.
  for free_page in free_pages {
    mngr.free(free_page)?;
  }
  Ok(meta_page)
}

// Returns the existing page id if the root has not changed, otherwise a new page id is returned.
fn insert(
  root: u32,
  buf: &mut[u8],
  key: u32,
  value: u32,
  depth: usize,
  mngr: &mut StorageManager
) -> Res<u32> {
  let hash_func = depth & HASH_FUNC_CNT_MINUS_1;

  mngr.read(root, buf)?;

  if is_data_page(&buf) {
    if insert_data(root, buf, key, value, mngr)? {
      Ok(root)
    } else {
      let new_root = rebalance(root, buf, key, value, hash_func, mngr)?;
      Ok(new_root)
    }
  } else if let Some(next) = meta_get(&buf, key) {
    let new_next = insert(next, buf, key, value, depth + 1, mngr)?;
    if new_next != next {
      mngr.read(root, buf)?;
      meta_set(buf, key, new_next);
      mngr.write(root, &buf)?;
    }
    Ok(root)
  } else {
    // There is no such next page in the meta page, so we need to create one and add the key
    // to the meta page
    let mut new_buf = vec![0u8; buf.len()];
    let next_page = create_new(&mut new_buf, key, value, mngr)?;
    meta_set(buf, key, next_page);
    mngr.write(root, &buf)?;
    Ok(root) // root has not changed
  }
}

fn delete_data(root: u32, buf: &mut [u8], key: u32, mngr: &mut StorageManager) -> Res<(Option<u32>, bool)> {
  assert!(is_data_page(&buf));

  let mut maybe_parent = None;
  let mut curr = root;
  let mut delete_ok = false;

  loop {
    if data_del(buf, key) {
      mngr.write(curr, &buf)?;
      delete_ok = true;
      break;
    }

    if let Some(overflow) = get_overflow_page(&buf) {
      maybe_parent = Some(curr);
      curr = overflow;
      mngr.read(curr, buf)?;
    } else {
      break;
    }
  };

  // Perform rebalancing for the data page chain
  if get_count(&buf) > 0 {
    Ok((Some(root), delete_ok))
  } else {
    let maybe_overflow = get_overflow_page(&buf);
    if let Some(parent) = maybe_parent {
      mngr.read(parent, buf)?;
      if let Some(overflow) = maybe_overflow {
        set_overflow_page(buf, overflow);
      } else {
        unset_overflow_page(buf);
      }
      // TODO: Free the current page
      mngr.write(parent, buf)?;
      Ok((Some(root), delete_ok))
    } else {
      // Deleting the root page of the chain
      // TODO: Free the current page
      Ok((maybe_overflow, delete_ok))
    }
  }
}

fn delete(root: u32, buf: &mut[u8], key: u32, mngr: &mut StorageManager) -> Res<(Option<u32>, bool)> {
  mngr.read(root, buf)?;

  if is_data_page(&buf) {
    let res = delete_data(root, buf, key, mngr)?;
    Ok(res)
  } else if let Some(next) = meta_get(&buf, key) {
    let (maybe_new_page, delete_ok) = delete(next, buf, key, mngr)?;
    if let Some(new_page) = maybe_new_page {
      if new_page != next {
        mngr.read(root, buf)?;
        meta_set(buf, key, new_page);
        mngr.write(root, &buf)?;
      }
      Ok((Some(root), delete_ok))
    } else {
      mngr.read(root, buf)?;
      meta_del(buf, key);
      mngr.write(root, &buf)?;
      if get_count(&buf) == 0 {
        // TODO: Free the current page
        Ok((None, delete_ok))
      } else {
        Ok((Some(root), delete_ok))
      }
    }
  } else {
    // No such key
    Ok((Some(root), false))
  }
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

  pub fn get(&mut self, key: u32) -> Res<Option<u32>> {
    match self.root {
      Some(mut root) => {
        loop {
          self.mngr.read(root, &mut self.buf)?;
          if is_data_page(&self.buf) {
            let res = data_get(&self.buf, key);
            if res.is_some() {
              return Ok(res);
            }
            if let Some(overflow) = get_overflow_page(&self.buf) {
              root = overflow;
            } else {
              return Ok(None);
            }
          } else if let Some(next) = meta_get(&self.buf, key) {
            root = next;
          } else {
            return Ok(None);
          }
        }
      },
      None => Ok(None),
    }
  }

  pub fn put(&mut self, key: u32, value: u32) -> Res<()> {
    let new_root = match self.root {
      Some(root) => insert(root, &mut self.buf, key, value, 1, &mut self.mngr)?,
      None => {
        self.buf.fill(0);
        create_new(&mut self.buf, key, value, &mut self.mngr)?
      },
    };

    if Some(new_root) != self.root {
      self.root = Some(new_root);
      self.mngr.update_page_table(self.root, self.max_block_id)?;
    }
    self.mngr.sync()
  }

  pub fn del(&mut self, key: u32) -> Res<bool> {
    let (new_root, delete_ok) = match self.root {
      Some(root) => delete(root, &mut self.buf, key, &mut self.mngr)?,
      None => (None, false),
    };

    if new_root != self.root {
      self.root = new_root;
      self.mngr.update_page_table(self.root, self.max_block_id)?;
    }
    self.mngr.sync()?;
    Ok(delete_ok)
  }

  pub fn mngr(&self) -> &StorageManager {
    &self.mngr
  }
}

// For debugging only
fn fmt0(pt: &mut PageTable, root: u32, off: usize) {
  pt.mngr.read(root, &mut pt.buf).unwrap();
  if is_data_page(&pt.buf) {
    print!("{:width$}*[{}] ({})", "", root, get_count(&pt.buf), width = off);
    if let Some(overflow) = get_overflow_page(&pt.buf) {
      print!(" ->");
      fmt0(pt, overflow, 1);
    } else {
      println!();
    }
  } else {
    let mut iter = key_value_iter(&pt.buf);
    let mut values = Vec::new();
    while let Some((_, v)) = iter.next() {
      values.push(v);
    }
    let hash_func = get_hash_func(&pt.buf);
    println!("{:width$}#[{}] ({}) hash({})", "", root, values.len(), hash_func, width = off);
    for &v in &values {
      fmt0(pt, v, off + 2);
    }
  }
}

pub fn fmt(pt: &mut PageTable) {
  println!("PageTable(root: {:?}, max block: {})", pt.root, pt.max_block_id);
  if let Some(root) = pt.root {
    fmt0(pt, root, 0);
  }
  println!("Storage: {} pages, {} free pages, {} mem",
    pt.mngr().num_pages().unwrap(),
    pt.mngr().num_free_pages().unwrap(),
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

  #[test]
  fn test_table_debug() {
    let opts = Options::new().as_mem(0).with_page_size(128).build().unwrap();
    let mngr = StorageManager::new(&opts).unwrap();
    let mut pt = PageTable::new(mngr);

    for i in 1..501 {
      // let block = pt.next_block_id();
      pt.put(i, i).unwrap();
    }

    fmt(&mut pt);

    for i in (1..501).rev() {
      // println!();
      // println!("Deleting key {}", i);
      assert!(pt.del(i).unwrap());
      // fmt(&mut pt);
    }

    fmt(&mut pt);

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

  // Meta page tests

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
  fn test_table_meta_page_set_hash_func() {
    let mut buf = vec![0u8; 128];
    init_header(&mut buf);
    assert_eq!(get_hash_func(&buf), 0);

    set_hash_func(&mut buf, 1);
    assert_eq!(get_hash_func(&buf), 1);

    set_hash_func(&mut buf, 4);
    assert_eq!(get_hash_func(&buf), 4);
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
  fn test_table_put_get_correctness() {
    let opts = Options::new().as_mem(0).with_page_size(128).build().unwrap();
    let mngr = StorageManager::new(&opts).unwrap();
    let mut pt = PageTable::new(mngr);

    for i in 1..1000 {
      pt.put(i, i).unwrap();
    }

    for i in 1..1000 {
      assert_eq!(pt.get(i).unwrap(), Some(i));
    }

    for i in 1000..2000 {
      assert_eq!(pt.get(i).unwrap(), None);
    }
  }

  #[test]
  fn test_table_put_del_correctness() {
    let opts = Options::new().as_mem(0).with_page_size(128).build().unwrap();
    let mngr = StorageManager::new(&opts).unwrap();
    let mut pt = PageTable::new(mngr);

    for i in 1..1000 {
      pt.put(i, i).unwrap();
    }

    for i in 1000..2000 {
      assert!(!pt.del(i).unwrap());
    }

    for i in 1..1000 {
      assert!(pt.del(i).unwrap());
    }

    for i in 1..2000 {
      assert!(!pt.del(i).unwrap());
    }
  }

  #[test]
  fn test_table_page_allocation() {
    let opts = Options::new().as_mem(0).with_page_size(128).build().unwrap();
    let mngr = StorageManager::new(&opts).unwrap();
    let mut pt = PageTable::new(mngr);

    // We can only fit 12 key-value pairs in a 128 byte page
    // Our chain is MAX_DATA_PAGES long

    let mut blocks = Vec::new();

    for i in 1..12 * MAX_DATA_PAGES + 1 {
      let block = pt.next_block_id();
      blocks.push(block);
      pt.put(block, block).unwrap();
      if i % 12 == 0 {
        assert_eq!(pt.mngr().num_pages().unwrap(), i / 12);
        assert_eq!(pt.mngr().num_free_pages().unwrap(), 0);
      }
    }

    assert_eq!(pt.mngr().num_pages().unwrap(), MAX_DATA_PAGES);
    assert_eq!(pt.mngr().num_free_pages().unwrap(), 0);

    // The next put will result in page rebalancing
    let block = pt.next_block_id();
    pt.put(block, block).unwrap();

    let num_pages = 1 /* meta page */ + 13 /* root data pages */ + 1 /* overflow page */;
    let num_free_pages = 6;
    assert_eq!(pt.mngr().num_pages().unwrap() - num_free_pages, num_pages);
    assert_eq!(pt.mngr().num_free_pages().unwrap(), num_free_pages);

    // When we delete pages, those pages need to be reclaimed by the storage manager

    for &block in blocks.iter().rev() {
      assert!(pt.del(block).unwrap());
    }

    assert_eq!(pt.mngr().num_pages().unwrap(), 0);
    assert_eq!(pt.mngr().num_free_pages().unwrap(), 0);
  }

  // Fuzzing tests

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

    let opts = Options::new().as_mem(0).with_page_size(4096).build().unwrap(); // 4KB page
    let mngr = StorageManager::new(&opts).unwrap();
    let mut pt = PageTable::new(mngr);

    for &elem in &input[..] {
      pt.put(elem, elem).unwrap();
    }

    assert!(pt.root.is_some());

    for &elem in &input[..] {
      assert_eq!(pt.get(elem).unwrap(), Some(elem));
    }

    let mut deleted = HashSet::new();
    for &elem in &input[..] {
      assert_eq!(pt.del(elem).unwrap(), !deleted.contains(&elem));
      deleted.insert(elem);
    }

    assert!(pt.root.is_none());
  }
}
