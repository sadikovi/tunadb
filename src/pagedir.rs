use std::io::Write;
use crate::storage::{INVALID_PAGE_ID, StorageManager};

// leaf node: [<header>, data]
// intr node: [<header>, data]
// header: [<is_leaf 1 byte>, <num_keys 3 bytes>, <ptr0 4 bytes>, <reserved 8 bytes>]
// min keys: max keys / 2
// max keys: (page size - header) / 8

const HEADER_SIZE: usize = 16;

#[inline]
fn get_max_keys(page_size: usize) -> usize {
  assert!((page_size - 1) & page_size == 0, "Page size {} is not a power of 2", page_size);
  assert!(page_size >= 2 * HEADER_SIZE, "Page size {} is too small", page_size);
  (page_size - HEADER_SIZE) / 8 /* entry size */
}

#[inline]
fn get_min_keys(page_size: usize) -> usize {
  let max_keys = get_max_keys(page_size);
  max_keys / 2
}

#[inline]
fn is_leaf(buf: &[u8]) -> bool {
  buf[0] == 1
}

#[inline]
fn set_is_leaf(buf: &mut [u8], flag: bool) {
  buf[0] = flag as u8
}

#[inline]
fn num_keys(buf: &[u8]) -> usize {
  let tmp = [buf[1], buf[2], buf[3], 0];
  u8_u32!(&tmp) as usize
}

#[inline]
fn set_num_keys(buf: &mut [u8], cnt: usize) {
  let tmp = u32_u8!(cnt as u32);
  buf[1] = tmp[0];
  buf[2] = tmp[1];
  buf[3] = tmp[2];
  assert_eq!(tmp[3], 0, "Count {} is too large", cnt);
}

#[inline]
fn next_leaf(buf: &[u8]) -> Option<u32> {
  let page = u8_u32!(buf[..HEADER_SIZE][4..8]);
  if page != INVALID_PAGE_ID { Some(page) } else { None }
}

#[inline]
fn set_next_leaf(buf: &mut [u8], page: Option<u32>) {
  res!((&mut buf[..HEADER_SIZE][4..8]).write(&u32_u8!(page.unwrap_or(INVALID_PAGE_ID))));
}

#[inline]
fn get_key(buf: &[u8], pos: usize) -> u32 {
  u8_u32!(&buf[HEADER_SIZE..][pos * 8..pos * 8 + 4])
}

#[inline]
fn set_key(buf: &mut [u8], pos: usize, item: u32) {
  res!((&mut buf[HEADER_SIZE..][pos * 8..pos * 8 + 4]).write(&u32_u8!(item)));
}

#[inline]
fn get_val(buf: &[u8], pos: usize) -> u32 {
  u8_u32!(&buf[HEADER_SIZE..][pos * 8 + 4..pos * 8 + 8])
}

#[inline]
fn set_val(buf: &mut [u8], pos: usize, item: u32) {
  res!((&mut buf[HEADER_SIZE..][pos * 8 + 4..pos * 8 + 8]).write(&u32_u8!(item)));
}

#[inline]
fn get_ptr(buf: &[u8], pos: usize) -> u32 {
  if pos == 0 {
    u8_u32!(buf[..HEADER_SIZE][4..8])
  } else {
    get_val(buf, pos - 1)
  }
}

#[inline]
fn set_ptr(buf: &mut [u8], pos: usize, item: u32) {
  if pos == 0 {
    res!((&mut buf[..HEADER_SIZE][4..8]).write(&u32_u8!(item)));
  } else {
    set_val(buf, pos - 1, item);
  }
}

// Returns true if key exists and position to insert
#[inline]
fn bsearch(buf: &[u8], key: u32) -> (bool, usize) {
  let mut start = 0;
  let mut end = num_keys(buf);
  // "start" would point to the insertion point where keys[start] >= key
  while start < end {
    let pivot = (start + end - 1) >> 1;
    let pivot_key = get_key(buf, pivot);
    if key < pivot_key {
      end = pivot;
    } else if key > pivot_key {
      start = pivot + 1;
    } else {
      return (true, pivot);
    }
  }
  (false, start)
}

#[inline]
fn insert(buf: &mut [u8], pos: usize, key: u32, val: u32) {
  assert!(is_leaf(&buf));
  let len = num_keys(&buf);
  for i in (pos..len).rev() {
    let k = get_key(&buf, i);
    let v = get_val(&buf, i);
    set_key(buf, i + 1, k);
    set_val(buf, i + 1, v);
  }
  set_key(buf, pos, key);
  set_val(buf, pos, val);
  set_num_keys(buf, len + 1);
}

#[inline]
fn delete(buf: &mut [u8], pos: usize) {
  assert!(is_leaf(&buf));
  let len = num_keys(&buf);
  for i in pos + 1..len {
    let k = get_key(&buf, i);
    let v = get_val(&buf, i);
    set_key(buf, i - 1, k);
    set_val(buf, i - 1, v);
  }
  set_num_keys(buf, len - 1);
}

// Moves values from right to left.
#[inline]
fn merge(parent: &mut [u8], right_pos: usize, left: &mut [u8], right: &mut [u8]) {
  assert_eq!(is_leaf(&left), is_leaf(&right));
  let left_len = num_keys(&left);
  let right_len = num_keys(&right);

  if is_leaf(&left) {
    for i in 0..right_len {
      set_key(left, left_len + i, get_key(&right, i));
      set_val(left, left_len + i, get_val(&right, i));
    }
    set_num_keys(left, left_len + right_len);
  } else {
    set_key(left, left_len, get_key(&parent, right_pos));
    for i in 0..right_len {
      set_key(left, left_len + 1 + i, get_key(&right, i));
    }
    for i in 0..right_len + 1 {
      set_ptr(left, left_len + 1 + i, get_ptr(&right, i));
    }
    set_num_keys(left, left_len + 1 + right_len);
  }

  let parent_len = num_keys(&parent);
  for i in right_pos + 1..parent_len {
    let k = get_key(&parent, i);
    set_key(parent, i - 1, k);
  }
  for i in right_pos + 2..parent_len + 1 {
    let p = get_ptr(&parent, i);
    set_ptr(parent, i - 1, p);
  }
  set_num_keys(parent, parent_len - 1);
}

//===================
// B+ Tree operations
//===================

fn btree_find(mut root: u32, key: u32, buf: &mut [u8], mngr: &mut StorageManager) -> Option<u32> {
  loop {
    mngr.read(root, buf);
    let (exists, pos) = bsearch(&buf, key);
    if is_leaf(&buf) {
      return if exists { Some(get_val(&buf, pos)) } else { None };
    } else {
      root = get_ptr(&buf, if exists { pos + 1 } else { pos });
    }
  }
}

fn btree_put_recur(root: u32, key: u32, val: u32, max_keys: usize, buf: &mut [u8], mngr: &mut StorageManager) -> Option<(u32, u32, u32)> {
  mngr.read(root, buf);
  let (exists, pos) = bsearch(&buf, key);
  if is_leaf(&buf) {
    if exists {
      set_val(buf, pos, val);
      mngr.write(root, buf);
      None
    } else {
      insert(buf, pos, key, val);
      let len = num_keys(&buf);
      if len < max_keys {
        mngr.write(root, buf);
        None
      } else {
        let split_pos = len / 2 + (len & 1); // len / 2 + (len % 2 == 0) ? 0 : 1
        // If the key is inserted into split position, it becomes the split key.
        let split_key = if pos == split_pos { key } else { get_key(&buf, split_pos) };
        // Create two pages for split.
        let mut left = vec![0u8; buf.len()];
        set_is_leaf(&mut left, true);
        for i in 0..split_pos {
          set_key(&mut left, i, get_key(&buf, i));
          set_val(&mut left, i, get_val(&buf, i));
        }
        set_num_keys(&mut left, split_pos);

        let mut right = vec![0u8; buf.len()];
        set_is_leaf(&mut right, true);
        for i in 0..len - split_pos {
          set_key(&mut right, i, get_key(&buf, split_pos + i));
          set_val(&mut right, i, get_val(&buf, split_pos + i));
        }
        set_num_keys(&mut right, len - split_pos);

        let left_id = mngr.write_next(&mut left);
        let right_id = mngr.write_next(&mut right);
        mngr.mark_as_free(root);

        Some((split_key, left_id, right_id))
      }
    }
  } else {
    let ptr_pos = if exists { pos + 1 } else { pos };
    let mut cbuf = vec![0u8; buf.len()]; // clone buffer so we don't have to re-read data
    match btree_put_recur(get_ptr(&buf, ptr_pos), key, val, max_keys, &mut cbuf, mngr) {
      Some((child_key, left_id, right_id)) => {
        set_ptr(buf, pos, right_id);
        // Shift keys and pointers to make space for the child split key.
        let len = num_keys(&buf);
        for i in (pos..len).rev() {
          let k = get_key(&buf, i);
          set_key(buf, i + 1, k);
        }
        set_key(buf, pos, child_key);

        for i in (pos..len + 1).rev() {
          let p = get_ptr(&buf, i);
          set_ptr(buf, i + 1, p);
        }
        set_ptr(buf, pos, left_id);
        let len = len + 1;
        set_num_keys(buf, len);

        if len < max_keys {
          mngr.write(root, buf);
          None // we do not need to propagate results
        } else {
          let split_pos = len / 2 + (len & 1); // len / 2 + (len % 2 == 0) ? 0 : 1
          let split_key = get_key(&buf, split_pos);

          let mut left = vec![0u8; buf.len()];
          set_is_leaf(&mut left, false);
          for i in 0..split_pos {
            set_key(&mut left, i, get_key(&buf, i));
            set_ptr(&mut left, i, get_ptr(&buf, i));
          }
          set_ptr(&mut left, split_pos, get_ptr(&buf, split_pos));
          set_num_keys(&mut left, split_pos);

          let mut right = vec![0u8; buf.len()];
          set_is_leaf(&mut right, false);
          for i in split_pos + 1..len {
            set_key(&mut right, i - split_pos - 1, get_key(&buf, i));
            set_ptr(&mut right, i - split_pos - 1, get_ptr(&buf, i));
          }
          set_ptr(&mut right, len - split_pos - 1, get_ptr(&buf, len));
          set_num_keys(&mut right, len - split_pos - 1);

          let left_id = mngr.write_next(&mut left);
          let right_id = mngr.write_next(&mut right);
          mngr.mark_as_free(root);

          Some((split_key, left_id, right_id))
        }
      },
      // Do nothing, the key was inserted successfully without splitting.
      None => None,
    }
  }
}

fn btree_put(key: u32, val: u32, max_keys: usize, buf: &mut [u8], mngr: &mut StorageManager) {
  match mngr.page_table_root() {
    Some(root) => {
      match btree_put_recur(root, key, val, max_keys, buf, mngr) {
        Some((child_key, left_id, right_id)) => {
          buf.fill(0);
          // Root page will always be internal after splitting.
          set_is_leaf(buf, false);
          set_key(buf, 0, child_key);
          set_ptr(buf, 0, left_id);
          set_ptr(buf, 1, right_id);
          set_num_keys(buf, 1);

          let new_root = mngr.write_next(buf);
          mngr.update_page_table(Some(new_root));
          mngr.sync();
        },
        None => {
          // Do nothing, no need to update root.
        }
      }
    },
    None => {
      buf.fill(0);
      set_is_leaf(buf, true);
      insert(buf, 0, key, val);
      let new_root = mngr.write_next(buf);
      mngr.update_page_table(Some(new_root));
      mngr.sync();
    }
  }
}

// fn btree_delete_recur(root: u32, key: u32, min_keys: usize, buf: &mut [u8], mngr: &mut StorageManager) -> (usize, Option<u32>) {
//   mngr.read(root, buf);
//   let (exists, pos) = bsearch(&buf, key);
//   if is_leaf(&buf) {
//     if exists {
//       delete(buf, pos);
//       mngr.write(root, &buf);
//       let len = num_keys(&buf);
//       // We deleted the smallest key, update the next smallest key in parent nodes.
//       if pos == 0 && len > 0 {
//         return (len, Some(key));
//       }
//     }
//     (num_keys(&buf), None)
//   } else {
//     let ptr_pos = if exists { pos + 1 } else { pos };
//     let ptr = get_ptr(&buf, ptr_pos);
//     let mut cbuf1 = vec![0u8; buf.len()];
//     let (child_len, child_smallest_key) = btree_delete_recur(ptr, key, min_keys, &mut cbuf1, mngr);
//
//     let mut is_dirty = false; // whether or not `buf` requires write to disk
//
//     if exists && get_key(&buf, pos) == key {
//       if let Some(smallest_key) = child_smallest_key {
//         set_key(buf, pos, smallest_key);
//         is_dirty = true;
//       }
//     }
//
//     if child_len < min_keys {
//       is_dirty = true;
//
//       let mut cbuf2 = vec![0u8; buf.len()];
//
//       // Perform rebalancing of the child nodes.
//       if ptr_pos > 0 {
//         // Steal from ptr-1 to ptr => parent: buf, ptr-1: cbuf1, ptr: cbuf2.
//         mngr.read(get_ptr(&buf, ptr_pos - 1), &mut cbuf1);
//         let cbuf1_len = num_keys(&cbuf1);
//         if cbuf1_len > min_keys {
//           mngr.read(ptr, &mut cbuf2);
//
//           if is_leaf(&cbuf1) {
//             let k = get_key(&cbuf1, cbuf1_len - 1);
//             let v = get_val(&cbuf1, cbuf1_len - 1);
//             delete(&mut cbuf1, cbuf1_len - 1);
//             set_key(buf, ptr_pos - 1, k);
//             insert(&mut cbuf2, 0, k, v);
//           } else {
//             let k = get_key(&cbuf1, cbuf1_len - 1);
//             let p = get_ptr(&cbuf1, cbuf1_len);
//             set_num_keys(&mut cbuf1, cbuf1_len - 1);
//
//             let cbuf2_len = num_keys(&cbuf2);
//             for i in (0..cbuf2_len).rev() {
//               let k = get_key(&cbuf2, i);
//               set_key(&mut cbuf2, i + 1, k);
//             }
//             for i in (0..cbuf2_len + 1).rev() {
//               let p = get_ptr(&cbuf2, i);
//               set_ptr(&mut cbuf2, i + 1, p);
//             }
//             set_num_keys(&mut cbuf2, cbuf2_len + 1);
//
//             set_key(&mut cbuf2, 0, get_key(&buf, ptr_pos - 1));
//             set_key(&mut cbuf2, 0, p);
//             set_key(buf, ptr_pos - 1, k);
//           }
//         }
//       } else if ptr_pos < len {
//         // Steal from ptr+1 to ptr => parent: buf, ptr+1: cbuf1, ptr: cbuf2.
//         mngr.read(get_ptr(&buf, ptr_pos + 1), &mut cbuf1);
//         let cbuf1_len = num_keys(&cbuf1);
//         if cbuf1_len > min_keys {
//           mngr.read(ptr, &mut cbuf2);
//
//           if is_leaf(&cbuf1) {
//             let k = get_key(&cbuf1, 0);
//             let v = get_val(&cbuf1, 0);
//             delete(&mut cbuf1, 0);
//             set_key(buf, ptr_pos, get_key(&cbuf1, 0));
//             let cbuf2_len = num_keys(&cbuf2);
//             insert(&mut cbuf2, cbuf2_len, k, v);
//           } else {
//             let k = get_key(&cbuf1, 0);
//             let p = get_ptr(&cbuf1, 0);
//
//             for i in (1..cbuf1_len).rev() {
//               let k = get_key(&cbuf1, i);
//               set_key(&mut cbuf1, i - 1, k);
//             }
//             for i in (1..cbuf1_len + 1).rev() {
//               let p = get_ptr(&cbuf1, i);
//               set_ptr(&mut cbuf1, i - 1, p);
//             }
//             set_num_keys(&mut cbuf1, cbuf1_len - 1);
//
//             let cbuf2_len = num_keys(&cbuf2);
//             set_key(&mut cbuf2, cbuf2_len, get_key(&buf, ptr_pos));
//             set_ptr(&mut cbuf2, cbuf2_len + 1, p);
//             set_key(buf, ptr_pos, k);
//           }
//         }
//       } else if ptr_pos == 0 {
//         // Merge ptr and ptr+1 nodes => parent: buf, ptr: cbuf1, ptr+1: cbuf2
//         mngr.read(ptr, &mut cbuf1);
//         mngr.read(get_ptr(&buf, ptr_pos + 1), &mut cbuf2);
//         merge(buf, ptr_pos + 1, &mut cbuf1, &mut cbuf2);
//       } else {
//         // Merge ptr-1 and ptr nodes => parent: buf, ptr-1: cbuf1, ptr: cbuf2
//         mngr.read(get_ptr(&buf, ptr_pos - 1), &mut cbuf1);
//         mngr.read(ptr, &mut cbuf2);
//         merge(buf, ptr_pos, &mut cbuf1, &mut cbuf2);
//       }
//     }
//   }
// }

fn page_print(buf: &[u8]) {
  let len = num_keys(buf);
  println!("Page: ");
  println!("  count: {}", len);
  if is_leaf(buf) {
    for i in 0..len {
      println!("  {}: {}", get_key(buf, i), get_val(buf, i));
    }
  } else {
    println!("        {}", get_ptr(buf, 0));
    for i in 0..len {
      println!("  > {}: {}", get_key(buf, i), get_ptr(buf, i + 1));
    }
  }
}

fn btree_print(root: u32, buf: &mut [u8], mngr: &mut StorageManager, offset: usize) {
  mngr.read(root, buf);
  let cnt = num_keys(&buf);
  if is_leaf(&buf) {
    println!("{:>width$} {} | cnt: {} | min: {} | max: {}",
      "*", root, cnt, get_key(&buf, 0), get_key(&buf, cnt - 1), width = offset);
  } else {
    println!("{:>width$} {} | cnt: {} | min: {} | max: {}",
      "+", root, cnt, get_key(&buf, 0), get_key(&buf, cnt - 1), width = offset);
    let cbuf = buf.to_vec();
    for i in 0..cnt + 1 {
      btree_print(get_ptr(&cbuf, i), buf, mngr, offset + 2);
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::storage::Options;

  #[test]
  fn test_pagedir_debug() {
    let page_size = 128 as usize;
    let mut mngr = StorageManager::new(&Options::new().as_mem(0).with_page_size(page_size as u32).build());
    let mut buf = vec![0u8; page_size];
    for i in 1..500 {
      btree_put(i, i * 10, get_max_keys(page_size), &mut buf, &mut mngr);
    }
    btree_print(mngr.page_table_root().unwrap(), &mut buf, &mut mngr, 4);

    mngr.sync(); // TODO: we need to call sync for some reason
    println!("Storage # num pages: {}, free pages: {}", mngr.num_pages(), mngr.num_free_pages());
    assert!(false, "OK");
  }

  #[test]
  #[should_panic(expected = "Page size 127 is not a power of 2")]
  fn test_pagedir_min_max_keys_invalid_page_size() {
    get_max_keys(127);
  }

  #[test]
  fn test_pagedir_min_max_keys() {
    let max_keys = get_max_keys(128);
    let min_keys = get_min_keys(128);
    assert_eq!(max_keys, 14);
    assert_eq!(min_keys, 7);
  }

  #[test]
  fn test_pagedir_is_leaf() {
    let mut buf = vec![0u8; 16];
    assert!(!is_leaf(&buf));

    set_is_leaf(&mut buf, true);
    assert!(is_leaf(&buf));

    set_is_leaf(&mut buf, false);
    assert!(!is_leaf(&buf));
  }

  #[test]
  fn test_pagedir_num_keys() {
    let mut buf = vec![0u8; 16];
    assert_eq!(num_keys(&buf), 0);

    set_num_keys(&mut buf, 123);
    assert_eq!(num_keys(&buf), 123);

    set_num_keys(&mut buf, 120_000);
    assert_eq!(num_keys(&buf), 120_000);

    set_num_keys(&mut buf, (1 << 24) - 1);
    assert_eq!(num_keys(&buf), (1 << 24) - 1);
  }

  #[test]
  #[should_panic(expected = "Count 16777216 is too large")]
  fn test_pagedir_num_keys_invalid_count() {
    let mut buf = vec![0u8; 16];
    set_num_keys(&mut buf, 1 << 24);
  }

  #[test]
  fn test_pagedir_next_leaf() {
    let mut buf = vec![0u8; 128];

    set_next_leaf(&mut buf, None);
    assert_eq!(next_leaf(&buf), None);

    set_next_leaf(&mut buf, Some(123));
    assert_eq!(next_leaf(&buf), Some(123));
  }

  #[test]
  fn test_pagedir_get_set_key() {
    let max_keys = get_max_keys(128);
    let mut buf = vec![0u8; 128];
    set_num_keys(&mut buf, max_keys);

    for i in 0..max_keys {
      set_key(&mut buf, i, i as u32);
    }

    for i in 0..max_keys {
      assert_eq!(get_key(&buf, i), i as u32);
    }
  }

  #[test]
  fn test_pagedir_get_set_val() {
    let max_keys = get_max_keys(128);
    let mut buf = vec![0u8; 128];
    set_num_keys(&mut buf, max_keys);

    for i in 0..max_keys {
      set_val(&mut buf, i, i as u32);
    }

    for i in 0..max_keys {
      assert_eq!(get_val(&buf, i), i as u32);
    }
  }

  #[test]
  fn test_pagedir_get_set_ptr() {
    let max_keys = get_max_keys(128);
    let mut buf = vec![0u8; 128];
    set_num_keys(&mut buf, max_keys);

    for i in 0..max_keys + 1 {
      set_ptr(&mut buf, i, i as u32);
    }

    for i in 0..max_keys + 1 {
      assert_eq!(get_ptr(&buf, i), i as u32);
    }
  }

  #[test]
  fn test_pagedir_bsearch() {
    let max_keys = get_max_keys(128);
    let mut buf = vec![0u8; 128];
    set_num_keys(&mut buf, max_keys);

    for i in 0..max_keys {
      set_key(&mut buf, i, (i * 2) as u32);
    }

    for i in 0..max_keys {
      assert_eq!(bsearch(&buf, (i * 2) as u32), (true, i));
    }

    assert_eq!(bsearch(&buf, 1), (false, 1));
    assert_eq!(bsearch(&buf, 5), (false, 3));
    assert_eq!(bsearch(&buf, 100), (false, 14));
  }

  #[test]
  fn test_pagedir_insert() {
    let mut buf = vec![0u8; 128];
    set_is_leaf(&mut buf, true);

    for i in 1..15 {
      let cnt = num_keys(&buf);
      insert(&mut buf, cnt, i, i);
      assert_eq!(cnt + 1, num_keys(&buf));
    }

    for i in 0..14 {
      assert_eq!(get_key(&buf, i), i as u32 + 1);
      assert_eq!(get_val(&buf, i), i as u32 + 1);
    }
  }

  #[test]
  fn test_pagedir_delete() {
    let mut buf = vec![0u8; 128];
    set_is_leaf(&mut buf, true);

    for i in 1..15 {
      let cnt = num_keys(&buf);
      insert(&mut buf, cnt, i, i);
      assert_eq!(cnt + 1, num_keys(&buf));
    }

    for i in 0..14 {
      delete(&mut buf, i);
    }

    assert_eq!(num_keys(&buf), 0);
  }
}
