use crate::storage::{INVALID_PAGE_ID, StorageManager};
use crate::page as pg;

// Inserts key and value in the btree and returns a new snapshot via a new root page.
pub fn put(root: u32, key: &[u8], val: &[u8], mngr: &mut StorageManager) -> u32 {
  let mut page = vec![0u8; mngr.page_size()];
  match recur_put(root, &key, &val, mngr, &mut page) {
    BTreePut::Update(id) => id,
    BTreePut::Split(left_id, right_id, key) => {
      // Root page will always be internal after splitting and will only have two values.
      pg::internal_init(&mut page);
      pg::internal_insert(&mut page, 0, &key, mngr);
      pg::internal_set_ptr(&mut page, 0, left_id);
      pg::internal_set_ptr(&mut page, 1, right_id);
      mngr.write_next(&page)
    },
  }
}

enum BTreePut {
  Update(u32 /* page id */),
  Split(u32 /* left page id */, u32 /* right page id */, Vec<u8> /* split key */)
}

// Puts key and value into btree.
fn recur_put(root: u32, key: &[u8], val: &[u8], mngr: &mut StorageManager, page: &mut [u8]) -> BTreePut {
  if root == INVALID_PAGE_ID {
    // Create new leaf page
    pg::leaf_init(page);
    pg::leaf_can_insert(&page, key, val);
    pg::leaf_insert(page, 0, key, val, mngr);
    BTreePut::Update(mngr.write_next(&page))
  } else {
    mngr.read(root, page);
    let (pos, exists) = pg::bsearch(&page, key, mngr);
    match pg::page_type(&page) {
      pg::PageType::Leaf => {
        if exists || pg::leaf_can_insert(&page, key, val) {
          if exists {
            // TODO: optimise page updates
            pg::leaf_delete(page, pos, mngr);
          }
          pg::leaf_insert(page, pos, key, val, mngr);

          let new_root = mngr.write_next(&page);
          mngr.mark_as_free(root);
          BTreePut::Update(new_root)
        } else {
          // We need to split the leaf page.
          let num_slots = pg::num_slots(&page);
          // Split point.
          let spos = num_slots / 2;
          // Split key.
          let skey = if pos == spos { key.to_vec() } else { pg::leaf_get_key(&page, spos, mngr) };

          let mut right_page = vec![0u8; mngr.page_size()];
          pg::leaf_init(&mut right_page);
          pg::leaf_split(page, &mut right_page, spos);

          if pos >= spos {
            pg::leaf_insert(&mut right_page, pos - spos, key, val, mngr);
          } else {
            pg::leaf_insert(page, pos, key, val, mngr);
          }

          let left_pid = mngr.write_next(&page);
          let right_pid = mngr.write_next(&right_page);
          mngr.mark_as_free(root);
          BTreePut::Split(left_pid, right_pid, skey)
        }
      },
      pg::PageType::Internal => {
        let mut right_page = page.to_vec(); // we reuse right_page as a temporary buffer
        let ptr = if exists { pos + 1 } else { pos };

        match recur_put(pg::internal_get_ptr(&page, ptr), key, val, mngr, &mut right_page) {
          BTreePut::Update(id) => {
            pg::internal_set_ptr(page, ptr, id);
            let new_root = mngr.write_next(&page);
            mngr.mark_as_free(root);
            BTreePut::Update(new_root)
          },
          BTreePut::Split(left_id, right_id, key) => {
            if pg::internal_can_insert(&page, &key) {
              pg::internal_insert(page, pos, &key, mngr);
              pg::internal_set_ptr(page, pos, left_id);
              pg::internal_set_ptr(page, pos + 1, right_id);

              let new_root = mngr.write_next(&page);
              mngr.mark_as_free(root);
              BTreePut::Update(new_root)
            } else {
              // We need to split internal page.
              let num_slots = pg::num_slots(&page);
              // Split point.
              let spos = num_slots / 2;
              // Split key.
              let skey = pg::internal_get_key(&page, spos, mngr);

              pg::internal_init(&mut right_page);
              pg::internal_split(page, &mut right_page, spos, mngr);

              // Decide where to insert the split key.
              // Note that there must always be enough space to insert the key in either
              // left or right page.
              //
              // We chose to insert it into the left page because it is simpler.
              //
              //    0  1  2     3       4  5  6
              //    k0 k1 k2   [k3]     k4 k5 k6
              // p0 p1 p2 p3         p4 p5 p6 p7
              //
              // If pos == spos, the key could go into either page: it will be at pos 0 in the
              // right page and it will be at pos `num_slots` in the left page.
              // If we insert the key into the right page, we will need to another if case for it,
              // we don't need to have it when inserting into the left page.
              if pos > spos {
                pg::internal_insert(&mut right_page, pos - spos - 1, &key, mngr);
                pg::internal_set_ptr(&mut right_page, pos - spos - 1, left_id);
                pg::internal_set_ptr(&mut right_page, pos - spos, right_id);
              } else {
                pg::internal_insert(page, pos, &key, mngr);
                pg::internal_set_ptr(page, pos, left_id);
                pg::internal_set_ptr(page, pos + 1, right_id);
              }

              let left_pid = mngr.write_next(&page);
              let right_pid = mngr.write_next(&right_page);
              mngr.mark_as_free(root);
              BTreePut::Split(left_pid, right_pid, skey)
            }
          }
        }
      },
      unsupported_type => {
        panic!("Invalid page type: {:?}", unsupported_type);
      },
    }
  }
}

// Returns value for the key if the key exists, otherwise None.
pub fn get(mut root: u32, key: &[u8], mngr: &mut StorageManager) -> Option<Vec<u8>> {
  if root == INVALID_PAGE_ID {
    return None;
  }

  let mut page = vec![0u8; mngr.page_size()];

  loop {
    mngr.read(root, &mut page);
    let (pos, exists) = pg::bsearch(&page, key, mngr);
    match pg::page_type(&page) {
      pg::PageType::Leaf => {
        return if exists { Some(pg::leaf_get_val(&page, pos, mngr)) } else { None }
      },
      pg::PageType::Internal => {
        let ptr = if exists { pos + 1 } else { pos };
        root = pg::internal_get_ptr(&page, ptr);
      },
      unsupported_type => {
        panic!("Invalid page type: {:?}", unsupported_type);
      },
    }
  }
}

// Deletes the key in the btree and returns a new snapshot via a new root page.
pub fn del(root: u32, key: &[u8], mngr: &mut StorageManager) -> u32 {
  let mut page = vec![0u8; mngr.page_size()];
  match recur_del(root, key, mngr, &mut page) {
    BTreeDel::Empty => root,
    BTreeDel::Update(pid, num_slots, ..) => {
      if num_slots > 0 {
        pid
      } else {
        mngr.read(pid, &mut page);
        match pg::page_type(&page) {
          pg::PageType::Internal => {
            // Current node is empty, return the child page instead.
            let next_pid = pg::internal_get_ptr(&page, 0);
            mngr.mark_as_free(pid);
            next_pid
          },
          pg::PageType::Leaf => {
            // Btree is empty, delete the current page and return invalid pointer.
            mngr.mark_as_free(pid);
            INVALID_PAGE_ID
          },
          unsupported_type => panic!("Invalid page type: {:?}", unsupported_type),
        }
      }
    },
  }
}

enum BTreeDel {
  Empty, // indicates the key did not exist, tree should not be modified
  Update(u32 /* page id */, usize /* num slots */, Option<Vec<u8>> /* next smallest key */),
}

fn recur_del(root: u32, key: &[u8], mngr: &mut StorageManager, page: &mut [u8]) -> BTreeDel {
  if root == INVALID_PAGE_ID {
    // Nothing to delete.
    BTreeDel::Empty
  } else {
    mngr.read(root, page);
    // Perform search to find the position of the key and whether or not it exists
    let (pos, exists) = pg::bsearch(&page, key, mngr);
    match pg::page_type(&page) {
      pg::PageType::Leaf => {
        if exists {
          // Delete an existing key.
          pg::leaf_delete(page, pos, mngr);
          // We are deleting the smallest key, update parents to the next smallest
          let mut next_smallest_key = None;
          if pos == 0 && pg::num_slots(&page) > 0 {
            next_smallest_key = Some(pg::leaf_get_key(&page, 0, mngr));
          }

          let new_num_slots = pg::num_slots(&page);
          let new_root = mngr.write_next(&page);
          mngr.mark_as_free(root);
          BTreeDel::Update(new_root, new_num_slots, next_smallest_key)
        } else {
          BTreeDel::Empty
        }
      },
      pg::PageType::Internal => {
        let mut child_page = vec![0u8; mngr.page_size()]; // we reuse it as a temporary buffer
        let ptr = if exists { pos + 1 } else { pos };

        match recur_del(pg::internal_get_ptr(&page, ptr), key, mngr, &mut child_page) {
          BTreeDel::Empty => BTreeDel::Empty,
          BTreeDel::Update(child_id, child_num_slots, next_smallest_key) => {
            pg::internal_set_ptr(page, ptr, child_id);
            // Update the next smallest key.
            // TODO: optimise key comparison.
            if exists && pg::internal_get_key(&page, pos, mngr) == key {
              if let Some(smallest_key) = next_smallest_key.as_ref() {
                // Update the key. Because we can only delete and re-insert the key, we also
                // need to update the pointer that is stored together with the key.
                let uptr = pg::internal_get_ptr(page, pos + 1);
                pg::internal_delete(page, pos, mngr);
                pg::internal_insert(page, pos, &smallest_key, mngr);
                pg::internal_set_ptr(page, pos + 1, uptr);
              }
            }

            if child_num_slots < pg::PAGE_MIN_SLOTS {
              mngr.read(child_id, &mut child_page);
              let mut sib_page = vec![0u8; mngr.page_size()];

              // Check the left sibling page.
              if ptr > 0 {
                let sib_id = pg::internal_get_ptr(&page, ptr - 1);
                mngr.read(sib_id, &mut sib_page);

                if pg::num_slots(&sib_page) > pg::PAGE_MIN_SLOTS &&
                    pg::steal_from_left(page, ptr, &mut child_page, &mut sib_page, mngr) {
                  let new_child_id = mngr.write_next(&mut child_page);
                  let new_sib_id = mngr.write_next(&mut sib_page);
                  pg::internal_set_ptr(page, ptr - 1, new_sib_id);
                  pg::internal_set_ptr(page, ptr, new_child_id);

                  mngr.mark_as_free(child_id);
                  mngr.mark_as_free(sib_id);
                } else if pg::merge(page, ptr - 1, &mut sib_page, &mut child_page, mngr) {
                  // Merge current into the left sibling page.
                  let new_sib_id = mngr.write_next(&mut sib_page);
                  pg::internal_set_ptr(page, ptr - 1, new_sib_id);

                  mngr.mark_as_free(child_id);
                  mngr.mark_as_free(sib_id);
                }
              } else if ptr < pg::num_slots(&page) {
                // Check the left sibling page.
                let sib_id = pg::internal_get_ptr(&page, ptr + 1);
                mngr.read(sib_id, &mut sib_page);

                if pg::num_slots(&sib_page) > pg::PAGE_MIN_SLOTS &&
                    pg::steal_from_right(page, ptr, &mut child_page, &mut sib_page, mngr) {
                  let new_child_id = mngr.write_next(&mut child_page);
                  let new_sib_id = mngr.write_next(&mut sib_page);
                  pg::internal_set_ptr(page, ptr, new_child_id);
                  pg::internal_set_ptr(page, ptr + 1, new_sib_id);

                  mngr.mark_as_free(child_id);
                  mngr.mark_as_free(sib_id);
                } else if pg::merge(page, ptr, &mut child_page, &mut sib_page, mngr) {
                  // Merge the right sibling page into current.
                  let new_child_id = mngr.write_next(&mut child_page);
                  pg::internal_set_ptr(page, ptr, new_child_id);

                  mngr.mark_as_free(child_id);
                  mngr.mark_as_free(sib_id);
                }
              }
            }

            let new_num_slots = pg::num_slots(&page);
            let new_root = mngr.write_next(&page);
            mngr.mark_as_free(root);
            BTreeDel::Update(new_root, new_num_slots, next_smallest_key)
          },
        }
      },
      unsupported_type => {
        panic!("Invalid page type: {:?}", unsupported_type);
      },
    }
  }
}

pub fn btree_debug(root: u32, mngr: &mut StorageManager) {
  let mut page = vec![0u8; mngr.page_size()];
  btree_debug_recur(root, &mut page, mngr, 2);
  println!();
}

fn btree_debug_recur(root: u32, page: &mut [u8], mngr: &mut StorageManager, offset: usize) {
  if root == INVALID_PAGE_ID {
    println!("{:>width$} INVALID PAGE", "!", width = offset);
    return;
  }

  mngr.read(root, page);
  let cnt = pg::num_slots(&page);
  match pg::page_type(&page) {
    pg::PageType::Leaf if cnt == 0 => {
      println!("{:>width$} {} | cnt: {} | min: N/A | max: N/A", "*", root, cnt, width = offset);
    },
    pg::PageType::Leaf => {
      let min_key = pg::leaf_get_key(&page, 0, mngr);
      let max_key = pg::leaf_get_key(&page, cnt - 1, mngr);
      println!("{:>width$} {} | cnt: {} | min: {:?} | max: {:?}",
        "*",
        root,
        cnt,
        &min_key[..min_key.len().min(8)],
        &max_key[..max_key.len().min(8)],
        width = offset
      );
    },
    pg::PageType::Internal if cnt == 0 => {
      println!("{:>width$} {} | cnt: {} | min: N/A | max: N/A", "+", root, cnt, width = offset);
    },
    pg::PageType::Internal => {
      let min_key = pg::internal_get_key(&page, 0, mngr);
      let max_key = pg::internal_get_key(&page, cnt - 1, mngr);
      println!("{:>width$} {} | cnt: {} | min: {:?} | max: {:?}",
        "+",
        root,
        cnt,
        &min_key[..min_key.len().min(8)],
        &max_key[..max_key.len().min(8)],
        width = offset
      );
      let cpage = page.to_vec(); // clone the buffer so recursive calls don't overwrite data
      for i in 0..cnt + 1 {
        let pid = pg::internal_get_ptr(&cpage, i);
        btree_debug_recur(pid, page, mngr, offset + 2);
      }
    },
    _ => panic!("Cannot print btree: unexpected page type"),
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use rand::prelude::*;

  #[test]
  fn test_btree_put_insert_empty() {
    let mut root = INVALID_PAGE_ID;
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    root = put(root, &[1], &[10], &mut mngr);

    assert_eq!(mngr.num_pages(), 1);

    let mut buf = vec![0u8; mngr.page_size()];
    mngr.read(root, &mut buf);

    assert_eq!(pg::page_type(&buf), pg::PageType::Leaf);
    assert_eq!(pg::num_slots(&buf), 1);
    assert_eq!(pg::leaf_get_key(&buf, 0, &mut mngr), vec![1]);
    assert_eq!(pg::leaf_get_val(&buf, 0, &mut mngr), vec![10]);
  }

  #[test]
  fn test_btree_put_update() {
    let mut root = INVALID_PAGE_ID;
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    root = put(root, &[1], &[10], &mut mngr);
    assert_eq!(get(root, &[1], &mut mngr), Some(vec![10]));

    root = put(root, &[1], &[20], &mut mngr);
    assert_eq!(get(root, &[1], &mut mngr), Some(vec![20]));

    root = put(root, &[1], &[30; 256], &mut mngr);
    assert_eq!(get(root, &[1], &mut mngr), Some(vec![30; 256]));
  }

  #[test]
  fn test_btree_put_insert_leaf_split() {
    let mut root = INVALID_PAGE_ID;
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    for i in 0..11 {
      root = put(root, &[i], &[i], &mut mngr);
    }

    let mut buf = vec![0u8; mngr.page_size()];
    mngr.read(root, &mut buf);

    assert_eq!(pg::page_type(&buf), pg::PageType::Internal);
    assert_eq!(pg::num_slots(&buf), 1);

    let ptr0 = pg::internal_get_ptr(&buf, 0);
    let ptr1 = pg::internal_get_ptr(&buf, 1);

    mngr.read(ptr0, &mut buf);
    assert_eq!(pg::page_type(&buf), pg::PageType::Leaf);
    assert_eq!(pg::num_slots(&buf), 5);

    mngr.read(ptr1, &mut buf);
    assert_eq!(pg::page_type(&buf), pg::PageType::Leaf);
    assert_eq!(pg::num_slots(&buf), 6);
  }

  #[test]
  fn test_btree_put_insert_internal_split() {
    let mut root = INVALID_PAGE_ID;
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    for i in 0..70 {
      root = put(root, &[i], &[i], &mut mngr);
    }

    let mut buf = vec![0u8; mngr.page_size()];
    mngr.read(root, &mut buf);

    assert_eq!(pg::page_type(&buf), pg::PageType::Internal);
    assert_eq!(pg::num_slots(&buf), 1);

    let ptr0 = pg::internal_get_ptr(&buf, 0);
    let ptr1 = pg::internal_get_ptr(&buf, 1);

    mngr.read(ptr0, &mut buf);
    assert_eq!(pg::page_type(&buf), pg::PageType::Internal);
    assert_eq!(pg::num_slots(&buf), 5);

    mngr.read(ptr1, &mut buf);
    assert_eq!(pg::page_type(&buf), pg::PageType::Internal);
    assert_eq!(pg::num_slots(&buf), 6);
  }

  #[test]
  fn test_btree_del_leaf_non_existent() {
    let mut root = INVALID_PAGE_ID;
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    for i in 0..3 {
      root = put(root, &[i], &[i * 10], &mut mngr);
    }
    for i in 4..10 {
      root = del(root, &[i], &mut mngr);
    }

    for i in 0..3 {
      assert_eq!(get(root, &[i], &mut mngr).unwrap(), vec![i * 10]);
    }
  }

  #[test]
  fn test_btree_del_leaf_asc() {
    let mut root = INVALID_PAGE_ID;
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    for i in 0..5 {
      root = put(root, &[i], &[i * 10], &mut mngr);
    }
    assert_ne!(root, INVALID_PAGE_ID);
    for i in 0..5 {
      root = del(root, &[i], &mut mngr);
    }

    assert_eq!(root, INVALID_PAGE_ID);
    for i in 0..5 {
      assert_eq!(get(root, &[i], &mut mngr), None);
    }

    mngr.sync();
    assert_eq!(mngr.num_pages(), 0);
  }

  #[test]
  fn test_btree_del_leaf_desc() {
    let mut root = INVALID_PAGE_ID;
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    for i in 0..5 {
      root = put(root, &[i], &[i * 10], &mut mngr);
    }
    assert_ne!(root, INVALID_PAGE_ID);
    for i in (0..5).rev() {
      root = del(root, &[i], &mut mngr);
    }

    assert_eq!(root, INVALID_PAGE_ID);
    for i in 0..5 {
      assert_eq!(get(root, &[i], &mut mngr), None);
    }

    mngr.sync();
    assert_eq!(mngr.num_pages(), 0);
  }

  #[test]
  fn test_btree_del_internal_asc() {
    let mut root = INVALID_PAGE_ID;
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    let num_keys = 255;

    for i in 0..num_keys {
      let key = if i % 10 == 0 { vec![i; 100] } else { vec![i] };
      root = put(root, &key, &[i; 10], &mut mngr);
    }

    assert_ne!(root, INVALID_PAGE_ID);
    for i in 0..num_keys {
      let key = if i % 10 == 0 { vec![i; 100] } else { vec![i] };
      root = del(root, &key, &mut mngr);
    }

    assert_eq!(root, INVALID_PAGE_ID);

    mngr.sync();
    assert_eq!(mngr.num_pages(), 0);
  }

  #[test]
  fn test_btree_del_internal_desc() {
    let mut root = INVALID_PAGE_ID;
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    let num_keys = 255;

    for i in 0..num_keys {
      let key = if i % 10 == 0 { vec![i; 100] } else { vec![i] };
      root = put(root, &key, &[i; 10], &mut mngr);
    }
    assert_ne!(root, INVALID_PAGE_ID);
    for i in (0..num_keys).rev() {
      let key = if i % 10 == 0 { vec![i; 100] } else { vec![i] };
      root = del(root, &key, &mut mngr);
    }

    assert_eq!(root, INVALID_PAGE_ID);

    mngr.sync();
    assert_eq!(mngr.num_pages(), 0);
  }

  #[test]
  fn test_btree_del_split_key() {
    // Regression test to check that we update next smallest key correctly.
    // When deleting [6], the internal page key needs to be updated to [7]
    // and the subsequent delete of [7] does not mess up the keys or fail.
    let mut root = INVALID_PAGE_ID;
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    for i in 1..20 {
      root = put(root, &[i], &[i], &mut mngr);
    }
    root = del(root, &[6], &mut mngr);
    root = del(root, &[7], &mut mngr);

    assert_eq!(get(root, &[3], &mut mngr).unwrap(), &[3]);
    assert_eq!(get(root, &[4], &mut mngr).unwrap(), &[4]);
    assert_eq!(get(root, &[11], &mut mngr).unwrap(), &[11]);
    assert_eq!(get(root, &[12], &mut mngr).unwrap(), &[12]);
  }

  #[test]
  fn test_btree_del_merge_of_leaf_nodes() {
    // This test verifies that the issue of incorrect types when merging is fixed:
    //   left: `Leaf`,
    //  right: `Internal`: Merge: different page type', src/page.rs:172:3

    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    let mut page = vec![0u8; mngr.page_size()];

    // Leaf 1
    pg::leaf_init(&mut page);
    pg::leaf_insert(&mut page, 0, &[1], &[1], &mut mngr);
    pg::leaf_insert(&mut page, 1, &[2], &[2], &mut mngr);
    let leaf_1 = mngr.write_next(&page);

    // Leaf 2
    pg::leaf_init(&mut page);
    pg::leaf_insert(&mut page, 0, &[4], &[4], &mut mngr);
    pg::leaf_insert(&mut page, 1, &[5], &[5], &mut mngr);
    let leaf_2 = mngr.write_next(&page);

    // Internal 1
    pg::internal_init(&mut page);
    pg::internal_set_ptr(&mut page, 0, leaf_1);
    pg::internal_insert(&mut page, 0, &[3], &mut mngr);
    pg::internal_set_ptr(&mut page, 1, leaf_2);
    let internal_1 = mngr.write_next(&page);

    // Leaf 3
    pg::leaf_init(&mut page);
    pg::leaf_insert(&mut page, 0, &[6], &[6], &mut mngr);
    pg::leaf_insert(&mut page, 1, &[7], &[7], &mut mngr);
    let leaf_3 = mngr.write_next(&page);

    // Leaf 4
    pg::leaf_init(&mut page);
    pg::leaf_insert(&mut page, 0, &[9], &[9], &mut mngr);
    pg::leaf_insert(&mut page, 1, &[10], &[10], &mut mngr);
    let leaf_4 = mngr.write_next(&page);

    // Internal 2
    pg::internal_init(&mut page);
    pg::internal_set_ptr(&mut page, 0, leaf_3);
    pg::internal_insert(&mut page, 0, &[8], &mut mngr);
    pg::internal_set_ptr(&mut page, 1, leaf_4);
    let internal_2 = mngr.write_next(&page);

    // Root
    pg::internal_init(&mut page);
    pg::internal_set_ptr(&mut page, 0, internal_1);
    pg::internal_insert(&mut page, 0, &[6], &mut mngr);
    pg::internal_set_ptr(&mut page, 1, internal_2);
    let mut root = mngr.write_next(&page);

    // Check that the tree structure is correct.
    for &i in &[1, 2, 4, 5, 6, 7, 9, 10] {
      assert_eq!(get(root, &[i], &mut mngr), Some(vec![i]));
    }

    for i in 0..20 {
      root = del(root, &[i], &mut mngr);
    }

    assert_eq!(root, INVALID_PAGE_ID);

    // Assert page consistency.
    mngr.sync();
    assert_eq!(mngr.num_pages(), 0, "Pages were not freed fully");
  }

  #[test]
  fn test_btree_get_empty() {
    let root = INVALID_PAGE_ID;
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();
    assert_eq!(get(root, &[1], &mut mngr), None);
  }

  #[test]
  fn test_btree_get_existent_key() {
    let mut root = INVALID_PAGE_ID;
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    for i in 0..100 {
      root = put(root, &[i], &[i], &mut mngr);
    }
    for i in 0..100 {
      assert_eq!(get(root, &[i], &mut mngr), Some(vec![i]));
    }
    for i in (0..100).rev() {
      assert_eq!(get(root, &[i], &mut mngr), Some(vec![i]));
    }
  }

  #[test]
  fn test_btree_get_non_existent_key() {
    let mut root = INVALID_PAGE_ID;
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    for i in 0..100 {
      root = put(root, &[i], &[i], &mut mngr);
    }

    for i in 100..200 {
      assert_eq!(get(root, &[i], &mut mngr), None);
    }
    for i in (100..200).rev() {
      assert_eq!(get(root, &[i], &mut mngr), None);
    }
  }

  #[test]
  fn test_btree_put_get_split_key() {
    // Regression test for the issue when the inserted key falls into split position
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    for i in 0..10 {
      // Prepare the tree
      let mut root = INVALID_PAGE_ID;
      for i in 0..10 {
        root = put(root, &[i * 2], &[i * 2], &mut mngr);
      }

      // This insert results in split
      root = put(root, &[i * 2 + 1], &[i * 2 + 1], &mut mngr);

      assert_eq!(get(root, &[i * 2 + 1], &mut mngr), Some(vec![i * 2 + 1]));
    }
  }

  // BTree range tests

  // #[test]
  // fn test_btree_range_no_bounds() {
  //   let (mut tree, _) = new_btree(5);
  //   let input: Vec<(Vec<u8>, Vec<u8>)> = (0..20).map(|i| (vec![i], vec![i * 10])).collect();
  //
  //   for i in &input[..] {
  //     tree = put(&tree, &i.0, &i.1).unwrap();
  //   }
  //
  //   let iter = BTreeIter::new(&tree, None, None);
  //   let res: Vec<(Vec<u8>, Vec<u8>)> = iter.collect();
  //   assert_eq!(res, input);
  // }
  //
  // #[test]
  // fn test_btree_range_start_bound() {
  //   let (mut tree, _) = new_btree(5);
  //   let input: Vec<(Vec<u8>, Vec<u8>)> = (0..20).map(|i| (vec![i], vec![i * 10])).collect();
  //
  //   for i in &input[..] {
  //     tree = put(&tree, &i.0, &i.1).unwrap();
  //   }
  //
  //   let iter = BTreeIter::new(&tree, Some(&[6]), None);
  //   let res: Vec<(Vec<u8>, Vec<u8>)> = iter.collect();
  //   assert_eq!(res, &input[6..]);
  // }
  //
  // #[test]
  // fn test_btree_range_end_bound() {
  //   let (mut tree, _) = new_btree(5);
  //   let input: Vec<(Vec<u8>, Vec<u8>)> = (0..20).map(|i| (vec![i], vec![i * 10])).collect();
  //
  //   for i in &input[..] {
  //     tree = put(&tree, &i.0, &i.1).unwrap();
  //   }
  //
  //   let iter = BTreeIter::new(&tree, None, Some(&[17]));
  //   let res: Vec<(Vec<u8>, Vec<u8>)> = iter.collect();
  //   assert_eq!(res, &input[..18]);
  // }
  //
  // #[test]
  // fn test_btree_range_both_bounds() {
  //   let (mut tree, _) = new_btree(5);
  //   let input: Vec<(Vec<u8>, Vec<u8>)> = (0..20).map(|i| (vec![i], vec![i * 10])).collect();
  //
  //   for i in &input[..] {
  //     tree = put(&tree, &i.0, &i.1).unwrap();
  //   }
  //
  //   let iter = BTreeIter::new(&tree, Some(&[6]), Some(&[17]));
  //   let res: Vec<(Vec<u8>, Vec<u8>)> = iter.collect();
  //   assert_eq!(res, &input[6..18]);
  // }
  //
  // #[test]
  // fn test_btree_range_outside_of_bounds() {
  //   let (mut tree, _) = new_btree(5);
  //   let input: Vec<(Vec<u8>, Vec<u8>)> = (0..20).map(|i| (vec![i + 1], vec![i])).collect();
  //
  //   for i in &input[..] {
  //     tree = put(&tree, &i.0, &i.1).unwrap();
  //   }
  //
  //   let iter = BTreeIter::new(&tree, Some(&[0]), Some(&[100]));
  //   let res: Vec<(Vec<u8>, Vec<u8>)> = iter.collect();
  //   assert_eq!(res, input);
  // }

  // BTree fuzz testing

  // A sequence of random byte keys that may contain duplicate values.
  fn random_byte_key_seq(cnt: usize, min_key_len: usize, max_key_len: usize) -> Vec<Vec<u8>> {
    let mut rng = thread_rng();
    let mut input = Vec::with_capacity(cnt);
    for _ in 0..cnt {
      let key_len = rng.gen_range(min_key_len..max_key_len + 1);
      let mut key = Vec::with_capacity(key_len);
      for _ in 0..key_len {
        key.push(rng.gen::<u8>());
      }
      input.push(key);
    }
    input
  }

  // A sequence of unique integer values that are shuffled.
  fn random_unique_u32_seq(len: usize) -> Vec<Vec<u8>> {
    let mut input = Vec::with_capacity(len);
    for i in 0..len {
      input.push((i as u32).to_be_bytes().to_vec());
    }
    shuffle(&mut input);
    input
  }

  fn shuffle(input: &mut Vec<Vec<u8>>) {
    input.shuffle(&mut thread_rng());
  }

  fn assert_find(root: u32, keys: &[Vec<u8>], mngr: &mut StorageManager, assert_match: bool) {
    for key in keys {
      let res = get(root, key, mngr);
      if assert_match && res != Some(key.to_vec()) {
        assert!(false, "Failed to find {:?}", key);
      } else if !assert_match && res == Some(key.to_vec()) {
        assert!(false, "Failed, the key {:?} exists", key);
      }
    }
  }

  #[test]
  fn test_btree_fuzz_unique_put_get_del() {
    let mut input = random_unique_u32_seq(500);

    for &page_size in &[256, 512, 1024] {
      shuffle(&mut input);

      println!("Input: {:?}, page size: {}", input, page_size);

      let mut root = INVALID_PAGE_ID;
      let mut mngr = StorageManager::builder().as_mem(0).with_page_size(page_size).build();

      for i in 0..input.len() {
        root = put(root, &input[i], &input[i], &mut mngr);
        assert_find(root, &input[0..i + 1], &mut mngr, true);
        assert_find(root, &input[i + 1..], &mut mngr, false);
      }

      // TODO:
      // let iter = BTreeIter::new(&tree, None, None);
      // let res: Vec<(Vec<u8>, Vec<u8>)> = iter.collect();
      // let mut exp: Vec<(Vec<u8>, Vec<u8>)> = input.iter().map(|i| (i.clone(), i.clone())).collect();
      // exp.sort();
      // assert_eq!(res, exp);

      shuffle(&mut input);
      for i in 0..input.len() {
        assert_find(root, &[input[i].clone()], &mut mngr, true);
        root = del(root, &input[i], &mut mngr);
        assert_find(root, &[input[i].clone()], &mut mngr, false);
      }
      assert_eq!(root, INVALID_PAGE_ID);

      // Assert page consistency.
      mngr.sync();
      assert_eq!(mngr.num_pages(), 0, "Pages were not freed fully");
    }
  }

  #[test]
  fn test_btree_fuzz_byte_put_get_del() {
    let mut input = random_byte_key_seq(500, 1, 256);

    for &page_size in &[256, 512, 1024] {
      shuffle(&mut input);

      println!("Input: {:?}, page size: {}", input, page_size);

      let mut root = INVALID_PAGE_ID;
      let mut mngr = StorageManager::builder().as_mem(0).with_page_size(page_size).build();

      for i in 0..input.len() {
        root = put(root, &input[i], &input[i], &mut mngr);
      }

      // TODO:
      // let iter = BTreeIter::new(&tree, None, None);
      // let res: Vec<(Vec<u8>, Vec<u8>)> = iter.collect();
      // let mut exp: Vec<(Vec<u8>, Vec<u8>)> = input.iter().map(|i| (i.clone(), i.clone())).collect();
      // exp.sort();
      // assert_eq!(res, exp);

      shuffle(&mut input);

      for i in 0..input.len() {
        assert!(get(root, &input[i], &mut mngr).is_some());
      }

      for i in 0..input.len() {
        root = del(root, &input[i], &mut mngr);
      }
      assert_eq!(root, INVALID_PAGE_ID);

      // Assert page consistency.
      mngr.sync();
      assert_eq!(mngr.num_pages(), 0, "Pages were not freed fully");
    }
  }

  #[test]
  fn test_btree_fuzz_byte_put_range() {
    let mut input = random_byte_key_seq(500, 4, 256);
    shuffle(&mut input);

    let exp: Vec<(Vec<u8>, Vec<u8>)> = input.iter().map(|i| (i.clone(), vec![])).collect();

    let mut root = INVALID_PAGE_ID;
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    for (key, val) in &exp[..] {
      root = put(root, &key, &val, &mut mngr);
    }

    // TODO:
    // exp.sort();
    //
    // for i in 0..exp.len() {
    //   for j in 0..exp.len() {
    //     let mut iter = BTreeIter::new(&tree, Some(&exp[i].0), Some(&exp[j].0));
    //     if i > j {
    //       assert_eq!(iter.next(), None);
    //     } else {
    //       let res: Vec<(Vec<u8>, Vec<u8>)> = iter.collect();
    //       assert_eq!(&res[..], &exp[i..j + 1]);
    //     }
    //   }
    // }
    //
    // assert_page_consistency(&cache);
  }
}
