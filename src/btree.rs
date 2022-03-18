use crate::storage::{INVALID_PAGE_ID, StorageManager};
use crate::page;

#[derive(Clone, Debug, PartialEq)]
pub enum BTreePut {
  Update(u32 /* page id */),
  Split(u32 /* left page id */, u32 /* right page id */, Vec<u8> /* split key */)
}

// Inserts key and value in the btree and returns a new snapshot via a new root page.
pub fn put(root: u32, key: &[u8], val: &[u8], mngr: &mut StorageManager) -> u32 {
  let mut page = vec![0u8; mngr.page_size()];
  match recur_put(root, &key, &val, mngr, &mut page) {
    BTreePut::Update(id) => id,
    BTreePut::Split(left_id, right_id, key) => {
      // Root page will always be internal after splitting and will only have two values.
      page::internal_init(&mut page);
      page::internal_insert(&mut page, 0, &key, mngr);
      page::internal_set_ptr(&mut page, 0, left_id);
      page::internal_set_ptr(&mut page, 1, right_id);
      mngr.write_next(&page)
    },
  }
}

// Puts key and value into btree.
fn recur_put(root: u32, key: &[u8], val: &[u8], mngr: &mut StorageManager, page: &mut [u8]) -> BTreePut {
  if root == INVALID_PAGE_ID {
    // Create new leaf page
    page::leaf_init(page);
    page::leaf_can_insert(&page, key, val);
    page::leaf_insert(page, 0, key, val, mngr);
    BTreePut::Update(mngr.write_next(&page))
  } else {
    mngr.read(root, page);
    let (pos, exists) = page::bsearch(&page, key, mngr);
    match page::page_type(&page) {
      page::PageType::Leaf => {
        if exists || page::leaf_can_insert(&page, key, val) {
          if exists {
            // TODO: optimise page updates
            page::leaf_delete(page, pos, mngr);
          }
          page::leaf_insert(page, pos, key, val, mngr);

          let new_root = mngr.write_next(&page);
          mngr.mark_as_free(root);
          BTreePut::Update(new_root)
        } else {
          // We need to split the leaf page.
          let num_slots = page::num_slots(&page);
          // Split point.
          let spos = num_slots / 2;
          // Split key.
          let skey = if pos == spos { key.to_vec() } else { page::leaf_get_key(&page, spos, mngr) };

          let mut right_page = vec![0u8; mngr.page_size()];
          page::leaf_init(&mut right_page);
          page::leaf_split(page, &mut right_page, spos);

          if pos >= spos {
            page::leaf_insert(&mut right_page, pos - spos, key, val, mngr);
          } else {
            page::leaf_insert(page, pos, key, val, mngr);
          }

          let left_pid = mngr.write_next(&page);
          let right_pid = mngr.write_next(&right_page);
          mngr.mark_as_free(root);
          BTreePut::Split(left_pid, right_pid, skey)
        }
      },
      page::PageType::Internal => {
        let mut right_page = page.to_vec(); // we reuse right_page as a temporary buffer
        let ptr = if exists { pos + 1 } else { pos };

        match recur_put(page::internal_get_ptr(&page, ptr), key, val, mngr, &mut right_page) {
          BTreePut::Update(id) => {
            page::internal_set_ptr(page, ptr, id);
            let new_root = mngr.write_next(&page);
            mngr.mark_as_free(root);
            BTreePut::Update(new_root)
          },
          BTreePut::Split(left_id, right_id, key) => {
            if page::internal_can_insert(&page, &key) {
              page::internal_insert(page, pos, &key, mngr);
              page::internal_set_ptr(page, pos, left_id);
              page::internal_set_ptr(page, pos + 1, right_id);

              let new_root = mngr.write_next(&page);
              mngr.mark_as_free(root);
              BTreePut::Update(new_root)
            } else {
              // We need to split internal page.
              let num_slots = page::num_slots(&page);
              // Split point.
              let spos = num_slots / 2;
              // Split key.
              let skey = page::internal_get_key(&page, spos, mngr);

              page::internal_init(&mut right_page);
              page::internal_split(page, &mut right_page, spos);

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
                page::internal_insert(&mut right_page, pos - spos - 1, &key, mngr);
                page::internal_set_ptr(&mut right_page, pos - spos - 1, left_id);
                page::internal_set_ptr(&mut right_page, pos - spos, right_id);
              } else {
                page::internal_insert(page, pos, &key, mngr);
                page::internal_set_ptr(page, pos, left_id);
                page::internal_set_ptr(page, pos + 1, right_id);
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
    let (pos, exists) = page::bsearch(&page, key, mngr);
    match page::page_type(&page) {
      page::PageType::Leaf => {
        return if exists { Some(page::leaf_get_val(&page, pos, mngr)) } else { None }
      },
      page::PageType::Internal => {
        let ptr = if exists { pos + 1 } else { pos };
        root = page::internal_get_ptr(&page, ptr);
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
  mngr.read(root, page);
  let cnt = page::num_slots(&page);
  match page::page_type(&page) {
    page::PageType::Leaf => {
      println!("{:>width$} {} | cnt: {} | min: {:?} | max: {:?}",
        "*",
        root,
        cnt,
        page::leaf_get_key(&page, 0, mngr),
        page::leaf_get_key(&page, cnt - 1, mngr),
        width = offset
      );
    },
    page::PageType::Internal => {
      println!("{:>width$} {} | cnt: {} | min: {:?} | max: {:?}",
        "+",
        root,
        cnt,
        page::internal_get_key(&page, 0, mngr),
        page::internal_get_key(&page, cnt - 1, mngr),
        width = offset
      );
      let cpage = page.to_vec(); // clone the buffer so recursive calls don't overwrite data
      for i in 0..cnt + 1 {
        let ptr = page::internal_get_ptr(&cpage, i);
        btree_debug_recur(ptr, page, mngr, offset + 2);
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
  fn test_btree_put() {
    let mut root = INVALID_PAGE_ID;
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();
    let num_keys = 100;
    for i in 0..num_keys {
      let key = vec![(num_keys -i) as u8; 1];
      let val = vec![(num_keys - i) as u8; 1];
      root = put(root, &key, &val, &mut mngr);
    }

    let mut tmp = vec![0u8; mngr.page_size()];
    for pid in 0..mngr.num_pages() as u32 {
      if mngr.is_accessible(pid) {
        mngr.read(pid, &mut tmp);
        page::debug(pid, &tmp);
      }
    }

    btree_debug(root, &mut mngr);

    assert!(false, "OK");
  }

  #[test]
  fn test_btree_put_insert_empty() {
    let mut root = INVALID_PAGE_ID;
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();

    root = put(root, &[1], &[10], &mut mngr);

    assert_eq!(mngr.num_pages(), 1);

    let mut buf = vec![0u8; mngr.page_size()];
    mngr.read(root, &mut buf);

    assert_eq!(page::page_type(&buf), page::PageType::Leaf);
    assert_eq!(page::num_slots(&buf), 1);
    assert_eq!(page::leaf_get_key(&buf, 0, &mut mngr), vec![1]);
    assert_eq!(page::leaf_get_val(&buf, 0, &mut mngr), vec![10]);
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

    assert_eq!(page::page_type(&buf), page::PageType::Internal);
    assert_eq!(page::num_slots(&buf), 1);

    let ptr0 = page::internal_get_ptr(&buf, 0);
    let ptr1 = page::internal_get_ptr(&buf, 1);

    mngr.read(ptr0, &mut buf);
    assert_eq!(page::page_type(&buf), page::PageType::Leaf);
    assert_eq!(page::num_slots(&buf), 5);

    mngr.read(ptr1, &mut buf);
    assert_eq!(page::page_type(&buf), page::PageType::Leaf);
    assert_eq!(page::num_slots(&buf), 6);
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

    assert_eq!(page::page_type(&buf), page::PageType::Internal);
    assert_eq!(page::num_slots(&buf), 1);

    let ptr0 = page::internal_get_ptr(&buf, 0);
    let ptr1 = page::internal_get_ptr(&buf, 1);

    mngr.read(ptr0, &mut buf);
    assert_eq!(page::page_type(&buf), page::PageType::Internal);
    assert_eq!(page::num_slots(&buf), 5);

    mngr.read(ptr1, &mut buf);
    assert_eq!(page::page_type(&buf), page::PageType::Internal);
    assert_eq!(page::num_slots(&buf), 6);
  }

  // #[test]
  // fn test_btree_del_leaf_non_existent() {
  //   let (mut tree, cache) = new_btree(5);
  //   for i in 0..3 {
  //     tree = put(&tree, &[i], &[i * 10]).unwrap();
  //   }
  //   for i in 4..10 {
  //     tree = del(&tree, &[i]).unwrap();
  //   }
  //
  //   assert_page_consistency(&cache);
  //   assert_num_pages(&cache, 10);
  //   assert_eq!(get_page(&cache, tree.root_page_id).keys, &[vec![0], vec![1], vec![2]]);
  //   assert_eq!(get_page(&cache, tree.root_page_id).vals, &[vec![0], vec![10], vec![20]]);
  // }
  //
  // #[test]
  // fn test_btree_del_leaf_asc() {
  //   let (mut tree, cache) = new_btree(5);
  //   for i in 0..5 {
  //     tree = put(&tree, &[i], &[i * 10]).unwrap();
  //   }
  //   for i in 0..5 {
  //     tree = del(&tree, &[i]).unwrap();
  //   }
  //
  //   assert_page_consistency(&cache);
  //   assert_num_pages(&cache, 11);
  //   assert_eq!(get_page(&cache, tree.root_page_id).keys.len(), 0);
  //   assert_eq!(get_page(&cache, tree.root_page_id).vals.len(), 0);
  // }
  //
  // #[test]
  // fn test_btree_del_leaf_desc() {
  //   let (mut tree, cache) = new_btree(5);
  //   for i in 0..5 {
  //     tree = put(&tree, &[i], &[i * 10]).unwrap();
  //   }
  //   for i in (0..5).rev() {
  //     tree = del(&tree, &[i]).unwrap();
  //   }
  //
  //   assert_page_consistency(&cache);
  //   assert_num_pages(&cache, 11);
  //   assert_eq!(get_page(&cache, tree.root_page_id).keys.len(), 0);
  //   assert_eq!(get_page(&cache, tree.root_page_id).vals.len(), 0);
  // }
  //
  // #[test]
  // fn test_btree_del_internal_asc() {
  //   let (mut tree, cache) = new_btree(5);
  //   for i in 0..10 {
  //     tree = put(&tree, &[i], &[i * 10]).unwrap();
  //   }
  //   for i in 0..10 {
  //     tree = del(&tree, &[i]).unwrap();
  //   }
  //
  //   assert_page_consistency(&cache);
  //   assert_num_pages(&cache, 38);
  //   assert_eq!(get_page(&cache, tree.root_page_id).keys.len(), 0);
  //   assert_eq!(get_page(&cache, tree.root_page_id).vals.len(), 0);
  // }
  //
  // #[test]
  // fn test_btree_del_internal_desc() {
  //   let (mut tree, cache) = new_btree(5);
  //   for i in 0..10 {
  //     tree = put(&tree, &[i], &[i * 10]).unwrap();
  //   }
  //   for i in (0..10).rev() {
  //     tree = del(&tree, &[i]).unwrap();
  //   }
  //
  //   assert_page_consistency(&cache);
  //   assert_num_pages(&cache, 39);
  //   assert_eq!(get_page(&cache, tree.root_page_id).keys.len(), 0);
  //   assert_eq!(get_page(&cache, tree.root_page_id).vals.len(), 0);
  // }
  //
  // #[test]
  // fn test_btree_del_split_key() {
  //   // Regression test to check that we update next smallest key correctly.
  //   // When deleting [3], the internal page key needs to be updated to [4]
  //   // and the subsequent delete of [4] does not cause "index out of bound" error.
  //   let (mut tree, cache) = new_btree(4);
  //   tree = put(&tree, &[1], &[1]).unwrap();
  //   tree = put(&tree, &[2], &[2]).unwrap();
  //   tree = put(&tree, &[3], &[3]).unwrap();
  //   tree = put(&tree, &[4], &[4]).unwrap();
  //   tree = put(&tree, &[5], &[5]).unwrap();
  //   tree = put(&tree, &[6], &[6]).unwrap();
  //
  //   tree = del(&tree, &[3]).unwrap();
  //   tree = del(&tree, &[4]).unwrap();
  //
  //   assert_page_consistency(&cache);
  //   assert_eq!(get(&tree, &[3]).unwrap(), None);
  //   assert_eq!(get(&tree, &[4]).unwrap(), None);
  // }

  #[test]
  fn test_btree_get_empty() {
    let mut root = INVALID_PAGE_ID;
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

  // A sequence of random byte keys that may contain duplicate values
  fn random_byte_key_seq(len: usize) -> Vec<Vec<u8>> {
    let mut rng = thread_rng();
    let mut input = Vec::with_capacity(len);
    for _ in 0..len {
      input.push(rng.gen::<[u8; 10]>().to_vec());
    }
    input
  }

  // A sequence of unique integer values that are shuffled
  fn random_unique_key_seq(len: usize) -> Vec<Vec<u8>> {
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
    let mut input = random_unique_key_seq(200);

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
      //
      // shuffle(&mut input);
      // for i in 0..input.len() {
      //   assert_find(&tree, &[input[i].clone()], true);
      //   tree = del(&tree, &input[i]).unwrap();
      //   assert_find(&tree, &[input[i].clone()], false);
      // }
      //
      // assert_page_consistency(&cache);
      // assert_eq!(get_page(&cache, tree.root_page_id).keys.len(), 0);
    }
  }

  #[test]
  fn test_btree_fuzz_byte_put_get_del() {
    let mut input = random_byte_key_seq(500);

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
      //
      // shuffle(&mut input);
      //
      // for i in 0..input.len() {
      //   assert!(get(&tree, &input[i]).unwrap().is_some());
      // }
      //
      // for i in 0..input.len() {
      //   tree = del(&tree, &input[i]).unwrap();
      // }
      //
      // assert_page_consistency(&cache);
      // assert_eq!(get_page(&cache, tree.root_page_id).keys.len(), 0);
    }
  }

  #[test]
  fn test_btree_fuzz_byte_put_range() {
    let mut input = random_byte_key_seq(500);
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
