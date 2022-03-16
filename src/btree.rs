use crate::storage::{INVALID_PAGE_ID, StorageManager};
use crate::page;

#[derive(Clone, Debug, PartialEq)]
pub enum BTreePut {
  Update(u32 /* page id */),
  Split(u32 /* left page id */, u32 /* right page id */, Vec<u8> /* split key */)
}

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
            // We should always be able to insert a key with new value
            // because either key + value will fit within the page or
            // key will fit + overflow.
            //
            // Consider doing something like this:
            // storing just an overflow page in 4 bytes of value length and setting flags
            // whether the key is overflow or value is overflow.
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
          let spos = num_slots / 2 + (num_slots & 1);
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
        unimplemented!()
      },
      unsupported_type => {
        panic!("Invalid page type: {:?}", unsupported_type);
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_btree_put() {
    let mut root = INVALID_PAGE_ID;
    let mut mngr = StorageManager::builder().as_mem(0).with_page_size(256).build();
    for i in 0..10 {
      let key = vec![10 - i; i as usize];
      let val = vec![10 - i; i as usize];
      root = put(root, &key, &val, &mut mngr);
    }

    let mut tmp = vec![0u8; mngr.page_size()];
    for pid in 0..mngr.num_pages() as u32 {
      if mngr.is_accessible(pid) {
        mngr.read(pid, &mut tmp);
        page::debug(pid, &tmp);
      }
    }

    assert!(false, "OK");
  }
}
