use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::io::Write;
use std::mem::size_of;
use crate::block::{BlockManager, BlockManagerStats};
use crate::page as pg;
use crate::storage::{INVALID_PAGE_ID, StorageManager};
use crate::util::LruCache;

//===========
// Page cache
//===========

// Default memory for page cache.
pub const DEFAULT_PAGE_CACHE_MEM: usize = 128 * 1024 * 1024;
// Max virtual id is 2,147,483,647.
const VID_MASK: u32 = !0x7fffffff;

// Returns true if it is a virtual page id.
#[inline]
pub fn is_virtual_page_id(id: u32) -> bool {
  id != INVALID_PAGE_ID && VID_MASK & id != 0
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PageInfo {
  // The page is virtual and is fully in memory.
  VirtualMem(u32 /* vid */, usize /* offset within the page cache buffer */, pg::PageType),
  // The page is virtual but the content has been flushed to disk.
  VirtualDisk(u32 /* vid */, u32 /* pid */, pg::PageType),
  // The page is physical, it was committed previously and resides on disk.
  Physical(usize /* offset within the page cache buffer */, pg::PageType),
}

impl PageInfo {
  // A convenient method to return page type for the enum.
  fn page_type(&self) -> pg::PageType {
    match self {
      &PageInfo::VirtualMem(_, _, pg_type) => pg_type,
      &PageInfo::VirtualDisk(_, _, pg_type) => pg_type,
      &PageInfo::Physical(_, pg_type) => pg_type,
    }
  }

  // A convenient method to return virtual page id for the enum.
  fn vid(&self) -> u32 {
    match self {
      &PageInfo::VirtualMem(vid, _, _) => vid,
      &PageInfo::VirtualDisk(vid, _, _) => vid,
      // Physical pages do not have virtual ids.
      &PageInfo::Physical(_, _) => unimplemented!(),
    }
  }
}

// We need to implement special ordering for PageInfo objects.
// This is needed for the priority queue to ensure we commit pages in order in which they are
// created.

impl PartialOrd for PageInfo {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for PageInfo {
  fn cmp(&self, other: &Self) -> Ordering {
    // The heap is a max heap so we need to reverse the order.
    match (self.page_type(), other.page_type()) {
      (pg::PageType::Overflow, pg::PageType::Overflow) => other.vid().cmp(&self.vid()),
      (pg::PageType::Overflow, pg::PageType::Leaf) => Ordering::Greater,
      (pg::PageType::Overflow, pg::PageType::Internal) => Ordering::Greater,
      (pg::PageType::Leaf, pg::PageType::Overflow) => Ordering::Less,
      (pg::PageType::Leaf, pg::PageType::Leaf) => other.vid().cmp(&self.vid()),
      (pg::PageType::Leaf, pg::PageType::Internal) => Ordering::Greater,
      (pg::PageType::Internal, pg::PageType::Overflow) => Ordering::Less,
      (pg::PageType::Internal, pg::PageType::Leaf) => Ordering::Less,
      (pg::PageType::Internal, pg::PageType::Internal) => other.vid().cmp(&self.vid()),
    }
  }
}

// Buffer pool for StorageManager.
pub struct PageCache {
  counter: u32, // counter for virtual page ids
  page_size: usize, // page size for fast access
  max_mem: usize, // maximum amount of memory in bytes allowed
  mngr: StorageManager,
  buf: Vec<u8>, // buffer for the cache
  buf_len: usize, // occupied portion of the buffer
  offset_map: HashMap<u32, PageInfo>, // maps page ids to offsets in the buf
  lru: LruCache<u32>, // LRU cache for page ids
  free_offsets: Vec<usize>, // stack of free offsets
  freed_pids: Vec<u32>, // list of freed physical pages, needed for rollback
  num_cache_hits: usize, // metric
  num_cache_misses: usize, // metric
}

// We have to split the page ids space of u32 into two because we need to maintain virtual ids as
// well as physical page ids in StorageManager. Virtual ids are needed to ensure we don't write
// temporary pages after btree modifications that will be replaced later anyway.
//
// Whenever we need to flush pages backed by virtual ids, we will convert all of the references to
// the corresponding physical ids.

impl PageCache {
  // Creates new page cache.
  pub fn new(max_mem: usize, mngr: StorageManager) -> Self {
    Self {
      counter: 1,
      page_size: mngr.page_size(),
      max_mem: max_mem,
      mngr: mngr,
      buf: Vec::new(),
      buf_len: 0,
      offset_map: HashMap::new(),
      lru: LruCache::new(),
      free_offsets: Vec::new(),
      freed_pids: Vec::new(),
      num_cache_hits: 0,
      num_cache_misses: 0,
    }
  }

  // Returns the next virtual id from a counter.
  #[inline]
  fn next_virtual_id(&mut self) -> u32 {
    let id = self.counter;
    self.counter += 1;
    assert!(id < !VID_MASK, "Reached the limit of virtual ids");
    id | VID_MASK
  }

  // Increases capacity of the buffer and returns true if the operation was successful.
  // False means the maximal capacity has been reached.
  fn increase_capacity(&mut self) -> bool {
    let cap = self.buf.capacity();
    if cap >= self.max_mem {
      return false;
    }
    let new_cap = if cap == 0 { self.page_size } else { cap << 1 };
    let mut new_buf = vec![0u8; new_cap.min(self.max_mem)];
    // TODO: improve performance.
    write_bytes!(&mut new_buf[..self.buf.len()], &self.buf[..]);
    self.buf = new_buf;
    true
  }

  // Makes room for a page in the cache and returns the start pos to write the bytes.
  // Some of the pages may be evicted.
  fn get_free_offset(&mut self) -> usize {
    match self.free_offsets.pop() {
      Some(off) => {
        // There is an offset available for reuse, return it.
        off
      },
      None => {
        while self.buf_len + self.page_size > self.buf.capacity() {
          if !self.increase_capacity() {
            break;
          }
        }
        if self.buf_len + self.page_size <= self.buf.capacity() {
          // We have space in the buffer, return the offset.
          let off = self.buf_len;
          self.buf_len += self.page_size;
          off
        } else {
          // There is not enough memory in the buffer, we need to evict.
          if let Some(id) = self.lru.evict() {
            match self.offset_map.remove(&id).expect("Evicted page is not in the offset map") {
              PageInfo::VirtualMem(_, off, pg_type) => {
                // Virtual page needs to be written to disk first.
                // We return offset of the virtual page so it can be reused.
                let page = &self.buf[off..off + self.page_size];
                let pid = self.mngr.write_next(page);
                self.offset_map.insert(id, PageInfo::VirtualDisk(id, pid, pg_type));
                off
              },
              PageInfo::VirtualDisk(_, pid, _) => {
                panic!("Virtual page {} was already written to disk (pid {})", id, pid);
              },
              PageInfo::Physical(off, ..) => {
                // A physical page can be evicted safely so simply return the offset.
                off
              },
            }
          } else {
            panic!(
              "Not enough space in cache, mem used: {}, max mem: {}",
              self.mem_used(),
              self.max_mem
            );
          }
        }
      },
    }
  }

  // Memory used by page cache.
  #[inline]
  pub fn mem_used(&self) -> usize {
    self.buf.capacity() +
    self.offset_map.len() * (size_of::<u32>() + size_of::<PageInfo>()) +
    self.lru.mem_usage() +
    self.free_offsets.len() * size_of::<usize>() +
    self.freed_pids.len() * size_of::<u32>()
  }

  // Resolves all virtual ids in the page and returns a boolean flag.
  // When `true`, all virtual ids have been resolved successfully, it is okay to write the page to
  // disk. `false` means that we could not resolve some (or all) virtual ids.
  fn resolve_page(page_type: pg::PageType, buf: &mut [u8], vid_to_pid: &HashMap<u32, u32>) -> bool {
    match page_type {
      pg::PageType::Overflow => {
        let next_pid = pg::next_page(&buf);
        if !is_virtual_page_id(next_pid) {
          // Overflow page does not depend on any other pages, write to disk.
          true
        } else if let Some(&pid) = vid_to_pid.get(&next_pid) {
          // Next page id has already been written to disk which means we can resolve
          // this page. Update next page id and write to disk.
          pg::set_next_page(buf, pid);
          true
        } else {
          false // cannot commit the page just yet
        }
      },
      pg::PageType::Leaf => {
        // All overflow pages should be written before we start processing leaf pages.
        for i in 0..pg::num_slots(&buf) {
          let cell = pg::leaf_get_cell_mut(buf, i);
          let overflow_pid = u8_u32!(&cell[12..16]);
          if is_virtual_page_id(overflow_pid) {
            let pid = vid_to_pid.get(&overflow_pid).expect("Not all overflow pages were resolved");
            write_u32!(&mut cell[12..16], pid);
          }
        }
        true
      },
      pg::PageType::Internal => {
        // All leaf pages should be written before we start processing internal pages.
        for i in 0..pg::num_slots(&buf) {
          let cell = pg::internal_get_cell_mut(buf, i);
          let overflow_pid = u8_u32!(&cell[12..16]);
          if is_virtual_page_id(overflow_pid) {
            let pid = vid_to_pid.get(&overflow_pid).expect("Not all leaf pages were resolved");
            write_u32!(&mut cell[12..16], pid);
          }
        }

        // Check if we can resolve pointers as they could be links to other internal pages that
        // have not yet been processed.
        let mut can_write = true;
        for i in 0..pg::num_slots(&buf) + 1 {
          let ptr = pg::internal_get_ptr(&buf, i);
          if is_virtual_page_id(ptr) {
            if let Some(&pid) = vid_to_pid.get(&ptr) {
              pg::internal_set_ptr(buf, i, pid);
            } else {
              can_write = false;
              break;
            }
          }
        }
        can_write
      },
    }
  }
}

impl BlockManager for PageCache {
  #[inline]
  fn page_size(&self) -> usize {
    self.page_size
  }

  #[inline]
  fn load(&mut self, id: u32, buf: &mut [u8]) {
    match self.offset_map.get(&id) {
      Some(&PageInfo::VirtualMem(_, off, _)) => {
        self.num_cache_hits += 1;
        write_bytes!(&mut buf[..], &self.buf[off..off + self.page_size]);
        self.lru.update(id);
      },
      Some(&PageInfo::VirtualDisk(_, pid, pg_type)) => {
        self.num_cache_misses += 1;
        // Load into the page buffer.
        self.mngr.read(pid, buf);
        // Also copy into the page cache buffer for future access.
        let off = self.get_free_offset();
        write_bytes!(&mut self.buf[off..off + self.page_size], &buf[..]);
        // Update the offset map to point to a new offset.
        self.offset_map.insert(id, PageInfo::VirtualMem(id, off, pg_type));
        // We don't need this page anymore - it is a temporary page.
        self.mngr.mark_as_free(pid);
        // Update LRU entry.
        self.lru.update(id);
      },
      Some(&PageInfo::Physical(off, _)) => {
        self.num_cache_hits += 1;
        write_bytes!(&mut buf[..], &self.buf[off..off + self.page_size]);
        self.lru.update(id);
      },
      None if !is_virtual_page_id(id) => {
        self.num_cache_misses += 1;
        // Simply load from storage.
        self.mngr.read(id, buf);
        let pg_type = pg::page_type(&buf);
        // Also copy into the page cache buffer for future access.
        let off = self.get_free_offset();
        write_bytes!(&mut self.buf[off..off + self.page_size], &buf[..]);
        // Update the offset map to point to a new offset.
        self.offset_map.insert(id, PageInfo::Physical(off, pg_type));
        self.lru.update(id);
      },
      None => {
        // Virtual pages are expected to always be in the offset map.
        panic!("Attempt to read free virtual page {}", id);
      },
    }
  }

  #[inline]
  fn store(&mut self, buf: &[u8]) -> u32 {
    // This method only writes virtual pages.
    let vid = self.next_virtual_id();
    let off = self.get_free_offset();
    let pg_type = pg::page_type(buf);
    write_bytes!(&mut self.buf[off..off + self.page_size], &buf[..]);
    self.offset_map.insert(vid, PageInfo::VirtualMem(vid, off, pg_type));
    self.lru.update(vid);
    vid
  }

  #[inline]
  fn free(&mut self, id: u32) {
    match self.offset_map.remove(&id) {
      Some(PageInfo::VirtualMem(_, off, _)) => {
        self.free_offsets.push(off);
        self.lru.remove(id);
      },
      Some(PageInfo::VirtualDisk(_, pid, _)) => {
        self.mngr.mark_as_free(pid);
        self.lru.remove(id);
      },
      Some(PageInfo::Physical(off, _)) => {
        self.mngr.mark_as_free(id);
        self.free_offsets.push(off);
        self.lru.remove(id);
        self.freed_pids.push(id);
      },
      None if !is_virtual_page_id(id) => {
        self.mngr.mark_as_free(id);
        self.freed_pids.push(id);
      },
      None => {
        // Virtual pages are expected to always be in the offset map.
        panic!("Attempt to free non-existent virtual page {}", id);
      },
    }
  }

  // Commits (writes) all of the virtual pages to disk.
  // Does NOT call mngr.sync().
  // Returns vid -> pid mapping for any external references.
  #[inline]
  fn commit(&mut self) -> HashMap<u32, u32> {
    // When we sync pages to disk, we need to replace all virtual ids with the physical page ids.

    let mut vid_to_pid = HashMap::new();
    let mut queue = BinaryHeap::new();
    let mut page = vec![0; self.page_size];

    // Add all of the virtual pages into the queue for processing.
    for (_, &info) in &self.offset_map {
      match info {
        PageInfo::VirtualMem(_, _, _) => queue.push(info),
        PageInfo::VirtualDisk(_, _, _) => queue.push(info),
        PageInfo::Physical(_, _) => {}, // ignore physical pages, they have already been written
      }
    }

    // Process the queue:
    // - Overflow pages will come before leaf pages.
    // - Leaf pages will come before internal pages.
    // - Older pages will come before newer ones.
    while let Some(info) = queue.pop() {
      match info {
        PageInfo::VirtualMem(vid, off, pg_type) => {
          let buf = &mut self.buf[off..off + self.page_size];
          assert_eq!(pg::page_type(&buf), pg_type);
          let can_write = Self::resolve_page(pg_type, buf, &vid_to_pid);
          assert!(can_write, "Could not resolve page with vid={}, off={}, type={:?}", vid, off, pg_type);
          vid_to_pid.insert(vid, self.mngr.write_next(&buf));

          // Clean up the state in the cache.
          self.offset_map.remove(&vid);
          self.free_offsets.push(off);
          self.lru.remove(vid);
        },
        PageInfo::VirtualDisk(vid, pid, pg_type) => {
          self.mngr.read(pid, &mut page);
          assert_eq!(pg::page_type(&page), pg_type);
          let can_write = Self::resolve_page(pg_type, &mut page, &vid_to_pid);
          assert!(can_write, "Could not resolve page with vid={}, pid={}, type={:?}", vid, pid, pg_type);
          self.mngr.write(pid, &page);
          vid_to_pid.insert(vid, pid);

          // Clean up the state in the cache.
          self.offset_map.remove(&vid);
          self.lru.remove(vid);
        },
        _ => unreachable!("Should never happen"),
      }
    }

    // Return the mapping of vid -> pid so root pages can be resolved.
    vid_to_pid
  }

  // Rolls back all of the pages.
  // Does NOT call mngr.sync().
  #[inline]
  fn rollback(&mut self) {
    let mut queue = Vec::new();

    // Collect all of the pages that we need to clean up without directly modifying the map.
    for (&id, &info) in &self.offset_map {
      match info {
        PageInfo::VirtualMem(_, _, _) => queue.push((id, info)),
        PageInfo::VirtualDisk(_, _, _) => queue.push((id, info)),
        PageInfo::Physical(_, _) => {}, // do nothing, see below
      }
    }

    // Clean up the state in the cache, roll back the changes.
    for (id, info) in &queue {
      match info {
        &PageInfo::VirtualMem(_, off, _) => {
          self.offset_map.remove(id);
          self.free_offsets.push(off);
          self.lru.remove(*id);
        },
        &PageInfo::VirtualDisk(_, pid, _) => {
          // Free all of the temporary pages that we have created.
          self.mngr.mark_as_free(pid);
          self.offset_map.remove(id);
          self.lru.remove(*id);
        },
        _ => unreachable!("Should never happen"),
      }
    }

    // Reinstall all of the freed physical pages to reconstruct the previous state.
    // TODO: maybe we should consider not removing pages from the cache so they stay in the cache
    // after rollback.
    for &pid in &self.freed_pids {
      self.mngr.restore_from_free(pid);
    }
  }

  #[inline]
  fn get_mngr(&self) -> &StorageManager {
    &self.mngr
  }

  #[inline]
  fn get_mngr_mut(&mut self) -> &mut StorageManager {
    &mut self.mngr
  }

  #[inline]
  fn stats(&self) -> BlockManagerStats {
    BlockManagerStats {
      page_size: self.page_size,
      num_pages: self.mngr.num_pages(),
      num_free_pages: self.mngr.num_free_pages(),
      is_proxy_cache: false,
      cache_mem_used: self.mem_used(),
      cache_mem_max: self.max_mem,
      cache_num_hits: self.num_cache_hits,
      cache_num_misses: self.num_cache_misses,
    }
  }
}

//=================
// Page cache proxy
//=================

// Proxy page cache delegates to the storage manager directly without any buffering.
pub struct PageCacheProxy {
  mngr: StorageManager,
  free_set: HashSet<u32>,
  write_set: HashSet<u32>,
  num_cache_hits: usize,
}

impl PageCacheProxy {
  // Creates new page cache.
  pub fn new(mngr: StorageManager) -> Self {
    Self { mngr, free_set: HashSet::new(), write_set: HashSet::new(), num_cache_hits: 0 }
  }
}

impl BlockManager for PageCacheProxy {
  #[inline]
  fn page_size(&self) -> usize {
    self.mngr.page_size()
  }

  #[inline]
  fn load(&mut self, pid: u32, buf: &mut [u8]) {
    self.num_cache_hits += 1;
    self.mngr.read(pid, buf);
  }

  #[inline]
  fn store(&mut self, buf: &[u8]) -> u32 {
    let pid = self.mngr.write_next(buf);
    self.write_set.insert(pid);
    pid
  }

  #[inline]
  fn free(&mut self, pid: u32) {
    self.mngr.mark_as_free(pid);
    // We have written this page so we don't need to restore it on rollback.
    if self.write_set.contains(&pid) {
      self.free_set.remove(&pid);
      self.write_set.remove(&pid);
    } else {
      self.free_set.insert(pid);
    }
  }

  #[inline]
  fn commit(&mut self) -> HashMap<u32, u32> {
    // Everything is already in storage manager, we do not need to commit anything.
    self.write_set.clear();
    self.free_set.clear();
    HashMap::new()
  }

  #[inline]
  fn rollback(&mut self) {
    for &pid in &self.write_set {
      self.mngr.mark_as_free(pid);
    }
    for &pid in &self.free_set {
      self.mngr.restore_from_free(pid);
    }
    self.write_set.clear();
    self.free_set.clear();
  }

  #[inline]
  fn get_mngr(&self) -> &StorageManager {
    &self.mngr
  }

  #[inline]
  fn get_mngr_mut(&mut self) -> &mut StorageManager {
    &mut self.mngr
  }

  #[inline]
  fn stats(&self) -> BlockManagerStats {
    BlockManagerStats {
      page_size: self.page_size(),
      num_pages: self.mngr.num_pages(),
      num_free_pages: self.mngr.num_free_pages(),
      is_proxy_cache: true,
      cache_mem_used: self.mngr.estimated_mem_usage(),
      // Max memory does not quite make sense in proxy cache.
      cache_mem_max: self.mngr.estimated_mem_usage(),
      cache_num_hits: self.num_cache_hits,
      cache_num_misses: 0, // everything is in memory
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use rand::prelude::*;
  use crate::btree;

  fn get_mngr(page_size: u32) -> StorageManager {
    StorageManager::builder().as_mem(0).with_page_size(page_size).build()
  }

  #[test]
  fn test_cache_init_mem_usage() {
    let cache = PageCache::new(0, get_mngr(128));
    assert_eq!(cache.mem_used(), 16);

    let mut cache = PageCache::new(1024, get_mngr(128));
    cache.increase_capacity();
    assert_eq!(cache.mem_used(), 128 + 16);
  }

  #[test]
  fn test_cache_increase_capacity() {
    for i in 1..10 {
      let max_mem = i * 1024;
      let mut cache = PageCache::new(max_mem, get_mngr(1024));
      for _ in 0..100 {
        cache.increase_capacity();
      }
      assert!(!cache.increase_capacity());
      assert_eq!(cache.buf.len(), max_mem);
      assert_eq!(cache.buf.capacity(), max_mem);
    }
  }

  #[test]
  fn test_cache_page_info_ordering_in_heap() {
    let pages = vec![
      PageInfo::VirtualMem(1, 1, pg::PageType::Overflow),
      PageInfo::VirtualMem(5, 5, pg::PageType::Overflow),
      PageInfo::VirtualMem(6, 6, pg::PageType::Overflow),
      PageInfo::VirtualMem(2, 2, pg::PageType::Leaf),
      PageInfo::VirtualMem(7, 7, pg::PageType::Leaf),
      PageInfo::VirtualMem(0, 0, pg::PageType::Internal),
      PageInfo::VirtualMem(3, 3, pg::PageType::Internal),
      PageInfo::VirtualMem(4, 4, pg::PageType::Internal)
    ];

    for _ in 0..100 {
      let mut heap = BinaryHeap::new();

      let mut pages_clone = pages.clone();
      pages_clone.shuffle(&mut thread_rng());

      while let Some(item) = pages_clone.pop() {
        heap.push(item);
      }

      assert_eq!(pages_clone.len(), 0);

      while let Some(item) = heap.pop() {
        pages_clone.push(item);
      }

      assert_eq!(pages, pages_clone);
    }
  }

  #[test]
  fn test_cache_eviction() {
    let page_size = 256;
    let mut page = vec![1u8; page_size];
    pg::leaf_init(&mut page);

    let mut cache = PageCache::new(page_size * 3, get_mngr(page_size as u32));
    let pid_1 = cache.store(&page);
    let pid_2 = cache.store(&page);
    let pid_3 = cache.store(&page);

    // One of the pages above will be evicted.
    let pid_4 = cache.store(&page);

    assert_eq!(
      cache.offset_map.get(&pid_4),
      Some(&PageInfo::VirtualMem(pid_4, 0, pg::PageType::Leaf))
    );
    assert_eq!(
      cache.offset_map.get(&pid_1),
      Some(&PageInfo::VirtualDisk(pid_1, 0, pg::PageType::Leaf))
    );

    // When loading a page, the least recently used VirtualMem page will be evicted.
    cache.load(0, &mut page);

    assert_eq!(
      cache.offset_map.get(&0),
      Some(&PageInfo::Physical(256, pg::PageType::Leaf))
    );
    assert_eq!(
      cache.offset_map.get(&pid_2),
      Some(&PageInfo::VirtualDisk(pid_2, 1, pg::PageType::Leaf))
    );

    // Check offset map.
    assert_eq!(cache.offset_map.len(), 5);

    // Check LRU cache, it must only contain VirtualMem pages.
    let mut pids = Vec::new();
    while let Some(pid) = cache.lru.evict() {
      pids.push(pid);
    }
    assert_eq!(pids, vec![pid_3, pid_4, 0]);
  }

  #[test]
  fn test_cache_rollback() {
    let page_size = 256;
    let mut cache = PageCache::new(page_size * 10, get_mngr(page_size as u32));

    let mut root = INVALID_PAGE_ID;

    // 1. Insert values into the page and commit.
    for i in 0..50 {
      root = btree::put(root, &[i; 1024], &[i], &mut cache);
    }

    let vid_to_pid = cache.commit();
    let root = *vid_to_pid.get(&root).unwrap();

    cache.get_mngr_mut().sync();

    assert_eq!(root, 475);
    assert_eq!(cache.get_mngr().num_pages(), root as usize + 1);
    assert_eq!(cache.get_mngr().num_free_pages(), 130);

    // 2. Insert + delete values into the page and roll back.
    let mut root2 = root;
    for i in 0..25 {
      root2 = btree::del(root2, &[i; 1024], &mut cache);
    }
    for i in 0..100 {
      root2 = btree::put(root2, &[i * 2; 1024], &[i * 2], &mut cache);
    }

    // Check that we have more pages written to storage now before rollback.
    assert!(cache.get_mngr().num_free_pages() < 130);

    cache.rollback();
    cache.get_mngr_mut().sync();

    assert_eq!(root, 475);
    assert_eq!(cache.get_mngr().num_pages(), root as usize + 1);
    assert_eq!(cache.get_mngr().num_free_pages(), 130);
  }

  // Copy of the test_cache_rollback for PageCacheProxy.
  #[test]
  fn test_cache_proxy_rollback() {
    let page_size = 256;
    let mut cache = PageCacheProxy::new(get_mngr(page_size));

    let mut root = INVALID_PAGE_ID;

    // 1. Insert values into the page and commit.
    for i in 0..50 {
      root = btree::put(root, &[i; 1024], &[i], &mut cache);
    }

    let vid_to_pid = cache.commit();
    assert_eq!(vid_to_pid.len(), 0);

    cache.get_mngr_mut().sync();

    assert_eq!(root, 477);
    assert_eq!(cache.get_mngr().num_pages(), root as usize + 1);
    assert_eq!(cache.get_mngr().num_free_pages(), 132);

    // 2. Insert + delete values into the page and roll back.
    let mut root2 = root;
    for i in 0..25 {
      root2 = btree::del(root2, &[i; 1024], &mut cache);
    }
    for i in 0..100 {
      root2 = btree::put(root2, &[i * 2; 1024], &[i * 2], &mut cache);
    }

    // Check that we have more pages written to storage now before rollback.
    assert!(cache.get_mngr().num_free_pages() < 130);

    cache.rollback();
    cache.get_mngr_mut().sync();

    assert_eq!(root, 477);
    assert_eq!(cache.get_mngr().num_pages(), root as usize + 1);
    assert_eq!(cache.get_mngr().num_free_pages(), 132);
  }

  #[test]
  fn test_cache_stats() {
    let page_size = 256;
    let mut cache = PageCache::new(1024, get_mngr(page_size as u32));

    let mut page = vec![1u8; page_size];
    pg::leaf_init(&mut page);

    cache.store(&page);
    cache.commit();
    cache.get_mngr_mut().sync();

    cache.store(&page);
    cache.free(0);
    cache.commit();
    cache.get_mngr_mut().sync();

    assert_eq!(cache.stats().page_size, page_size);
    assert_eq!(cache.stats().num_pages, 2);
    assert_eq!(cache.stats().num_free_pages, 1);
  }

  #[test]
  fn test_cache_proxy_stats() {
    let page_size = 256;
    let cache = PageCacheProxy::new(get_mngr(page_size as u32));
    // Proxy cache routes calls directly to storage manager, we don't need to explicitly check.
    assert_eq!(cache.stats().page_size, page_size);
    assert_eq!(cache.stats().num_pages, 0);
    assert_eq!(cache.stats().num_free_pages, 0);
  }
}
