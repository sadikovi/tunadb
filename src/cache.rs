use std::collections::HashMap;
use crate::error::Res;
use crate::page::{Page, PageID, PageManager, PageType};

enum CacheEntry {
  Borrowed,
  Ref(Page),
}

// Page cache, i.e. buffer pool, is a single threaded cache of pages in memory.
// Currently implements the basic API that is needed to manage pages.
pub struct PageCache<'a> {
  capacity: usize,
  entries: HashMap<PageID, CacheEntry>,
  page_mngr: &'a mut dyn PageManager,
  lru: LRU,
}

impl<'a> PageCache<'a> {
  // Creates a new page cache with capacity and page manager.
  pub fn new(capacity: usize, page_mngr: &'a mut dyn PageManager) -> Self {
    Self {
      capacity: capacity,
      entries: HashMap::with_capacity(capacity),
      page_mngr: page_mngr,
      lru: LRU::new(),
    }
  }

  // Returns the length of the entries in the cache.
  pub fn len(&self) -> usize {
    self.entries.len()
  }

  // Creates a new page using page manager and puts it in the cache.
  pub fn alloc_page(&mut self, page_type: PageType, page_size: usize) -> Res<Page> {
    self.evict()?;
    let page = self.page_mngr.alloc_page(page_type, page_size)?;
    // Make sure there are no duplicate page ids
    assert!(self.entries.get(&page.id()).is_none(), "Duplicate page id {}", page.id());
    self.entries.insert(page.id(), CacheEntry::Borrowed);
    // LRU entry is not there but the operation is no-op
    self.lru.remove(page.id());
    Ok(page)
  }

  // Returns a page that is in the cache or loads it from disk and stores in the cache.
  // LRU entries are updated on each access.
  pub fn get_page(&mut self, page_id: PageID) -> Res<Page> {
    let res = match self.entries.get(&page_id) {
      // Page was already borrowed
      Some(CacheEntry::Borrowed) => Err(err!("Page {} was already borrowed", page_id)),
      // Page exists, we can borrow it
      Some(CacheEntry::Ref(_)) => Ok(true),
      // Page does not exist in the cache
      None => Ok(false),
    };
    match res {
      Ok(true) => {
        let page = match self.entries.insert(page_id, CacheEntry::Borrowed) {
          Some(CacheEntry::Ref(page)) => page,
          _ => panic!("Unexpected cache state"),
        };
        // Remove from LRU since the page is being borrowed
        self.lru.remove(page_id);
        Ok(page)
      },
      Ok(false) => {
        // Load from the disk and insert into the cache
        self.evict()?;
        let page = self.page_mngr.read_page(page_id)?;
        self.entries.insert(page_id, CacheEntry::Borrowed);
        // Remove from LRU since the page is being borrowed
        self.lru.remove(page_id);
        Ok(page)
      },
      Err(err) => Err(err),
    }
  }

  // Returns page into the cache by replacing a default value.
  pub fn put_page(&mut self, page: Page) -> Res<()> {
    let page_id = page.id();
    let res = match self.entries.get(&page_id) {
      Some(CacheEntry::Borrowed) => Ok(()),
      _ => Err(err!("Page {} was replaced incorrectly", page_id)),
    };
    match res {
      Ok(_) => {
        // Replaced the correct page
        self.entries.insert(page_id, CacheEntry::Ref(page));
        // Put page id into the LRU cache
        self.lru.add(page_id);
        Ok(())
      },
      Err(err) => Err(err),
    }
  }

  // Deletes page from the cache and on disk.
  // If page is not in the cache, page manager still removes the page.
  pub fn free_page(&mut self, page_id: PageID) -> Res<()> {
    let res = match self.entries.get(&page_id) {
      // Page has been borrowed, we cannot delete it
      Some(CacheEntry::Borrowed) => Err(err!("Page {} was borrowed", page_id)),
      // It is okay to remove, it does not matter if the page is in the cache
      _ => Ok(()),
    };
    match res {
      Ok(_) => {
        self.entries.remove(&page_id);
        // Remove from LRU cache
        self.lru.remove(page_id);
        self.page_mngr.free_page(page_id)
      },
      Err(err) => Err(err),
    }
  }

  // Evicts entries from the cache to make space for a new entry.
  fn evict(&mut self) -> Res<()> {
    while self.len() >= self.capacity {
      if let Some(page_id) = self.lru.evict() {
        let res = match self.entries.get(&page_id) {
          Some(CacheEntry::Ref(_)) => Ok(()),
          _ => Err(err!("Fatal error: cannot evict page {}!", page_id)),
        };
        match res {
          Ok(_) => {
            let page = match self.entries.remove(&page_id) {
              Some(CacheEntry::Ref(page)) => page,
              _ => panic!("Unexpected cache state"),
            };
            if page.is_dirty {
              self.page_mngr.write_page(page)?;
            }
          },
          Err(err) => return Err(err),
        }
      } else {
        return Err(err!("Cannot evict, len: {}, capacity: {}", self.len(), self.capacity));
      }
    }
    Ok(())
  }
}

// LRU entry for page ids.
struct LRUEntry {
  prev: Option<PageID>,
  next: Option<PageID>,
}

// LRU cache for page ids.
// Used in page cache to keep track of pages.
pub struct LRU {
  head: Option<PageID>,
  tail: Option<PageID>,
  entries: HashMap<PageID, LRUEntry>
}

impl LRU {
  // Creates new LRU instance.
  pub fn new() -> Self {
    Self { head: None, tail: None, entries: HashMap::new() }
  }

  // Returns true if the LRU cache is empty.
  // Used mainly for testing.
  pub fn is_empty(&self) -> bool {
    self.head.is_none() && self.tail.is_none() && self.entries.len() == 0
  }

  // Internal function to get LRUEntry reference
  fn get_lru(&self, id: PageID) -> &LRUEntry {
    self.entries.get(&id).expect(&format!("Entry {} is not found", id))
  }

  // Internal function to get mutable LRUEntry reference
  fn get_lru_mut(&mut self, id: PageID) -> &mut LRUEntry {
    self.entries.get_mut(&id).expect(&format!("Entry {} is not found", id))
  }

  // Adds an item to the LRU cache.
  pub fn add(&mut self, id: PageID) {
    let mut entry = LRUEntry { prev: None, next: None };
    // Update the entry to point to the current head
    if let Some(curr_id) = self.head {
      entry.next = Some(curr_id);
      let curr = self.get_lru_mut(curr_id);
      curr.prev = Some(id);
    }
    // Update the head to the new entry
    self.head = Some(id);
    // If it is the first element, update the tail
    if self.tail.is_none() {
      self.tail = self.head;
    }
    // Finally, insert the entry into the map
    self.entries.insert(id, entry);
  }

  // Removes an item from the LRU cache.
  pub fn remove(&mut self, id: PageID) {
    // Remove the entry from the map
    let entry_opt = self.entries.remove(&id);

    if let Some(entry) = entry_opt {
      // Update prev pointer for the entry
      match entry.prev {
        Some(prev_id) => {
          let prev = self.get_lru_mut(prev_id);
          prev.next = entry.next;
        },
        None => {
          // The previous pointer does not exist, update the current head
          self.head = entry.next;
        }
      }
      // Update next pointer for the entry
      match entry.next {
        Some(next_id) => {
          let next = self.get_lru_mut(next_id);
          next.prev = entry.prev;
        },
        None => {
          // The next pointer does not exist, update the current tail
          self.tail = entry.prev;
        }
      }
    }
  }

  // Evicts an item according to LRU policy.
  pub fn evict(&mut self) -> Option<PageID> {
    if let Some(id) = self.tail {
      self.remove(id);
      Some(id)
    } else {
      None
    }
  }
}

// Iterator to traverse LRU entries.
pub struct LRUIter<'a> {
  lru: &'a LRU,
  ptr: Option<PageID>,
  direct: bool,
}

impl<'a> LRUIter<'a> {
  // Creates an iterator with direct traversal (most recently used first)
  // or with LRU order (least recently used first).
  pub fn new(lru: &'a LRU, direct: bool) -> Self {
    Self { lru: lru, ptr: if direct { lru.head } else { lru.tail }, direct: direct }
  }
}

impl<'a> Iterator for LRUIter<'a> {
  type Item = PageID;

  fn next(&mut self) -> Option<Self::Item> {
    if let Some(id) = self.ptr {
      let entry = self.lru.get_lru(id);
      self.ptr = if self.direct { entry.next } else { entry.prev };
      Some(id)
    } else {
      None
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  const PAGE_SIZE_4KB: usize = 4 * 1024;

  #[test]
  fn test_page_lru_evict_empty() {
    let mut lru = LRU::new();
    assert_eq!(lru.evict(), None);
    assert!(lru.is_empty());
  }

  #[test]
  fn test_page_lru_remove_empty() {
    let mut lru = LRU::new();
    lru.remove(123);
    assert!(lru.is_empty());
  }

  #[test]
  fn test_page_lru_add() {
    let mut lru = LRU::new();
    for id in 1..10 {
      lru.add(id);
    }
    assert!(!lru.is_empty());
    let mut res = Vec::new();
    while !lru.is_empty() {
      res.push(lru.evict().unwrap());
    }
    assert_eq!(res, vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);
    assert!(lru.is_empty());
  }

  #[test]
  fn test_page_lru_add_remove() {
    let mut lru = LRU::new();
    for id in 1..6 {
      lru.add(id);
    }
    lru.remove(1);
    lru.remove(3);
    lru.add(1);
    lru.remove(5);
    lru.add(3);
    lru.add(5);

    let mut res = Vec::new();
    while !lru.is_empty() {
      res.push(lru.evict().unwrap());
    }
    assert_eq!(res, vec![2, 4, 1, 3, 5]);
    assert!(lru.is_empty());
  }

  // Simple inmemory page manager that stores pages in a vector
  struct MemPageManager {
    pages: Vec<Page>,
    deleted: Vec<PageID>,
  }

  impl MemPageManager {
    fn new() -> Self {
      Self { pages: Vec::new(), deleted: Vec::new() }
    }

    fn check_deleted(&self, page_id: PageID) -> Res<()> {
      for id in &self.deleted {
        if *id == page_id {
          return Err(err!("Page {} is deleted", page_id));
        }
      }
      Ok(())
    }
  }

  impl PageManager for MemPageManager {
    fn alloc_page(&mut self, page_type: PageType, page_size: usize) -> Res<Page> {
      let id = self.pages.len() as u32;
      let page = Page::empty(page_type, id, page_size);
      self.pages.push(page.clone());
      Ok(page)
    }

    fn read_page(&mut self, page_id: PageID) -> Res<Page> {
      self.check_deleted(page_id)?;
      Ok(self.pages[page_id as usize].clone())
    }

    fn write_page(&mut self, page: Page) -> Res<()> {
      let page_id = page.id();
      self.check_deleted(page_id)?;
      self.pages[page_id as usize] = page;
      Ok(())
    }

    fn free_page(&mut self, page_id: PageID) -> Res<()> {
      self.deleted.push(page_id);
      Ok(())
    }
  }

  #[test]
  fn test_page_cache_multiple_alloc() {
    let mut manager = MemPageManager::new();
    let mut cache = PageCache::new(5, &mut manager);

    let mut page1 = cache.alloc_page(PageType::Leaf, PAGE_SIZE_4KB).unwrap();
    let mut page2 = cache.alloc_page(PageType::Leaf, PAGE_SIZE_4KB).unwrap();

    assert_eq!(cache.len(), 2);

    page1.is_dirty = true;
    page2.is_dirty = true;

    cache.put_page(page1).unwrap();
    cache.put_page(page2).unwrap();

    assert_eq!(cache.len(), 2);
  }

  #[test]
  fn test_page_cache_alloc_error() {
    let mut manager = MemPageManager::new();
    let mut cache = PageCache::new(5, &mut manager);

    for _ in 0..5 {
      cache.alloc_page(PageType::Leaf, PAGE_SIZE_4KB).unwrap();
    }
    assert!(cache.alloc_page(PageType::Leaf, PAGE_SIZE_4KB).is_err());
  }

  #[test]
  fn test_page_cache_get_error() {
    let mut manager = MemPageManager::new();
    let mut cache = PageCache::new(5, &mut manager);

    for _ in 0..10 {
      let page = cache.alloc_page(PageType::Leaf, PAGE_SIZE_4KB).unwrap();
      cache.put_page(page).unwrap();
    }

    for id in 0..5 {
      cache.get_page(id).unwrap();
    }

    assert!(cache.get_page(6).is_err());
  }

  #[test]
  fn test_page_cache_get_put() {
    let mut manager = MemPageManager::new();
    let mut cache = PageCache::new(5, &mut manager);

    for _ in 0..10 {
      let page = cache.alloc_page(PageType::Leaf, PAGE_SIZE_4KB).unwrap();
      cache.put_page(page).unwrap();
    }

    for id in (0..10).rev() {
      let page = cache.get_page(id).unwrap();
      cache.put_page(page).unwrap();
    }

    let iter = LRUIter::new(&cache.lru, false); // tail first
    let res: Vec<PageID> = iter.collect();
    assert_eq!(res, vec![4, 3, 2, 1, 0]);
  }

  #[test]
  fn test_page_cache_free() {
    let mut manager = MemPageManager::new();
    let mut cache = PageCache::new(5, &mut manager);

    for _ in 0..10 {
      let page = cache.alloc_page(PageType::Leaf, PAGE_SIZE_4KB).unwrap();
      cache.put_page(page).unwrap();
    }

    for id in 0..10 {
      cache.free_page(id).unwrap();
    }

    let iter = LRUIter::new(&cache.lru, true);
    let res: Vec<PageID> = iter.collect();
    assert_eq!(res, vec![]);

    assert!(cache.lru.is_empty());
    assert_eq!(cache.len(), 0);
    assert_eq!(&manager.deleted, &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
  }

  #[test]
  fn test_page_cache_multiple_get() {
    let mut manager = MemPageManager::new();
    let mut cache = PageCache::new(5, &mut manager);

    for _ in 0..5 {
      let page = cache.alloc_page(PageType::Leaf, PAGE_SIZE_4KB).unwrap();
      cache.put_page(page).unwrap();
    }

    let mut page1 = cache.get_page(1).unwrap();
    let mut page2 = cache.get_page(2).unwrap();

    assert_eq!(cache.len(), 5);

    let iter = LRUIter::new(&cache.lru, true);
    let res: Vec<PageID> = iter.collect();
    assert_eq!(res, vec![4, 3, 0]);

    page1.is_dirty = true;
    page2.is_dirty = true;

    cache.put_page(page1).unwrap();
    cache.put_page(page2).unwrap();

    assert_eq!(cache.len(), 5);

    let iter = LRUIter::new(&cache.lru, true);
    let res: Vec<PageID> = iter.collect();
    assert_eq!(res, vec![2, 1, 4, 3, 0]);
  }

  #[test]
  fn test_page_cache_state_get_page() {
    let mut manager = MemPageManager::new();
    let mut cache = PageCache::new(5, &mut manager);

    let page = cache.alloc_page(PageType::Leaf, PAGE_SIZE_4KB).unwrap();

    let res1 = cache.get_page(page.id());
    assert!(res1.is_err());
    // The subsequent call should be the same error
    let res2 = cache.get_page(page.id());
    assert_eq!(res1, res2);
  }

  #[test]
  fn test_page_cache_state_put_page() {
    let mut manager = MemPageManager::new();

    let page = manager.alloc_page(PageType::Leaf, PAGE_SIZE_4KB).unwrap();

    let mut cache = PageCache::new(5, &mut manager);

    let res1 = cache.put_page(page);
    assert!(res1.is_err());
    assert_eq!(cache.entries.len(), 0);
  }

  #[test]
  fn test_page_cache_state_free_page() {
    let mut manager = MemPageManager::new();
    let mut cache = PageCache::new(5, &mut manager);

    let page = cache.alloc_page(PageType::Leaf, PAGE_SIZE_4KB).unwrap();

    let res1 = cache.free_page(page.id());
    assert!(res1.is_err());

    // The subsequent call should be the same error
    let res2 = cache.free_page(page.id());
    assert_eq!(res1, res2);
  }
}
