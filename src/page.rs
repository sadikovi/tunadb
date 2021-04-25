//! Module for page definition.
use std::collections::HashMap;
use std::sync::RwLock;
use crate::error::Res;

/// Page id alias.
type PageID = u32;

/// Page is a fundamental unit of data in memory and on disk.
#[derive(Clone)]
pub struct Page {
  id: PageID,
  is_dirty: bool,
}

/// Page manager that maintains pages on disk or in memory.
pub trait PageManager {
  /// Creates new page and returns the page or a copy.
  fn alloc_page(&mut self) -> Res<Page>;
  /// Returns a copy of the page for the page id.
  fn read_page(&mut self, page_id: PageID) -> Res<Page>;
  /// Updates the page.
  fn write_page(&mut self, page: Page) -> Res<()>;
  /// Deletes the page for the page id.
  fn free_page(&mut self, page_id: PageID) -> Res<()>;
}

enum CacheEntry {
  Borrowed,
  Ref(Page),
}

/// Page cache, i.e. buffer pool, is a single threaded cache of pages in memory.
/// Currently implements the basic API that is needed to manage pages.
pub struct PageCache<'a> {
  capacity: usize,
  entries: HashMap<PageID, CacheEntry>,
  page_mngr: &'a mut dyn PageManager,
}

impl<'a> PageCache<'a> {
  /// Creates a new page cache with capacity and page manager.
  pub fn new(capacity: usize, page_mngr: &'a mut dyn PageManager) -> Self {
    Self {
      capacity: capacity,
      entries: HashMap::with_capacity(capacity),
      page_mngr: page_mngr,
    }
  }

  /// Returns the length of the entries in the cache.
  pub fn len(&self) -> usize {
    self.entries.len()
  }

  /// Creates a new page using page manager and puts it in the cache.
  pub fn alloc_page(&mut self) -> Res<Page> {
    let page = self.page_mngr.alloc_page()?;
    self.entries.insert(page.id, CacheEntry::Borrowed);
    Ok(page)
  }

  /// Returns a page that is in the cache or loads it from disk and stores in the cache.
  /// LRU entries are updated on each access.
  pub fn get_page(&mut self, page_id: PageID) -> Res<Page> {
    let exists = self.entries.get(&page_id).is_some();
    if exists {
      // Check if the page is borrowed
      match self.entries.insert(page_id, CacheEntry::Borrowed) {
        // Borrow the page
        Some(CacheEntry::Ref(page)) => Ok(page),
        // Page was already borrowed
        Some(CacheEntry::Borrowed) => Err(err!("Page {} was already borrowed", page_id)),
        // Page does not exist in the cache
        None => Err(err!("Page {} not found", page_id)),
      }
    } else {
      // Load from the disk and insert into the cache
      let page = self.page_mngr.read_page(page_id)?;
      self.entries.insert(page_id, CacheEntry::Borrowed);
      Ok(page)
    }
  }

  /// Returns page into the cache by replacing a default value.
  pub fn put_page(&mut self, page: Page) -> Res<()> {
    let page_id = page.id;
    match self.entries.insert(page_id, CacheEntry::Ref(page)) {
      // Replaced the correct page
      Some(CacheEntry::Borrowed) => Ok(()),
      _ => Err(err!("Page {} was replaced incorrectly", page_id)),
    }
  }

  /// Deletes page from the cache and on disk.
  /// If page is not in the cache, page manager still removes the page.
  pub fn free_page(&mut self, page_id: PageID) -> Res<()> {
    match self.entries.remove(&page_id) {
      // Page has been borrowed, we cannot delete it
      Some(CacheEntry::Borrowed) => Err(err!("Page {} was borrowed", page_id)),
      // It is okay to remove, it does not matter if the page is in the cache
      _ => self.page_mngr.free_page(page_id),
    }
  }
}

struct LRUEntry {
  id: PageID,
  prev: Option<PageID>,
  next: Option<PageID>,
}

struct LRU {
  head: Option<PageID>,
  tail: Option<PageID>,
  entries: HashMap<PageID, LRUEntry>
}

impl LRU {
  /// Creates new LRU instance.
  pub fn new() -> Self {
    Self { head: None, tail: None, entries: HashMap::new() }
  }

  /// Returns true if the LRU cache is empty.
  /// Used mainly for testing.
  pub fn is_empty(&self) -> bool {
    self.head.is_none() && self.tail.is_none() && self.entries.len() == 0
  }

  // Internal function to get LRUEntry from the map
  fn get_lru(&mut self, id: PageID) -> &mut LRUEntry {
    self.entries.get_mut(&id).expect(&format!("Entry {} is not found", id))
  }

  /// Adds an item to the LRU cache.
  pub fn add(&mut self, id: PageID) {
    let mut entry = LRUEntry { id: id, prev: None, next: None };
    // Update the entry to point to the current head
    if let Some(curr_id) = self.head {
      entry.next = Some(curr_id);
      let curr = self.get_lru(curr_id);
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

  /// Removes an item from the LRU cache.
  pub fn remove(&mut self, id: PageID) {
    // Remove the entry from the map
    let entry_opt = self.entries.remove(&id);

    if let Some(entry) = entry_opt {
      // Update prev pointer for the entry
      match entry.prev {
        Some(prev_id) => {
          let prev = self.get_lru(prev_id);
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
          let next = self.get_lru(next_id);
          next.prev = entry.prev;
        },
        None => {
          // The next pointer does not exist, update the current tail
          self.tail = entry.prev;
        }
      }
    }
  }

  /// Evicts an item according to LRU policy.
  pub fn evict(&mut self) -> Option<PageID> {
    if let Some(id) = self.tail {
      self.remove(id);
      Some(id)
    } else {
      None
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

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
    fn alloc_page(&mut self) -> Res<Page> {
      let id = self.pages.len() as u32;
      let page = Page { id: id, is_dirty: false };
      self.pages.push(page.clone());
      Ok(page)
    }

    fn read_page(&mut self, page_id: PageID) -> Res<Page> {
      self.check_deleted(page_id)?;
      Ok(self.pages[page_id as usize].clone())
    }

    fn write_page(&mut self, page: Page) -> Res<()> {
      let page_id = page.id;
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
  fn test_page_cache_simple() {
    let mut manager = MemPageManager::new();
    let mut cache = PageCache::new(5, &mut manager);

    let mut page1 = cache.alloc_page().unwrap();
    let mut page2 = cache.alloc_page().unwrap();

    assert_eq!(cache.len(), 2);

    page1.is_dirty = true;
    page2.is_dirty = true;

    cache.put_page(page1).unwrap();
    cache.put_page(page2).unwrap();

    assert_eq!(cache.len(), 2);
  }
}
