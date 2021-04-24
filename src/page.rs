//! Module for page definition.
use std::collections::HashMap;
use std::sync::RwLock;
use crate::error::Res;

type PageID = u32;

#[derive(Clone)]
pub struct Page {
  id: PageID,
  is_dirty: bool,
}

/// Page manager that maintains pages on disk or in memory
pub trait PageManager {
  fn alloc_page(&mut self) -> Res<Page>;
  fn read_page(&mut self, page_id: PageID) -> Res<Page>;
  fn write_page(&mut self, page: Page) -> Res<()>;
  fn free_page(&mut self, page_id: PageID) -> Res<()>;
}

macro_rules! read_acq {
  ($cache_func:expr) => {
    $cache_func.unwrap().try_read().unwrap()
  };
}

macro_rules! write_acq {
  ($cache_func:expr) => {
    $cache_func.unwrap().try_write().unwrap()
  };
}

#[derive(Clone, Copy)]
struct LRU {
  id: PageID,
  prev: Option<PageID>,
  next: Option<PageID>,
}

struct CacheEntry {
  page: RwLock<Page>,
  lru: LRU,
}

pub struct PageCache<'a> {
  capacity: usize,
  entries: HashMap<PageID, CacheEntry>,
  page_mngr: &'a mut dyn PageManager,
  head: Option<PageID>,
  tail: Option<PageID>,
}

impl<'a> PageCache<'a> {
  pub fn new(capacity: usize, page_mngr: &'a mut dyn PageManager) -> Self {
    Self {
      capacity: capacity,
      entries: HashMap::with_capacity(capacity),
      page_mngr: page_mngr,
      head: None,
      tail: None,
    }
  }

  pub fn len(&self) -> usize {
    self.entries.len()
  }

  pub fn alloc(&mut self) -> Res<&RwLock<Page>> {
    while self.entries.len() >= self.capacity {
      self.evict()?;
    }
    let page = self.page_mngr.alloc_page()?;
    let page_id = page.id;
    // Insert the new page and update LRU for the page
    self.insert(page)?;
    self.get(page_id)
  }

  pub fn get(&mut self, page_id: PageID) -> Res<&RwLock<Page>> {
    let lru_opt = match self.entries.get(&page_id) {
      Some(entry) => Some(entry.lru),
      None => None,
    };

    match lru_opt {
      Some(mut lru) => {
        self.unlink(&mut lru)?;
        self.link(&mut lru)?;
        let entry = self.entries.get_mut(&page_id).ok_or(err!("Page {} not found", page_id))?;
        entry.lru = lru;
      },
      None => {
        // evict the entry if the map is full
        while self.entries.len() >= self.capacity {
          self.evict()?;
        }
        // Extract a new page
        let page = self.page_mngr.read_page(page_id)?;
        // Insert the new page and update LRU for the page
        self.insert(page)?;
      },
    }

    self.entries.get(&page_id).map(|entry| &entry.page)
      .ok_or(err!("Page {} not found", page_id))
  }

  pub fn delete(&mut self, page_id: PageID) -> Res<()> {
    let entry_opt = self.entries.remove(&page_id);
    if let Some(mut entry) = entry_opt {
      self.unlink(&mut entry.lru)?;
    }
    self.page_mngr.free_page(page_id)
  }

  fn insert(&mut self, page: Page) -> Res<()> {
    let page_id = page.id;
    // Update LRU for the page
    let mut lru = LRU { id: page_id, prev: None, next: None };
    self.link(&mut lru)?;
    // Insert the new page and LRU
    self.entries.insert(
      page_id,
      CacheEntry {
        page: RwLock::new(page),
        lru: lru,
      }
    );
    Ok(())
  }

  fn evict(&mut self) -> Res<()> {
    if let Some(page_id) = self.tail {
      let mut entry = self.entries.remove(&page_id).ok_or(err!("Page {} not found", page_id))?;
      self.unlink(&mut entry.lru)?;
      let page = entry.page.into_inner()?;
      if page.is_dirty {
        self.page_mngr.write_page(page)?;
      }
    }
    Ok(())
  }

  fn unlink(&mut self, lru: &mut LRU) -> Res<()> {
    // entry->prev->next = entry->next
    if let Some(prev_id) = lru.prev {
      let mut prev = self.entries.get_mut(&prev_id)
        .ok_or(err!["Page {} not found", prev_id])?;
      prev.lru.next = lru.next;
    } else {
      // entry is the head
      self.head = lru.next;
    }

    // entry->next->prev = entry->prev
    if let Some(next_id) = lru.next {
      let mut next = self.entries.get_mut(&next_id)
        .ok_or(err!["Page {} not found", next_id])?;
      next.lru.prev = lru.prev;
    } else {
      // entry is the tail
      self.tail = lru.prev;
    }

    lru.next = None;
    lru.prev = None;

    Ok(())
  }

  fn link(&mut self, lru: &mut LRU) -> Res<()> {
    if let Some(head_id) = self.head {
      let mut head = self.entries.get_mut(&head_id)
        .ok_or(err!["Page {} not found", head_id])?;
      head.lru.prev = Some(lru.id);
      lru.next = self.head;
    }
    self.head = Some(lru.id);
    if self.tail.is_none() {
      self.tail = self.head;
    }
    Ok(())
  }
}

pub struct PageCacheIter<'a> {
  cache: &'a PageCache<'a>,
  ptr: Option<PageID>,
  direct: bool,
}

impl<'a> PageCacheIter<'a> {
  pub fn new(cache: &'a PageCache<'a>, direct: bool) -> Self {
    Self {
      cache: cache,
      ptr: if direct { cache.head } else { cache.tail },
      direct: direct,
    }
  }
}

impl<'a> Iterator for PageCacheIter<'a> {
  type Item = &'a RwLock<Page>;

  fn next(&mut self) -> Option<Self::Item> {
    if let Some(page_id) = self.ptr {
      let entry_opt = self.cache.entries.get(&page_id);
      if let Some(entry) = entry_opt {
        self.ptr = if self.direct { entry.lru.next } else { entry.lru.prev };
      }
      entry_opt.map(|entry| &entry.page)
    } else {
      None
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

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

  // Helper function to collect page ids into a vector
  fn collect_iter(iter: &mut PageCacheIter) -> Vec<PageID> {
    iter.map(|res| res.try_read().unwrap().id).collect()
  }

  fn test_lru_direct<'a>(cache: &'a PageCache<'a>, exp: Vec<PageID>) {
    assert_eq!(collect_iter(&mut PageCacheIter::new(cache, true)), exp, "Direct LRU");
  }

  fn test_lru_reverse<'a>(cache: &'a PageCache<'a>, exp: Vec<PageID>) {
    assert_eq!(collect_iter(&mut PageCacheIter::new(cache, false)), exp, "Direct LRU");
  }

  #[test]
  fn test_page_cache_empty() {
    let mut mngr = MemPageManager::new();
    let cache = PageCache::new(10, &mut mngr);
    assert_eq!(cache.len(), 0);

    let mut iter = PageCacheIter::new(&cache, true);
    assert!(iter.next().is_none());

    let mut iter = PageCacheIter::new(&cache, false);
    assert!(iter.next().is_none());
  }

  #[test]
  fn test_page_cache_delete_empty() {
    let mut mngr = MemPageManager::new();
    let mut cache = PageCache::new(10, &mut mngr);

    cache.delete(123).unwrap();

    assert_eq!(cache.len(), 0);
    test_lru_direct(&cache, vec![]);
    test_lru_reverse(&cache, vec![]);

    // We still try to delete in page manager even if the page is not in the cache
    assert_eq!(mngr.deleted, vec![123]);
  }

  #[test]
  fn test_page_cache_alloc() {
    let mut mngr = MemPageManager::new();
    let mut cache = PageCache::new(10, &mut mngr);

    {
      let page = read_acq![cache.alloc()];
      assert_eq!(page.id, 0);
    }
    {
      let page = read_acq![cache.alloc()];
      assert_eq!(page.id, 1);
    }

    assert_eq!(cache.len(), 2);

    test_lru_direct(&cache, vec![1, 0]);
    test_lru_reverse(&cache, vec![0, 1]);
  }

  #[test]
  fn test_page_cache_alloc_delete() {
    let mut mngr = MemPageManager::new();
    let mut cache = PageCache::new(10, &mut mngr);

    cache.alloc().unwrap();
    cache.delete(0).unwrap();

    assert_eq!(cache.len(), 0);

    test_lru_direct(&cache, vec![]);
    test_lru_reverse(&cache, vec![]);
  }

  #[test]
  fn test_page_cache_alloc_get() {
    let mut mngr = MemPageManager::new();
    let mut cache = PageCache::new(10, &mut mngr);

    // 2 -> 1 -> 0
    {
      cache.alloc().unwrap();
      cache.alloc().unwrap();
      cache.alloc().unwrap();
      cache.get(0).unwrap();
      cache.get(1).unwrap();
    }

    test_lru_direct(&cache, vec![1, 0, 2]);
    test_lru_reverse(&cache, vec![2, 0, 1]);
  }

  #[test]
  fn test_page_cache_alloc_get_evict() {
    let mut mngr = MemPageManager::new();
    let mut cache = PageCache::new(5, &mut mngr);

    for _ in 0..10 {
      cache.alloc().unwrap();
    }

    assert_eq!(cache.len(), 5);

    for i in (0..10).rev() {
      cache.get(i).unwrap();
    }

    assert_eq!(cache.len(), 5);

    test_lru_direct(&cache, vec![0, 1, 2, 3, 4]);
    test_lru_reverse(&cache, vec![4, 3, 2, 1, 0]);
  }

  #[test]
  fn test_page_cache_alloc_get_delete() {
    let mut mngr = MemPageManager::new();
    let mut cache = PageCache::new(5, &mut mngr);

    for _ in 0..10 {
      cache.alloc().unwrap();
    }

    for i in 0..10 {
      cache.delete(i).unwrap();
    }

    assert_eq!(cache.len(), 0);
    test_lru_direct(&cache, vec![]);
    test_lru_reverse(&cache, vec![]);

    assert_eq!(mngr.deleted.len(), 10);
  }

  #[test]
  fn test_page_cache_get_delete() {
    let mut mngr = MemPageManager::new();
    let mut cache = PageCache::new(5, &mut mngr);

    for _ in 0..10 {
      cache.alloc().unwrap();
    }

    cache.get(3).unwrap();
    cache.delete(3).unwrap();

    assert_eq!(cache.len(), 4);
    test_lru_direct(&cache, vec![9, 8, 7, 6]);
    test_lru_reverse(&cache, vec![6, 7, 8, 9]);

    assert_eq!(mngr.deleted, vec![3]);
  }
}
