//! Module for page definition.
use std::collections::HashMap;
use std::sync::RwLock;
use crate::error::Res;

type PageID = u32;

pub struct Page {
  id: PageID,
}

/// Page manager that maintains pages on disk or in memory
pub trait PageManager {
  fn alloc_page(&mut self) -> Res<Page>;
  fn read_page(&mut self, page_id: PageID) -> Res<Page>;
  fn write_page(&mut self, page: Page) -> Res<()>;
  fn free_page(&mut self, page_id: PageID) -> Res<()>;
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
        if self.entries.len() == self.capacity {
          self.evict()?;
        }
        // Extract a new page
        let page = self.page_mngr.read_page(page_id)?;
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
      },
    }

    self.entries.get(&page_id).map(|entry| &entry.page)
      .ok_or(err!("Page {} not found", page_id))
  }

  pub fn delete(&mut self, page_id: PageID) -> Res<()> {
    let entry_opt = self.entries.remove(&page_id);
    if let Some(mut entry) = entry_opt {
      self.unlink(&mut entry.lru)?;
      self.page_mngr.free_page(page_id)?;
    }
    Ok(())
  }

  pub fn len(&self) -> usize {
    self.entries.len()
  }

  fn evict(&mut self) -> Res<()> {
    if let Some(page_id) = self.tail {
      let mut entry = self.entries.remove(&page_id).ok_or(err!("Page {} not found", page_id))?;
      self.unlink(&mut entry.lru)?;
      self.page_mngr.write_page(
        entry.page.into_inner()?
      )?;
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
    lru.next = self.head;
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
