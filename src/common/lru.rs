use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::mem::size_of;

// ========================
// LRU cache implementation
// ========================

#[derive(Clone, Copy, Debug, PartialEq)]
struct LruCacheEntry<T: Copy + Debug + PartialEq> {
  prev: Option<T>,
  next: Option<T>,
}

#[derive(Debug)]
pub struct LruCache<T: Copy + Debug + PartialEq + Eq + Hash> {
  entries: HashMap<T, LruCacheEntry<T>>,
  pinned: HashMap<T, ()>,
  head: Option<T>, // most recently used
  tail: Option<T>, // least recently used
}

impl<T: Copy + Debug + PartialEq + Eq + Hash> LruCache<T> {
  // Creates a new instance of LRU cache.
  pub fn new() -> Self {
    Self { entries: HashMap::new(), pinned: HashMap::new(), head: None, tail: None }
  }

  // Number of entries in the cache.
  pub fn len(&self) -> usize {
    return self.entries.len()
  }

  // Number of pinned entries in the cache.
  pub fn pinned_len(&self) -> usize {
    return self.pinned.len()
  }

  // Pins an existing key in the cache so it cannot be evicted.
  pub fn pin(&mut self, key: T) {
    if self.entries.get(&key).is_some() {
      self.pinned.insert(key, ());
    }
  }

  // Unpins the key in the cache.
  pub fn unpin(&mut self, key: T) {
    self.pinned.remove(&key);
  }

  // Updates an existing key or inserts a new one as most recently used.
  pub fn update(&mut self, key: T) {
    self.remove(key);
    self.insert(key);
  }

  // Removes and returns the least recently used key.
  pub fn evict(&mut self) -> Option<T> {
    let mut curr = self.tail;
    while let Some(key) = curr {
      if self.pinned.get(&key).is_none() {
        self.remove(key);
        return Some(key);
      } else {
        curr = self.entries.get(&key).unwrap().prev;
      }
    }
    None
  }

  pub fn mem_usage(&self) -> usize {
    /* head */ size_of::<Option<T>>() +
    /* tail */ size_of::<Option<T>>() +
    /* entries */ self.entries.len() * (size_of::<T>() + size_of::<LruCacheEntry<T>>()) +
    /* pinned */ self.pinned.len() * size_of::<T>()
  }

  // Must be private, consider using `update()` instead.
  fn insert(&mut self, key: T) {
    assert!(self.entries.get(&key).is_none());
    self.entries.insert(key, LruCacheEntry { prev: None, next: self.head });
    if let Some(head) = self.head {
      let value = self.entries.get_mut(&head).unwrap();
      value.prev = Some(key);
    }
    self.head = Some(key);
    if self.tail.is_none() {
      self.tail = self.head;
    }
  }

  // Allows to remove cache entry.
  // If the entry does not exist, it is a no-op.
  pub fn remove(&mut self, key: T) {
    if let Some(entry) = self.entries.remove(&key) {
      if let Some(prev) = entry.prev {
        self.entries.get_mut(&prev).unwrap().next = entry.next;
      } else {
        self.head = entry.next;
      }
      if let Some(next) = entry.next {
        self.entries.get_mut(&next).unwrap().prev = entry.prev;
      } else {
        self.tail = entry.prev;
      }
    }
  }

  // Clears the content of LRU cache.
  pub fn clear(&mut self) {
    self.entries.clear();
    self.pinned.clear();
    self.head = None;
    self.tail = None;
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use rand::prelude::*;

  fn collect_forward(cache: &LruCache::<u32>) -> Vec<u32> {
    let mut vec = Vec::new();
    let mut tmp = cache.head;
    while let Some(key) = tmp {
      vec.push(key);
      tmp = cache.entries.get(&key).unwrap().next;
    }
    vec
  }

  fn collect_backward(cache: &LruCache::<u32>) -> Vec<u32> {
    let mut vec = Vec::new();
    let mut tmp = cache.tail;
    while let Some(key) = tmp {
      vec.push(key);
      tmp = cache.entries.get(&key).unwrap().prev;
    }
    vec
  }

  #[test]
  fn test_util_lru_update_first_element() {
    let mut cache = LruCache::<u32>::new();
    cache.update(1);

    assert_eq!(cache.entries.get(&1), Some(&LruCacheEntry { prev: None, next: None }));
    assert_eq!(cache.head, Some(1));
    assert_eq!(cache.tail, Some(1));
  }

  #[test]
  fn test_util_lru_update_head() {
    let mut cache = LruCache::<u32>::new();
    cache.update(1);
    cache.update(1);

    assert_eq!(cache.entries.get(&1), Some(&LruCacheEntry { prev: None, next: None }));
    assert_eq!(cache.head, Some(1));
    assert_eq!(cache.tail, Some(1));
  }

  #[test]
  fn test_util_lru_evict_empty() {
    let mut cache = LruCache::<u32>::new();
    assert_eq!(cache.evict(), None);
  }

  #[test]
  fn test_util_lru_update_evict_head() {
    let mut cache = LruCache::<u32>::new();
    cache.update(1);
    cache.evict();

    assert_eq!(cache.entries.len(), 0);
    assert_eq!(cache.head, None);
    assert_eq!(cache.tail, None);
  }

  #[test]
  fn test_util_lru_update_evict_update_head() {
    let mut cache = LruCache::<u32>::new();
    cache.update(1);
    cache.evict();
    cache.update(2);

    assert_eq!(cache.entries.get(&2), Some(&LruCacheEntry { prev: None, next: None }));
    assert_eq!(cache.head, Some(2));
    assert_eq!(cache.tail, Some(2));
  }

  #[test]
  fn test_util_lru_update_many_elements() {
    let mut cache = LruCache::<u32>::new();
    cache.update(1);
    cache.update(2);
    cache.update(3);
    cache.update(4);
    cache.update(2);

    assert_eq!(collect_forward(&cache), vec![2, 4, 3, 1]);
    assert_eq!(collect_backward(&cache), vec![1, 3, 4, 2]);
    assert_eq!(cache.entries.get(&2), Some(&LruCacheEntry { prev: None, next: Some(4) }));
    assert_eq!(cache.entries.get(&1), Some(&LruCacheEntry { prev: Some(3), next: None }));
    assert_eq!(cache.head, Some(2));
    assert_eq!(cache.tail, Some(1));
  }

  #[test]
  fn test_util_lru_evict_many_elements() {
    let mut cache = LruCache::<u32>::new();
    cache.update(1);
    cache.update(2);
    cache.update(3);
    cache.update(4);
    cache.update(2);

    let mut vec = Vec::new();
    while let Some(key) = cache.evict() {
      vec.push(key);
    }
    assert_eq!(vec, vec![1, 3, 4, 2]);

    assert_eq!(cache.len(), 0);
  }

  #[test]
  fn test_util_lru_mem_usage() {
    let mut cache = LruCache::<u32>::new();
    cache.update(1);
    assert_eq!(cache.mem_usage(), 8 /* head */ + 8 /* tail */ + 16 + 4);
    cache.update(2);
    assert_eq!(cache.mem_usage(), 8 /* head */ + 8 /* tail */ + 2 * (16 + 4));
    cache.pin(2);
    assert_eq!(cache.mem_usage(), 8 /* head */ + 8 /* tail */ + 2 * (16 + 4) + 1 * 4);
  }

  #[test]
  fn test_util_lru_pin_non_existent() {
    let mut cache = LruCache::<u32>::new();
    cache.update(1);
    cache.pin(2);

    assert_eq!(cache.pinned_len(), 0);
    assert_eq!(cache.len(), 1);
  }

  #[test]
  fn test_util_lru_unpin_non_existent() {
    let mut cache = LruCache::<u32>::new();
    cache.update(1);
    cache.pin(1);
    cache.unpin(2);

    assert_eq!(cache.pinned_len(), 1);
    assert_eq!(cache.len(), 1);
  }

  #[test]
  fn test_util_lru_pin_evict() {
    let mut cache = LruCache::<u32>::new();
    cache.update(1);
    cache.update(2);
    cache.update(3);

    cache.pin(2);

    assert_eq!(cache.evict(), Some(1));
    assert_eq!(cache.evict(), Some(3));
    assert_eq!(cache.evict(), None);

    cache.unpin(2);

    assert_eq!(cache.evict(), Some(2));
    assert_eq!(cache.evict(), None);
  }

  #[test]
  fn test_util_lru_pin_all_evict() {
    let mut cache = LruCache::<u32>::new();
    for i in 0..10 {
      cache.update(i);
    }
    for i in 0..10 {
      cache.pin(i);
    }
    assert_eq!(cache.evict(), None);

    for i in 0..10 {
      cache.unpin(i);
    }
    for _ in 0..10 {
      assert!(cache.evict().is_some());
    }
  }

  #[test]
  fn test_util_lru_clear() {
    let mut cache = LruCache::<u32>::new();
    for i in 0..200 {
      cache.update(i);
    }

    for i in 0..10 {
      cache.pin(i);
    }

    for _ in 0..10 {
      assert!(cache.evict().is_some());
    }

    cache.clear();

    assert_eq!(cache.entries.len(), 0);
    assert_eq!(cache.pinned.len(), 0);
    assert_eq!(cache.head, None);
    assert_eq!(cache.tail, None);

    // There should be no items for eviction.
    assert_eq!(cache.evict(), None);
  }

  // LRU cache fuzz testing

  #[test]
  fn test_util_lru_fuzz_update_evict() {
    let num_iterations = 100;
    let num_keys = 100;

    for _ in 0..num_iterations {
      let mut vec = Vec::<u32>::new();
      for _ in 0..10 {
        for key in 0..num_keys {
          vec.push(key);
        }
      }

      vec.shuffle(&mut thread_rng());

      let mut cache = LruCache::<u32>::new();
      for &key in &vec[..] {
        cache.update(key);
      }

      let expected = collect_backward(&cache);
      assert_eq!(expected.len(), num_keys as usize);
      assert_eq!(cache.len(), expected.len());

      for &key in &expected[..] {
        assert_eq!(cache.evict(), Some(key));
      }
      assert_eq!(cache.evict(), None);
      assert_eq!(cache.len(), 0);
    }
  }
}
