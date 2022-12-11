use std::collections::HashMap;
use crate::storage::smgr::StorageManager;

// BlockManager is wrapper trait on top of StorageManager that allows to implement page cache,
// commit and roll back changes.
pub trait BlockManager {
  // The current page size in bytes.
  fn page_size(&self) -> usize;
  // Loads page from disk or memory into the provided buffer.
  fn load(&mut self, pid: u32, buf: &mut [u8]);
  // Stores the buffer in memory or on disk and returns page id.
  fn store(&mut self, buf: &[u8]) -> u32;
  // Frees the corresponding page id.
  fn free(&mut self, pid: u32);
  // Commits all of the pages and returns a mapping of virtual page ids to physical page ids.
  fn commit(&mut self) -> HashMap<u32, u32>;
  // Rolls back all of the changes that have been made so far.
  fn rollback(&mut self);
  // Returns a reference to the underlying StorageManager.
  fn get_mngr(&self) -> &StorageManager;
  // Returns a mutable reference to the underlying StorageManager.
  fn get_mngr_mut(&mut self) -> &mut StorageManager;
  // Statistics and metrics for page cache and StorageManager.
  fn stats(&self) -> BlockManagerStats;
}

#[derive(Clone, Copy, Debug)]
pub struct BlockManagerStats {
  pub page_size: usize, // in bytes
  pub num_pages: usize,
  pub num_free_pages: usize,
  pub is_proxy_cache: bool,
  pub cache_mem_used: usize, // in bytes
  pub cache_mem_max: usize, // in bytes
  pub cache_num_hits: usize,
  pub cache_num_misses: usize,
}

impl BlockManagerStats {
  // Returns memory used by cache as percentage, e.g. 58%.
  pub fn cache_mem_used_pcnt(&self) -> f64 {
    if self.cache_mem_max == 0 {
      0f64
    } else {
      self.cache_mem_used as f64 / self.cache_mem_max as f64 * 100f64
    }
  }

  // Returns percentage of cache hits, e.g. 32%.
  pub fn cache_hit_pcnt(&self) -> f64 {
    if self.cache_num_hits + self.cache_num_misses == 0 {
      0f64
    } else {
      self.cache_num_hits as f64 / (self.cache_num_hits + self.cache_num_misses) as f64 * 100f64
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  // Returns stats used in the unit tests below.
  fn get_test_stats() -> BlockManagerStats {
    BlockManagerStats {
      page_size: 1024,
      num_pages: 10,
      num_free_pages: 2,
      is_proxy_cache: false,
      cache_mem_used: 0,
      cache_mem_max: 0,
      cache_num_hits: 0,
      cache_num_misses: 0,
    }
  }

  #[test]
  fn test_block_stats_cache_mem_used_pcnt() {
    let mut stats = get_test_stats();

    stats.cache_mem_used = 0;
    stats.cache_mem_max = 0;
    assert_eq!(stats.cache_mem_used_pcnt(), 0 as f64);

    stats.cache_mem_used = 1024;
    stats.cache_mem_max = 0;
    assert_eq!(stats.cache_mem_used_pcnt(), 0 as f64);

    stats.cache_mem_used = 512;
    stats.cache_mem_max = 1024;
    assert_eq!(stats.cache_mem_used_pcnt(), 50 as f64);

    stats.cache_mem_used = 1024;
    stats.cache_mem_max = 1024;
    assert_eq!(stats.cache_mem_used_pcnt(), 100 as f64);
  }

  #[test]
  fn test_block_stats_cache_hit_pcnt() {
    let mut stats = get_test_stats();

    stats.cache_num_hits = 0;
    stats.cache_num_misses = 0;
    assert_eq!(stats.cache_hit_pcnt(), 0 as f64);

    stats.cache_num_hits = 0;
    stats.cache_num_misses = 10;
    assert_eq!(stats.cache_hit_pcnt(), 0 as f64);

    stats.cache_num_hits = 10;
    stats.cache_num_misses = 0;
    assert_eq!(stats.cache_hit_pcnt(), 100 as f64);

    stats.cache_num_hits = 10;
    stats.cache_num_misses = 10;
    assert_eq!(stats.cache_hit_pcnt(), 50 as f64);
  }
}
