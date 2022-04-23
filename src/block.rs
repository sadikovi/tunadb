use std::collections::HashMap;
use crate::storage::StorageManager;

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
  pub page_size: usize,
  pub num_pages: usize,
  pub num_free_pages: usize,
  pub is_proxy_cache: bool,
}

impl BlockManagerStats {
  // Returns empty/default statistics.
  pub fn empty() -> Self {
    Self {
      page_size: 0,
      num_pages: 0,
      num_free_pages: 0,
      is_proxy_cache: false
    }
  }
}
