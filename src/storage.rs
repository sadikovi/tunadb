use std::cmp;
use std::collections::HashSet;
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::Path;
use crate::error::Res;

// File descriptor and StorageManager code.
// All methods do not return `Res` because any error that occurs at this level is considered
// to be unrecoverable and indicates either an OS-level error, e.g. no space left, or a bug in
// the code.

enum Descriptor {
  // File-based storage.
  Disk { fd: File },
  // In-memory storage.
  Mem { data: Vec<u8> },
}

impl Descriptor {
  // Creates a new descriptor backed by a file.
  fn disk(path: &str) -> Self {
    let fd = OpenOptions::new().read(true).write(true).create(true).open(path);
    Descriptor::Disk { fd: res!(fd, "Failed to open {}", path) }
  }

  // Creates a new in-memory descriptor.
  fn mem(capacity: usize) -> Self {
    let data = Vec::with_capacity(capacity);
    Descriptor::Mem { data }
  }

  // Reads data into the provided buffer at the position.
  #[inline]
  fn read(&mut self, pos: u64, buf: &mut [u8]) {
    assert!(pos + buf.len() as u64 <= self.len(), "Read past EOF: pos {} len {}", pos, buf.len());

    match self {
      Descriptor::Disk { fd } => {
        res!(fd.seek(SeekFrom::Start(pos)), "Failed to seek to pos {}", pos);
        res!(fd.read_exact(buf), "Failed to read exactly {} bytes at pos {}", buf.len(), pos);
      },
      Descriptor::Mem { data } => {
        let pos = pos as usize;
        res!(
          (&mut data[pos..pos + buf.len()].as_ref()).read_exact(buf),
          "Failed to read exactly {} bytes at pos {}", buf.len(), pos
        );
      },
    }
  }

  // Writes data at the specified position.
  #[inline]
  fn write(&mut self, pos: u64, buf: &[u8]) {
    assert!(pos <= self.len(), "Write past EOF: pos {} len {}", pos, buf.len());

    match self {
      Descriptor::Disk { fd } => {
        res!(fd.seek(SeekFrom::Start(pos)), "Failed to seek to pos {}", pos);
        res!(fd.write_all(buf), "Failed to write {} bytes at pos {}", buf.len(), pos);
        res!(fd.flush(), "Failed to flush the file descriptor");
        // TODO: call self.fd.sync_all()
      },
      Descriptor::Mem { data } => {
        let pos = pos as usize;
        // Write has append semantics
        let min_len = cmp::min(buf.len(), data[pos..].len());
        res!(
          data[pos..pos + min_len].as_mut().write_all(&buf[0..min_len]),
          "Failed to write {} bytes at pos {}", buf.len(), pos
        );
        if min_len < buf.len() {
          // Write the rest of the data
          data.extend_from_slice(&buf[min_len..]);
        }
      },
    }
  }

  // Truncates to the provided length, `len` must be less than or equal to length.
  #[inline]
  fn truncate(&mut self, len: u64) {
    let curr_len = self.len();
    assert!(len <= curr_len, "Failed to truncate to len {}, curr_len {}", len, curr_len);

    match self {
      Descriptor::Disk { fd } => {
        if len < curr_len {
          res!(fd.set_len(len), "Failed to set file length as {} bytes", len);
        }
      },
      Descriptor::Mem { data } => {
        if len < curr_len {
          data.truncate(len as usize);
        }
      },
    }
  }

  // Total length in bytes of the file or memory buffer, used for appends.
  #[inline]
  fn len(&self) -> u64 {
    match self {
      Descriptor::Disk { fd } => res!(fd.metadata().map(|m| m.len())),
      Descriptor::Mem { data } => data.len() as u64,
    }
  }

  // Total amount of memory (in bytes) used by the descriptor.
  #[inline]
  fn estimated_mem_usage(&self) -> usize {
    match self {
      Descriptor::Disk { .. } => 0,
      // This is indicator of memory used, not allocated.
      // Technically, this should probably be capacity of the underlying vector;
      // however, we use length for debugging purposes
      Descriptor::Mem { data } => data.len(),
    }
  }
}

impl Drop for Descriptor {
  fn drop(&mut self) {
    match self {
      Descriptor::Disk { fd } => {
        // Sync the content of the file to disk including all of the OS internal metadata.
        res!(fd.sync_all());
      },
      Descriptor::Mem { .. } => {
        // Do nothing, the underlying vector will be dropped automatically.
      },
    }
  }
}

const MAGIC: &[u8] = &[b'T', b'U', b'N', b'A'];
// We have a fixed header size, see sync() method for more information.
const DB_HEADER_SIZE: usize = 32;
pub const MIN_PAGE_SIZE: u32 = 16;
pub const MAX_PAGE_SIZE: u32 = 1 * 1024 * 1024; // 1MB
pub const DEFAULT_PAGE_SIZE: u32 = 4096; // 4KB
pub const INVALID_PAGE_ID: u32 = u32::MAX;

// Meta block magic.
const META_PAGE_MAGIC: &[u8] = &[b'M', b'E', b'T', b'A'];
// Meta block offset at the beginning of the page:
//   magic (4 bytes)
//   next page (4 bytes)
//   count (4 bytes)
const META_OFFSET: usize = 12;

// Calculates the absolute position of a page depending on the page size.
// This is needed so we can account for the database header size.
#[inline]
fn pos(page_id: u32, page_size: u32) -> u64 {
  DB_HEADER_SIZE as u64 + page_id as u64 * page_size as u64
}

// StorageManager options.
#[derive(Clone, Debug)]
pub struct Options {
  page_size: u32,
  is_disk: bool,
  disk_path: String,
  mem_capacity: usize,
}

impl Options {
  // Creates Options struct with default values.
  pub fn new() -> Self {
    Self {
      page_size: DEFAULT_PAGE_SIZE,
      is_disk: false,
      disk_path: String::new(),
      mem_capacity: 0,
    }
  }
}

pub struct StorageManagerBuilder {
  opts: Options,
}

impl StorageManagerBuilder {
  // Creates a new instance of StorageManagerBuilder.
  pub fn new() -> Self {
    Self { opts: Options::new() }
  }

  // Creates options for disk-based storage manager.
  pub fn as_disk(mut self, path: &str) -> Self {
    self.opts.is_disk = true;
    self.opts.disk_path = path.to_owned();
    self
  }

  // Creates options for memory-based storage manager.
  pub fn as_mem(mut self, capacity: usize) -> Self {
    self.opts.is_disk = false;
    self.opts.mem_capacity = capacity;
    self
  }

  // Sets the provided page size.
  pub fn with_page_size(mut self, page_size: u32) -> Self {
    self.opts.page_size = page_size;
    self
  }

  // Returns storage manager as a result.
  pub fn try_build(self) -> Res<StorageManager> {
    StorageManager::try_new(&self.opts)
  }

  // Returns storage manager by unwrapping the result.
  pub fn build(self) -> StorageManager {
    self.try_build().unwrap()
  }
}

pub struct StorageManager {
  desc: Descriptor,
  flags: u32, //
  page_size: u32, // page size on disk
  free_page_id: u32, // pointer to the free list as the first meta block
  root_page: Option<u32>, // root page for the first btree
  free_list: Vec<u32>, // in-memory free list, contains pages available for reuse
  free_set: HashSet<u32>, // in-memory set of all of the free pages, cleared on sync
}

impl StorageManager {
  // Builder for StorageManager.
  pub fn builder() -> StorageManagerBuilder {
    StorageManagerBuilder::new()
  }

  // Creates a new StorageManager with the provided options.
  // The method opens or creates a corresponding database.
  //
  // Consider using `builder()` method instead.
  fn try_new(opts: &Options) -> Res<Self> {
    if opts.page_size < MIN_PAGE_SIZE || opts.page_size > MAX_PAGE_SIZE {
      return Err(err!("Corrupt database file, invalid page size {}", opts.page_size));
    }

    if opts.is_disk {
      if opts.disk_path.len() == 0 {
        return Err(err!("Empty file path"));
      }

      let path = Path::new(&opts.disk_path);

      if path.exists() {
        if !path.is_file() {
          return Err(err!("Not a file: {}", path.display()));
        }
        if res!(path.metadata()).len() < DB_HEADER_SIZE as u64 {
          return Err(err!("Corrupt database file, header is too small"));
        }

        let mut buf = vec![0u8; DB_HEADER_SIZE];
        let mut desc = Descriptor::disk(opts.disk_path.as_ref());
        desc.read(0, &mut buf[..]);

        if &buf[0..4] != MAGIC {
          return Err(err!("Corrupt database file, invalid MAGIC"));
        }

        // Reserved for database flags.
        let flags = u8_u32!(&buf[4..8]);

        let page_size = u8_u32!(&buf[8..12]);
        if page_size < MIN_PAGE_SIZE || page_size > MAX_PAGE_SIZE {
          return Err(err!("Corrupt database file, invalid page size {}", page_size));
        }

        let mut free_page_id = u8_u32!(&buf[12..16]);
        let mut free_list = Vec::new();
        let mut free_set = HashSet::new();

        let mut meta_buf = vec![0u8; page_size as usize];
        while free_page_id != INVALID_PAGE_ID {
          desc.read(pos(free_page_id, page_size), &mut meta_buf[..]);
          // Add meta page to the free list, it can be reused.
          free_list.push(free_page_id);
          free_set.insert(free_page_id);
          if &meta_buf[0..4] != META_PAGE_MAGIC {
            println!("WARN: free page magic mismatch, aborting load");
            break;
          }
          // Update free page id to the next meta block.
          free_page_id = u8_u32!(&meta_buf[4..8]);
          // Load all of the pages in the current meta block.
          let mut cnt = u8_u32!(&meta_buf[8..12]);
          let mut off = META_OFFSET;
          while cnt > 0 {
            let page_id = u8_u32!(&meta_buf[off..]);
            free_list.push(page_id);
            free_set.insert(page_id);
            off += 4;
            cnt -= 1;
          }
        }

        free_list.sort();
        free_list.reverse();

        let root_page = match u8_u32!(&buf[16..20]) {
          INVALID_PAGE_ID => None,
          page_id => Some(page_id)
        };

        Ok(Self {
          desc,
          flags,
          page_size,
          free_page_id: INVALID_PAGE_ID, // free page id is updated in sync/drop
          root_page,
          free_list,
          free_set,
        })
      } else {
        let mut mngr = Self {
          desc: Descriptor::disk(opts.disk_path.as_ref()),
          flags: 0,
          page_size: opts.page_size,
          free_page_id: INVALID_PAGE_ID,
          root_page: None,
          free_list: Vec::new(),
          free_set: HashSet::new(),
        };
        mngr.sync(); // stores header on disk and advances descriptor
        Ok(mngr)
      }
    } else {
      let mut mngr = Self {
        desc: Descriptor::mem(opts.mem_capacity),
        flags: 0,
        page_size: opts.page_size,
        free_page_id: INVALID_PAGE_ID,
        root_page: None,
        free_list: Vec::new(),
        free_set: HashSet::new(),
      };
      mngr.sync(); // stores header and advances descriptor
      Ok(mngr)
    }
  }

  // Returns root page id that is currently set.
  // The value is the one that is in memory (most recent) in case disk and memory have diverged.
  pub fn root_page(&self) -> Option<u32> {
    self.root_page
  }

  // Updates root page id in memory.
  // Does not sync data.
  pub fn update_root_page(&mut self, root_opt: Option<u32>) {
    self.root_page = root_opt;
  }

  // Reads the content of the page with `page_id` into the buffer.
  // No sync is required for this method.
  pub fn read(&mut self, page_id: u32, buf: &mut [u8]) {
    assert!(page_id != INVALID_PAGE_ID, "Invalid page id");
    assert!(!self.free_set.contains(&page_id), "Attempt to read free page {}", page_id);
    self.desc.read(pos(page_id, self.page_size), &mut buf[..self.page_size as usize])
  }

  // Writes data in the page with `page_id`.
  // No sync is required for this method.
  pub fn write(&mut self, page_id: u32, buf: &[u8]) {
    assert!(page_id != INVALID_PAGE_ID, "Invalid page id");
    assert!(!self.free_set.contains(&page_id), "Attempt to write to free page {}", page_id);
    self.desc.write(pos(page_id, self.page_size), &buf[..self.page_size as usize])
  }

  // Writes data to the next available page and returns its page id.
  pub fn write_next(&mut self, buf: &[u8]) -> u32 {
    let next_page_id = match self.free_list.pop() {
      Some(page_id) => {
        self.free_set.remove(&page_id);
        page_id
      },
      None => self.num_pages() as u32,
    };
    self.write(next_page_id, buf);
    next_page_id
  }

  // Marks the page as free so it is not available for future reads and writes; however,
  // it is also not available yet for reuse. The page is finally freed and recycled after sync.
  pub fn mark_as_free(&mut self, page_id: u32) {
    assert!(page_id != INVALID_PAGE_ID, "Invalid page id");
    assert!(self.num_pages() > page_id as usize, "Invalid page {} to free", page_id);
    self.free_set.insert(page_id);
  }

  // Marks the page as available if it was freed, the exact opposite of `mark_as_free()`.
  // This is used to roll back changes and restore freed pages.
  pub fn restore_from_free(&mut self, page_id: u32) {
    assert!(page_id != INVALID_PAGE_ID, "Invalid page id");
    assert!(self.num_pages() > page_id as usize, "Invalid page {} to restore", page_id);
    self.free_set.remove(&page_id);
  }

  // Returns true if the page is accessible, e.g. not freed or outside the bounds.
  #[inline]
  pub fn is_accessible(&self, page_id: u32) -> bool {
    page_id != INVALID_PAGE_ID &&
      (page_id as usize) < self.num_pages() &&
        !self.free_set.contains(&page_id)
  }

  // Sync metadata + free pages.
  pub fn sync(&mut self) {
    // We cannot use pages that were marked as free (free_set) since we may need to roll back in
    // case of a file write failure or other panic.

    // Meta blocks are already included in the free list so we just reset the free page id here.
    self.free_page_id = INVALID_PAGE_ID;

    // We need to make sure we don't add any duplicate pages, check below.
    for pid in &self.free_list {
      if self.free_set.contains(pid) {
        self.free_set.remove(pid);
      }
    }

    // Move all of the marked as free pages into the free list.
    // It is fine to keep out of order, the list will be sorted.
    for &free_page in self.free_set.iter() {
      self.free_list.push(free_page);
    }
    self.free_set.clear();

    // Sort the list, we need the ascending order so pop/push are in descending order.
    self.free_list.sort();

    // Figure out if we can truncate the file.
    let mut can_truncate = false;
    let mut trunc_page = self.num_pages() as u32;
    while let Some(pid) = self.free_list.pop() {
      if pid + 1 == trunc_page {
        can_truncate = true;
        trunc_page = pid;
      } else {
        self.free_list.push(pid);
        break;
      }
    }

    // If there are more free pages left, write them to meta pages.
    if self.free_list.len() > 0 {
      // Calculate the number of pages (meta blocks) we need to store all of the free pages.
      let mut meta_block_cnt = {
        let min_pages = (4 /* u32 size */ * self.free_list.len()) as f64 /
          (4 /* u32 size */ + self.page_size as usize - META_OFFSET) as f64;
        min_pages.ceil() as usize
      };

      // The number of meta blocks is always less than or equal to the length of the free list.
      assert!(
        meta_block_cnt <= self.free_list.len(),
        "Invalid number of meta blocks, meta block count: {}, free pages: {}",
        meta_block_cnt, self.free_list.len()
      );

      let mut len = self.free_list.len();
      let mut off = META_OFFSET; // the first 12 bytes are reserved for metadata: magic, page id, and count
      let mut cnt: u32 = 0; // number of pages per meta block
      let mut buf = vec![0u8; self.page_size as usize];

      let mut prev = INVALID_PAGE_ID;
      let mut curr = INVALID_PAGE_ID;

      while len > 0 {
        len -= 1;
        let pid = self.free_list[len];

        if curr == INVALID_PAGE_ID {
          curr = pid;
        } else {
          res!((&mut buf[off..]).write(&u32_u8!(pid)));
          cnt += 1;
          off += 4;
        }

        if off > buf.len() - 4 /* u32 size */ || len == 0 {
          res!((&mut buf[0..4]).write(META_PAGE_MAGIC));
          res!((&mut buf[4..8]).write(&u32_u8!(prev)));
          res!((&mut buf[8..12]).write(&u32_u8!(cnt)));
          self.write(curr, &buf[..]);
          meta_block_cnt -= 1;

          prev = curr;
          curr = INVALID_PAGE_ID;
          off = META_OFFSET;
          cnt = 0;
        }
      }

      // Write the remaining data into one more page.
      if meta_block_cnt > 0 {
        res!((&mut buf[0..4]).write(&u32_u8!(prev)));
        res!((&mut buf[4..8]).write(&u32_u8!(cnt)));
        self.write(curr, &buf[..]);
        self.free_page_id = curr;
        meta_block_cnt -= 1;
      } else {
        self.free_page_id = prev;
      }

      // All meta blocks must have been used at this point.
      assert!(meta_block_cnt == 0, "Meta blocks inconsistency, {} blocks left", meta_block_cnt);
    }

    // We never clear free_list as it will be used later.
    // Move all of the pages into free_set
    for &pid in &self.free_list {
      self.free_set.insert(pid);
    }
    self.free_list.reverse();

    // Persist the database header.
    let mut buf = [0u8; DB_HEADER_SIZE];
    res!((&mut buf[0..]).write(MAGIC));
    res!((&mut buf[4..]).write(&u32_u8!(self.flags)));
    res!((&mut buf[8..]).write(&u32_u8!(self.page_size)));
    res!((&mut buf[12..]).write(&u32_u8!(self.free_page_id)));
    res!((&mut buf[16..]).write(&u32_u8!(self.root_page.unwrap_or(INVALID_PAGE_ID))));
    self.desc.write(0, &buf[..]);

    // Optionally truncate the file.
    if can_truncate {
      self.desc.truncate(pos(trunc_page, self.page_size));
    }
  }

  // ==================
  // Storage statistics
  // ==================

  // Returns the configured page size for the storage manager.
  // This will never exceed 4 bytes (u32::MAX)
  #[inline]
  pub fn page_size(&self) -> usize {
    self.page_size as usize
  }

  // Total number of pages that are managed by the storage manager.
  #[inline]
  pub fn num_pages(&self) -> usize {
    if self.desc.len() == 0 {
      return 0;
    }
    ((self.desc.len() - DB_HEADER_SIZE as u64) / self.page_size as u64) as usize
  }

  // Number of free pages that were reclaimed and are available for use.
  // This does not include pages that were marked as free but have not been released yet.
  #[inline]
  pub fn num_free_pages(&self) -> usize {
    self.free_list.len() as usize
  }

  // The amount of memory (in bytes) used by the storage manager.
  #[inline]
  pub fn estimated_mem_usage(&self) -> usize {
    let desc_mem_usage = self.desc.estimated_mem_usage();
    let free_mem_usage = self.free_set.len() * 4 /* u32 size */ + self.free_list.len() * 4;
    desc_mem_usage + free_mem_usage
  }
}

#[cfg(test)]
pub mod tests {
  use super::*;
  use std::env::temp_dir;
  use std::fs::remove_file;
  use std::path::Path;
  use rand::prelude::*;

  struct TempFile {
    path: String,
  }

  impl TempFile {
    fn new() -> Self {
      let file_name = format!("test_storage_tmp_file_{}", rand::random::<u64>());
      let mut tmp_dir = temp_dir();
      tmp_dir.push(file_name);
      let path = tmp_dir.as_path();
      assert!(!path.exists(), "Random path {:?} exists", path);
      Self { path: path.to_str().unwrap().to_owned() }
    }

    fn path(&self) -> &str {
      self.path.as_ref()
    }
  }

  impl Drop for TempFile {
    fn drop(&mut self) {
      let path = Path::new(&self.path);
      if path.exists() {
        remove_file(path).unwrap();
      }
    }
  }

  // Creates a temporary file for tests.
  // Public so other modules can reuse this function.
  pub fn with_tmp_file<F>(func: F) where F: Fn(&str) -> () {
    let tmp = TempFile::new();
    println!("path: {}", tmp.path());
    func(tmp.path());
  }

  fn with_disk_descriptor<F>(func: F) where F: Fn(&mut Descriptor) -> () {
    println!("Started testing FileDescriptor");
    with_tmp_file(|path| {
      let mut desc = Descriptor::disk(path);
      func(&mut desc);
    });
    println!("Finished testing FileDescriptor");
  }

  fn with_mem_descriptor<F>(func: F) where F: Fn(&mut Descriptor) -> () {
    println!("Started testing MemDescriptor");
    let mut desc = Descriptor::mem(0);
    func(&mut desc);
    println!("Finished testing MemDescriptor");
  }

  fn with_all_descriptors<F>(func: F) where F: Fn(&mut Descriptor) -> () {
    with_disk_descriptor(|desc| func(desc));
    with_mem_descriptor(|desc| func(desc));
  }

  fn storage_mem(page_size: u32) -> StorageManager {
    StorageManager::builder().as_mem(0).with_page_size(page_size).build()
  }

  fn storage_disk(page_size: u32, path: &str) -> StorageManager {
    StorageManager::builder().as_disk(path).with_page_size(page_size).build()
  }

  //==============
  // Options tests
  //==============

  #[test]
  fn test_storage_options_default() {
    let opts = Options::new();
    assert!(!opts.is_disk);
    assert_eq!(opts.page_size, DEFAULT_PAGE_SIZE);
  }

  //============================
  // StorageManagerBuilder tests
  //============================

  #[test]
  fn test_storage_storage_builder_mem() {
    let builder = StorageManagerBuilder::new().as_mem(128);
    let opts = builder.opts;
    assert!(!opts.is_disk);
    assert_eq!(opts.mem_capacity, 128);
    assert_eq!(opts.page_size, DEFAULT_PAGE_SIZE);
  }

  #[test]
  fn test_storage_options_disk() {
    with_tmp_file(|path| {
      let builder = StorageManagerBuilder::new().as_disk(path).with_page_size(32);
      let opts = builder.opts;
      assert!(opts.is_disk);
      assert_eq!(opts.disk_path, path.to_owned());
      assert_eq!(opts.page_size, 32);
    });
  }

  #[test]
  fn test_storage_options_chaining() {
    with_tmp_file(|path| {
      let builder = StorageManagerBuilder::new()
        .as_disk(path).with_page_size(32)
        .as_mem(128).with_page_size(64);
      let opts = builder.opts;
      assert!(!opts.is_disk);
      assert_eq!(opts.mem_capacity, 128);
      assert_eq!(opts.page_size, 64);
    });
  }

  #[test]
  #[should_panic(expected = "Empty file path")]
  fn test_storage_options_invalid_empty_path() {
    StorageManagerBuilder::new().as_disk(&"").build();
  }

  #[test]
  #[should_panic(expected = "invalid page size")]
  fn test_storage_options_invalid_too_small_page() {
    StorageManagerBuilder::new().as_mem(0).with_page_size(MIN_PAGE_SIZE - 1).build();
  }

  #[test]
  #[should_panic(expected = "invalid page size")]
  fn test_storage_options_invalid_too_large_page() {
    StorageManagerBuilder::new().as_mem(0).with_page_size(MAX_PAGE_SIZE + 1).build();
  }

  //=================
  // Descriptor tests
  //=================

  #[test]
  #[should_panic(expected = "Write past EOF")]
  fn test_storage_descriptor_disk_write_fail_eof() {
    with_disk_descriptor(|desc| desc.write(10, &[1, 2, 3]));
  }

  #[test]
  #[should_panic(expected = "Write past EOF")]
  fn test_storage_descriptor_mem_write_fail_eof() {
    with_mem_descriptor(|desc| desc.write(10, &[1, 2, 3]));
  }

  #[test]
  fn test_storage_descriptor_write_ok() {
    with_all_descriptors(|desc| {
      desc.write(0, &[1, 2, 3]);
      desc.write(3, &[4, 5, 6]);
    });
  }

  #[test]
  #[should_panic(expected = "Read past EOF")]
  fn test_storage_descriptor_disk_read_fail_eof() {
    with_disk_descriptor(|desc| {
      let mut res = vec![0; 5];
      desc.read(10, &mut res[0..4])
    });
  }

  #[test]
  #[should_panic(expected = "Read past EOF")]
  fn test_storage_descriptor_mem_read_fail_eof() {
    with_mem_descriptor(|desc| {
      let mut res = vec![0; 5];
      desc.read(10, &mut res[0..4])
    });
  }

  #[test]
  #[should_panic(expected = "Read past EOF: pos 0 len 5")]
  fn test_storage_descriptor_disk_read_fail_too_long() {
    with_disk_descriptor(|desc| {
      let mut res = vec![0; 5];
      desc.read(0, &mut res[0..5])
    });
  }

  #[test]
  #[should_panic(expected = "Read past EOF: pos 0 len 5")]
  fn test_storage_descriptor_mem_read_fail_too_long() {
    with_mem_descriptor(|desc| {
      let mut res = vec![0; 5];
      desc.read(0, &mut res[0..5])
    });
  }

  #[test]
  fn test_storage_descriptor_tmp_write() {
    with_all_descriptors(|desc| {
      desc.write(0, "Hello, world!".as_bytes());
    });
  }

  #[test]
  fn test_storage_descriptor_read_ok() {
    with_all_descriptors(|desc| {
      desc.write(0, &[1, 2, 3, 4, 5, 6, 7, 8]);

      let mut res = vec![0; 5];
      desc.read(0, &mut res[0..4]);
      assert_eq!(res, vec![1, 2, 3, 4, 0]);
    });
  }

  #[test]
  #[should_panic(expected = "Failed to truncate to len 100, curr_len 3")]
  fn test_storage_descriptor_disk_truncate() {
    with_disk_descriptor(|desc| {
      desc.write(0, &[1, 2, 3]);
      // Truncate with larger length.
      desc.truncate(100);
    });
  }

  #[test]
  #[should_panic(expected = "Failed to truncate to len 100, curr_len 3")]
  fn test_storage_descriptor_mem_truncate() {
    with_mem_descriptor(|desc| {
      desc.write(0, &[1, 2, 3]);
      // Truncate with larger length.
      desc.truncate(100);
    });
  }

  #[test]
  fn test_storage_descriptor_truncate() {
    with_all_descriptors(|desc| {
      desc.write(0, &[1, 2, 3, 4, 5, 6, 7, 8]);

      // Truncate with smaller length.
      desc.truncate(5);
      let mut res = vec![0; 10];
      desc.read(0, &mut res[0..5]);
      assert_eq!(&res[0..5], &[1, 2, 3, 4, 5]);

      // Truncate with the same length.
      desc.truncate(5);
      assert_eq!(desc.len(), 5);
    });
  }

  #[test]
  fn test_storage_descriptor_len() {
    with_all_descriptors(|desc| {
      desc.write(0, &[1, 2, 3, 4, 5, 6, 7, 8]);

      assert_eq!(desc.len(), 8);
      for len in (0..desc.len()).rev() {
        desc.truncate(len);
        assert_eq!(desc.len(), len);
      }
    });
  }

  #[test]
  fn test_storage_descriptor_estimated_mem_usage() {
    with_mem_descriptor(|desc| {
      desc.write(0, &[1, 2, 3, 4, 5, 6, 7, 8]);
      assert_eq!(desc.estimated_mem_usage(), 8);
      desc.truncate(2);
      assert_eq!(desc.estimated_mem_usage(), 2);
    });

    // FileDescriptor has 0 memory usage.
    with_disk_descriptor(|desc| {
      desc.write(0, &[1, 2, 3, 4, 5, 6, 7, 8]);
      assert_eq!(desc.estimated_mem_usage(), 0);
      desc.truncate(2);
      assert_eq!(desc.estimated_mem_usage(), 0);
    });
  }

  //=====================
  // StorageManager tests
  //=====================

  #[test]
  fn test_storage_manager_init_mem() {
    let mngr = storage_mem(24);
    assert_eq!(mngr.flags, 0);
    assert_eq!(mngr.page_size, 24);
    assert_eq!(mngr.free_page_id, INVALID_PAGE_ID);
    assert_eq!(mngr.root_page, None);
    assert_eq!(mngr.free_list.len(), 0);
    assert_eq!(mngr.free_set.len(), 0);
    assert_eq!(mngr.num_pages(), 0);
    assert_eq!(mngr.estimated_mem_usage(), DB_HEADER_SIZE);
  }

  #[test]
  fn test_storage_manager_init_disk() {
    with_tmp_file(|path| {
      let mngr = storage_disk(24, path);
      assert_eq!(mngr.flags, 0);
      assert_eq!(mngr.page_size, 24);
      assert_eq!(mngr.free_page_id, INVALID_PAGE_ID);
      assert_eq!(mngr.root_page, None);
      assert_eq!(mngr.free_list.len(), 0);
      assert_eq!(mngr.free_set.len(), 0);
      assert_eq!(mngr.num_pages(), 0);
      assert_eq!(mngr.estimated_mem_usage(), 0);
      assert_eq!(Path::new(path).metadata().unwrap().len(), DB_HEADER_SIZE as u64);
    })
  }

  #[test]
  fn test_storage_manager_init_disk_2() {
    with_tmp_file(|path| {
      let _mngr = storage_disk(24, path);
      let mngr = storage_disk(32, path);

      assert_eq!(mngr.flags, 0);
      assert_eq!(mngr.page_size, 24);
      assert_eq!(mngr.free_page_id, INVALID_PAGE_ID);
      assert_eq!(mngr.root_page, None);
      assert_eq!(mngr.free_list.len(), 0);
      assert_eq!(mngr.free_set.len(), 0);
      assert_eq!(mngr.num_pages(), 0);
      assert_eq!(mngr.estimated_mem_usage(), 0);
    })
  }

  #[test]
  fn test_storage_manager_root_page_persist() {
    with_tmp_file(|path| {
      {
        let mut mngr = storage_disk(32, path);
        assert_eq!(mngr.root_page(), None);

        mngr.update_root_page(Some(100));
        assert_eq!(mngr.root_page(), Some(100));
        mngr.sync();
      }
      {
        let mngr = storage_disk(32, path);
        assert_eq!(mngr.root_page(), Some(100));
      }
    })
  }

  #[test]
  fn test_storage_manager_write_read() {
    let mut mngr = storage_mem(32);
    let mut buf = vec![5u8; mngr.page_size as usize];
    (&mut buf[..]).write(&[1, 2, 3, 4]).unwrap();

    let page_id = mngr.write_next(&buf[..]);
    assert_eq!(page_id, 0);

    (&mut buf[4..]).write(&[8, 9, 0]).unwrap();
    mngr.write(page_id, &buf[..]);

    mngr.read(page_id, &mut buf[..]);
    assert_eq!(&buf[..8], &[1, 2, 3, 4, 8, 9, 0, 5]);
  }

  #[test]
  fn test_storage_manager_write_free() {
    let mut mngr = storage_mem(32);
    let buf = vec![5u8; mngr.page_size as usize];

    for i in 0..10 {
      assert_eq!(mngr.write_next(&buf[..]), i);
    }

    mngr.sync();

    // We don't persist free_count after sync.
    assert_eq!(mngr.free_page_id, INVALID_PAGE_ID);

    mngr.mark_as_free(2);
    mngr.mark_as_free(0);
    mngr.mark_as_free(1);

    assert_eq!(mngr.num_free_pages(), 0);

    mngr.sync();

    // We persist free pages after sync.
    assert_eq!(mngr.free_page_id, 2);
    assert_eq!(mngr.free_list, vec![2, 1, 0]);
    assert_eq!(mngr.free_set, [2, 1, 0].iter().cloned().collect());
    assert_eq!(mngr.num_free_pages(), 3);

    // We need to pop the first page from the list.
    assert_eq!(mngr.write_next(&buf[..]), 0);
    assert_eq!(mngr.free_list, vec![2, 1]);
    assert_eq!(mngr.free_set, [2, 1].iter().cloned().collect());
    assert_eq!(mngr.num_free_pages(), 2);

    // We truncate the descriptor instead of keeping the pages.
    for i in 1..10 {
      mngr.mark_as_free(i);
    }

    assert_eq!(mngr.free_list, vec![2, 1]);
    assert_eq!(mngr.free_set, [9, 8, 7, 6, 5, 4, 3, 2, 1].iter().cloned().collect());
    assert_eq!(mngr.num_free_pages(), 2);

    mngr.sync();

    assert_eq!(mngr.free_list.len(), 0);
    assert_eq!(mngr.free_set.len(), 0);
    assert_eq!(mngr.num_pages(), 1);
  }

  #[test]
  #[should_panic(expected = "Invalid page 100 to free")]
  fn test_storage_manager_free_out_of_bound() {
    let mut mngr = storage_mem(32);
    mngr.mark_as_free(100);
  }

  #[test]
  #[should_panic(expected = "Attempt to write to free page")]
  fn test_storage_manager_write_into_free_page() {
    let mut mngr = storage_mem(32);
    let buf = vec![5u8; mngr.page_size as usize];
    let page_id = mngr.write_next(&buf[..]);
    mngr.mark_as_free(page_id);
    mngr.write(page_id, &buf[..]);
  }

  #[test]
  #[should_panic(expected = "Attempt to write to free page")]
  fn test_storage_manager_write_into_free_page_after_sync() {
    let mut mngr = storage_mem(32);
    let buf = vec![5u8; mngr.page_size as usize];
    for _ in 0..5 {
      mngr.write_next(&buf[..]);
    }
    mngr.mark_as_free(0);
    mngr.sync();
    mngr.write(0, &buf[..]);
  }

  #[test]
  #[should_panic(expected = "Attempt to read free page")]
  fn test_storage_manager_read_free_page() {
    let mut mngr = storage_mem(32);
    let mut buf = vec![5u8; mngr.page_size as usize];
    let page_id = mngr.write_next(&buf[..]);
    mngr.mark_as_free(page_id);
    mngr.read(page_id, &mut buf[..]);
  }

  #[test]
  #[should_panic(expected = "Attempt to read free page")]
  fn test_storage_manager_read_free_page_after_sync() {
    let mut mngr = storage_mem(32);
    let mut buf = vec![5u8; mngr.page_size as usize];
    for _ in 0..5 {
      mngr.write_next(&buf[..]);
    }
    mngr.mark_as_free(0);
    mngr.sync();
    mngr.read(0, &mut buf[..]);
  }

  #[test]
  fn test_storage_manager_free_double_free() {
    let mut mngr = storage_mem(32);
    let buf = vec![1u8; mngr.page_size as usize];

    for i in 0..4 {
      assert_eq!(mngr.write_next(&buf[..]), i);
    }

    for _ in 0..10 {
      mngr.mark_as_free(1);
    }

    mngr.mark_as_free(0);
    mngr.mark_as_free(2);

    assert_eq!(mngr.free_list, vec![]);
    assert_eq!(mngr.free_set, [0, 1, 2].iter().cloned().collect());
    assert_eq!(mngr.num_free_pages(), 0);

    mngr.sync();

    mngr.mark_as_free(1);

    assert_eq!(mngr.free_list, vec![2, 1, 0]);
    assert_eq!(mngr.free_set, [0, 1, 2].iter().cloned().collect());
    assert_eq!(mngr.num_free_pages(), 3);
  }

  #[test]
  fn test_storage_manager_free_truncate_evict() {
    let mut mngr = storage_mem(32);
    let buf = vec![1u8; mngr.page_size as usize];

    // Write 10 pages in total.
    for _ in 0..10 {
      mngr.write_next(&buf[..]);
    }

    mngr.mark_as_free(8);
    mngr.mark_as_free(7);
    mngr.mark_as_free(6);
    mngr.mark_as_free(4);

    mngr.sync();

    assert_eq!(mngr.num_pages(), 10);
    assert_eq!(mngr.num_free_pages(), 4);
    assert_eq!(mngr.free_list, vec![8, 7, 6, 4]);
    assert_eq!(mngr.free_set, [8, 7, 6, 4].iter().cloned().collect());

    mngr.mark_as_free(9);

    mngr.sync();

    assert_eq!(mngr.num_pages(), 6);
    assert_eq!(mngr.num_free_pages(), 1);
    assert_eq!(mngr.free_list, vec![4]);
    assert_eq!(mngr.free_set, [4].iter().cloned().collect());

    mngr.mark_as_free(3);
    mngr.mark_as_free(2);
    mngr.mark_as_free(1);
    mngr.mark_as_free(0);

    mngr.sync();

    assert_eq!(mngr.num_pages(), 6);
    assert_eq!(mngr.num_free_pages(), 5);
    assert_eq!(mngr.free_list, vec![4, 3, 2, 1, 0]);
    assert_eq!(mngr.free_set, [4, 3, 2, 1, 0].iter().cloned().collect());

    mngr.mark_as_free(5);

    mngr.sync();

    assert_eq!(mngr.num_pages(), 0);
    assert_eq!(mngr.num_free_pages(), 0);
    assert_eq!(mngr.free_list.len(), 0);
    assert_eq!(mngr.free_set.len(), 0);
  }

  #[test]
  fn test_storage_manager_free_drop() {
    with_tmp_file(|path| {
      {
        let mut mngr = storage_disk(32, path);
        let buf = vec![1u8; mngr.page_size as usize];
        for _ in 0..3 {
          mngr.write_next(&buf[..]);
        }

        mngr.mark_as_free(0);

        mngr.sync();
      }
      {
        let mut mngr = storage_disk(32, path);

        assert_eq!(mngr.num_free_pages(), 1);
        assert_eq!(mngr.free_list, vec![0]);
        assert_eq!(mngr.free_set, [0].iter().cloned().collect());

        mngr.mark_as_free(2);
        mngr.mark_as_free(1);

        mngr.sync();
      }
      {
        let mngr = storage_disk(32, path);

        assert_eq!(mngr.num_free_pages(), 0);
        assert_eq!(mngr.free_list.len(), 0);
        assert_eq!(mngr.free_set.len(), 0);
      }
    });
  }

  #[test]
  fn test_storage_manager_free_manager_restart() {
    with_tmp_file(|path| {
      {
        let mut mngr = storage_disk(32, path);
        let buf = vec![1u8; mngr.page_size as usize];

        for i in 0..9 {
          assert_eq!(mngr.write_next(&buf[..]), i);
        }

        for i in 0..8 {
          mngr.mark_as_free(i);
        }

        mngr.sync();

        assert_eq!(mngr.num_pages(), 9);
        assert_eq!(mngr.free_list, vec![7, 6, 5, 4, 3, 2, 1, 0]);
        assert_eq!(mngr.free_set, [0, 1, 2, 3, 4, 5, 6, 7].iter().cloned().collect());
      }
      // Drop implementation should store free list on disk.
      {
        let mut mngr = storage_disk(32, path);
        assert_eq!(mngr.num_pages(), 9);
        assert_eq!(mngr.free_page_id, INVALID_PAGE_ID);
        // We first add meta blocks (0, 1) and then pages in decreasing order.
        assert_eq!(mngr.free_list, vec![7, 6, 5, 4, 3, 2, 1, 0]);
        assert_eq!(mngr.free_set, [0, 1, 2, 3, 4, 5, 6, 7].iter().cloned().collect());

        mngr.mark_as_free(8);

        mngr.sync();
      }
      // The file should be truncated.
      {
        let mngr = storage_disk(32, path);
        assert_eq!(mngr.num_pages(), 0);
        assert_eq!(mngr.free_page_id, INVALID_PAGE_ID);
        assert_eq!(mngr.free_list.len(), 0);
        assert_eq!(mngr.free_set.len(), 0);
      }
    })
  }

  #[test]
  fn test_storage_manager_free_corrupt_meta_block() {
    with_tmp_file(|path| {
      {
        let mut mngr = storage_disk(32, path);
        let buf = vec![255u8; mngr.page_size as usize];

        for i in 0..10 {
          assert_eq!(mngr.write_next(&buf[..]), i);
        }

        for i in 0..9 {
          mngr.mark_as_free(i);
        }

        mngr.sync();

        // Modify meta block so we cannot read the pages.
        // There are 2 meta blocks, meta block 1 has pid 8.
        mngr.desc.write(pos(8, 32), &buf);
      }

      {
        let mngr = storage_disk(32, path);
        // Because the meta block is corrupted, free list will only contain part of the pids.
        assert_eq!(mngr.free_list, vec![8, 2, 1, 0]);
      }
    })
  }

  #[test]
  fn test_storage_manager_is_accessible() {
    let mut mngr = storage_mem(32);
    let buf = vec![1u8; mngr.page_size as usize];

    // Write 10 pages in total.
    for _ in 0..10 {
      mngr.write_next(&buf[..]);
    }

    // Allocated pages are accessible.
    for page_id in 0..10 {
      assert!(mngr.is_accessible(page_id));
    }

    // Pages outside the bounds are not accessible.
    for page_id in 10..20 {
      assert!(!mngr.is_accessible(page_id));
    }

    // Freed pages are not accessible.
    for page_id in 0..10 {
      mngr.mark_as_free(page_id);
      assert!(!mngr.is_accessible(page_id));
    }

    // Invalid page is not accessible.
    assert!(!mngr.is_accessible(INVALID_PAGE_ID));
  }

  #[test]
  fn test_storage_manager_restore_from_free() {
    let mut mngr = storage_mem(32);
    let mut buf = vec![2u8; mngr.page_size as usize];

    // Write 10 pages in total.
    for _ in 0..10 {
      mngr.write_next(&buf[..]);
    }

    // Free the pages.
    for page_id in 0..10 {
      mngr.mark_as_free(page_id);
    }

    // Restore the pages.
    for page_id in 0..10 {
      mngr.restore_from_free(page_id);
    }

    // All pages should be accessible.
    for page_id in 0..10 {
      assert!(mngr.is_accessible(page_id));
      mngr.write(page_id, &buf);
      mngr.read(page_id, &mut buf);
    }
  }

  #[test]
  #[should_panic(expected = "Invalid page id")]
  fn test_storage_manager_restore_from_free_invalid() {
    let mut mngr = storage_mem(32);
    mngr.restore_from_free(INVALID_PAGE_ID);
  }

  #[test]
  #[should_panic(expected = "Invalid page 100 to restore")]
  fn test_storage_manager_restore_from_free_out_of_bound() {
    let mut mngr = storage_mem(32);
    mngr.restore_from_free(100);
  }

  //============================
  // StorageManager fuzz testing
  //============================

  fn shuffle(input: &mut Vec<u32>) {
    input.shuffle(&mut thread_rng());
  }

  #[test]
  fn test_storage_manager_fuzz_free_fully() {
    let mut mngr = storage_mem(32);
    let buf = vec![1u8; mngr.page_size as usize];
    let num_pages = 500;
    let num_iterations = 100;
    let mut pages = Vec::new();

    for _ in 0..num_iterations {
      for _ in 1..num_pages + 1 {
        pages.push(mngr.write_next(&buf[..]));
      }

      shuffle(&mut pages);

      while let Some(page) = pages.pop() {
        mngr.mark_as_free(page);
      }

      mngr.sync();

      assert_eq!(mngr.num_pages(), 0);
      assert_eq!(mngr.num_free_pages(), 0);
      assert_eq!(mngr.free_list.len(), 0);
      assert_eq!(mngr.free_set.len(), 0);
    }
  }

  #[test]
  fn test_storage_manager_fuzz_free_with_writes() {
    let mut mngr = storage_mem(32);
    let buf = vec![1u8; mngr.page_size as usize];
    let num_pages = 500;
    let num_pages_to_keep = 23;
    let num_iterations = 100;
    let mut pages = Vec::new();

    for _ in 0..num_iterations {
      for _ in 1..num_pages + 1 {
        pages.push(mngr.write_next(&buf[..]));
      }

      shuffle(&mut pages);

      while pages.len() > num_pages_to_keep {
        let page = pages.pop().unwrap();
        mngr.mark_as_free(page);
      }

      mngr.sync();

      assert_eq!(mngr.free_list.len(), mngr.num_free_pages());
      assert_eq!(mngr.free_set.len(), mngr.free_list.len());
    }

    assert_eq!(mngr.num_free_pages() + pages.len(), mngr.num_pages());
    assert_eq!(mngr.free_list.len(), mngr.num_free_pages());
    assert_eq!(mngr.free_set.len(), mngr.free_list.len());

    while let Some(page) = pages.pop() {
      mngr.mark_as_free(page);
    }

    assert_eq!(mngr.num_pages(), pages.len() + mngr.free_set.len());

    mngr.sync();

    assert_eq!(mngr.num_pages(), 0);
    assert_eq!(mngr.num_free_pages(), 0);
    assert_eq!(mngr.free_list.len(), 0);
    assert_eq!(mngr.free_set.len(), 0);
  }
}
