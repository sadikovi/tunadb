use std::cmp;
use std::collections::BTreeMap;
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::Path;

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
  fn disk(path: &str) -> Self {
    let fd = OpenOptions::new().read(true).write(true).create(true).open(path);
    Descriptor::Disk { fd: res!(fd, "Failed to open {}", path) }
  }

  fn mem(capacity: usize) -> Self {
    let data = Vec::with_capacity(capacity);
    Descriptor::Mem { data }
  }

  // Reads data into the provided buffer at the position.
  fn read(&mut self, pos: u64, buf: &mut [u8]) {
    if pos + buf.len() as u64 > self.len() {
      panic!("Read past EOF: pos {} len {}", pos, buf.len());
    }

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
  fn write(&mut self, pos: u64, buf: &[u8]) {
    if pos > self.len() {
      panic!("Write past EOF: pos {} len {}", pos, buf.len());
    }

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
  fn truncate(&mut self, len: u64) {
    let curr_len = self.len();
    if len > curr_len {
      panic!("Failed to truncate to len {}, curr_len {}", len, curr_len);
    }

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

  // Total length of the file or memory buffer, used for appends.
  fn len(&self) -> u64 {
    match self {
      Descriptor::Disk { fd } => res!(fd.metadata().map(|m| m.len())),
      Descriptor::Mem { data } => data.len() as u64,
    }
  }

  // Total amount of memory (in bytes) used by the descriptor.
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

const MAGIC: &[u8] = &[b'T', b'U', b'N', b'A'];

// We have a fixed metadata size, see sync() method for more information.
const METADATA_LEN: usize = 32;
const MIN_PAGE_SIZE: u32 = 16;
const MAX_PAGE_SIZE: u32 = 1 * 1024 * 1024; // 1MB
const DEFAULT_PAGE_SIZE: u32 = 4096; // 4KB

// Whether or not the page table id is set and valid
const FLAG_PAGE_TABLE_IS_SET: u32 = 0x1;

// Calculates the absolute position of a page depending on the page size.
// This is needed so we can account for the metadata length.
#[inline]
fn pos(page_id: u32, page_size: u32) -> u64 {
  METADATA_LEN as u64 + page_id as u64 * page_size as u64
}

// StorageManager options.
pub struct Options {
  page_size: u32,
  is_disk: bool,
  disk_path: String,
  mem_capacity: usize,
}

impl Options {
  pub fn new() -> OptionsBuilder {
    OptionsBuilder {
      opts: Self {
        page_size: DEFAULT_PAGE_SIZE,
        is_disk: false,
        disk_path: String::new(),
        mem_capacity: 0,
      }
    }
  }
}

pub struct OptionsBuilder {
  opts: Options,
}

impl OptionsBuilder {
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

  // Returns new options from the builder.
  // All options are validated here.
  pub fn build(self) -> Options {
    if self.opts.is_disk && self.opts.disk_path.len() == 0 {
      panic!("Empty file path");
    }
    if self.opts.page_size < MIN_PAGE_SIZE || self.opts.page_size > MAX_PAGE_SIZE {
      panic!("Invalid page size {}", self.opts.page_size);
    }
    self.opts
  }
}

pub struct StorageManager {
  desc: Descriptor,
  flags: u32,
  page_size: u32, // page size on disk
  free_page_id: u32, // pointer to the free list, represents the absolute position of a page
  free_count: u32, // number of pages in the free list
  free_map: BTreeMap<u32, (Option<u32>, Option<u32>)>, // page id -> (prev, next), keys are sorted
  page_table_root: u32, // root page for the page table
}

impl StorageManager {
  pub fn new(opts: &Options) -> Self {
    if opts.is_disk {
      let path = Path::new(&opts.disk_path);

      if path.exists() {
        if !path.is_file() {
          panic!("Not a file: {}", path.display());
        }

        if res!(path.metadata()).len() < METADATA_LEN as u64 {
          panic!("Corrupt database file, header is too small");
        }

        let mut page_buf = vec![0u8; METADATA_LEN];
        let mut desc = Descriptor::disk(opts.disk_path.as_ref());
        desc.read(0, &mut page_buf[..]);

        let flags = u8_u32!(&page_buf[4..8]);

        if &page_buf[..4] != MAGIC {
          panic!("Corrupt database file, invalid MAGIC");
        }

        let page_size = u8_u32!(&page_buf[8..12]);
        if page_size < MIN_PAGE_SIZE || page_size > MAX_PAGE_SIZE {
          panic!("Corrupt database file, invalid page size {}", page_size);
        }

        let free_page_id = u8_u32!(&page_buf[12..16]);
        let free_count = u8_u32!(&page_buf[16..20]);
        let page_table_root = u8_u32!(&page_buf[20..24]);
        let mut free_map = BTreeMap::new();

        // Reconstruct the in-memory map
        let mut cnt = 0;
        let mut prev_opt = None;
        let mut curr = free_page_id;
        let mut page_buf = vec![0u8; page_size as usize];
        while cnt < free_count {
          let next_opt = if cnt + 1 < free_count {
            desc.read(pos(curr, page_size), &mut page_buf[..]);
            Some(u8_u32!(&page_buf[0..4]))
          } else {
            None
          };

          free_map.insert(curr, (prev_opt, next_opt));
          prev_opt = Some(curr);
          curr = next_opt.unwrap_or(u32::MAX);

          cnt += 1;
        }
        Self { desc, flags, page_size, free_page_id, free_count, free_map, page_table_root }
      } else {
        let mut mngr = Self {
          desc: Descriptor::disk(opts.disk_path.as_ref()),
          flags: 0,
          page_size: opts.page_size,
          free_page_id: 0,
          free_count: 0,
          free_map: BTreeMap::new(),
          page_table_root: 0,
        };
        mngr.sync();
        mngr
      }
    } else {
      let mut mngr = Self {
        desc: Descriptor::mem(opts.mem_capacity),
        flags: 0,
        page_size: opts.page_size,
        free_page_id: 0,
        free_count: 0,
        free_map: BTreeMap::new(),
        page_table_root: 0,
      };
      mngr.sync(); // stores metadata in page 0 and advances descriptor
      mngr
    }
  }

  // Returns the currently set page table root.
  pub fn page_table_root(&self) -> Option<u32> {
    if self.flags & FLAG_PAGE_TABLE_IS_SET != 0 {
      Some(self.page_table_root)
    } else {
      None
    }
  }

  // Updates page table root in memory.
  // Call sync() to persist data on disk.
  pub fn update_page_table(&mut self, root_opt: Option<u32>) {
    // TODO: implement this method
    match root_opt {
      Some(root) => {
        self.page_table_root = root;
        self.flags |= FLAG_PAGE_TABLE_IS_SET;
      },
      None => {
        self.page_table_root = 0;
        self.flags &= !FLAG_PAGE_TABLE_IS_SET;
      }
    }
  }

  // Reads the content of the page with `page_id` into the buffer.
  pub fn read(&mut self, page_id: u32, buf: &mut [u8]) {
    self.desc.read(pos(page_id, self.page_size), &mut buf[..self.page_size as usize])
  }

  // Writes data in the page with `page_id`.
  pub fn write(&mut self, page_id: u32, buf: &[u8]) {
    self.desc.write(pos(page_id, self.page_size), &buf[..self.page_size as usize])
  }

  // Writes data to the next available page and returns its page id.
  pub fn write_next(&mut self, buf: &[u8]) -> u32 {
    let page_id = if self.free_count > 0 {
      let (&next_page_id, _) = res!(self.free_map.first_key_value());
      self.remove_free_page(next_page_id);
      self.sync();
      next_page_id
    } else {
      self.num_pages() as u32
    };
    self.write(page_id, buf);
    page_id
  }

  // Removes the provided page id from free list and free map.
  // Does not perform sync.
  fn remove_free_page(&mut self, page_id: u32) {
    if let Some(value) = self.free_map.remove(&page_id) {
      self.free_count -= 1;

      match value {
        (Some(prev), Some(next)) => {
          // TODO: optimise this
          let mut page_buf = vec![0u8; self.page_size as usize];
          res!((&mut page_buf[0..]).write(&u32_u8!(next)));
          self.write(prev, &page_buf);
          // Point prev to next
          res!(self.free_map.get_mut(&prev)).1 = Some(next);
          res!(self.free_map.get_mut(&next)).0 = Some(prev);
        },
        (Some(prev), None) => {
          // It is the tail of the free list, there is no need to override the page data.
          res!(self.free_map.get_mut(&prev)).1 = None; // next = None
        },
        (None, Some(next)) => {
          // Current head of the free list.
          self.free_page_id = next;
          res!(self.free_map.get_mut(&next)).0 = None; // prev = None
        },
        (None, None) => {
          // Free list only had one element.
          assert_eq!(self.free_count, 0);
          assert_eq!(self.free_map.len(), 0);
        },
      }
    } else {
      panic!("Free page {} is not found", page_id);
    }
  }

  // Marks page as free so it can be reused.
  pub fn free(&mut self, page_id: u32) {
    let num_pages = self.num_pages();

    if page_id as usize >= num_pages {
      panic!("Invalid page {} to free", page_id);
    }

    // If the free map already contains the page, return to avoid double free issues.
    if self.free_map.get(&page_id).is_some() {
      return;
    }

    // If the page is the last page, truncate instead of adding to the free list.
    if num_pages - 1 == page_id as usize {
      let mut last_page_id = page_id;
      while let Some((&curr, _)) = self.free_map.last_key_value() {
        if curr + 1 == last_page_id {
          last_page_id = curr;
          self.remove_free_page(curr);
        } else {
          break;
        }
      }
      self.desc.truncate(pos(last_page_id, self.page_size));
    } else {
      if self.free_count > 0 {
        // Update free map
        res!(self.free_map.get_mut(&self.free_page_id)).0 = Some(page_id);
        self.free_map.insert(page_id, (None, Some(self.free_page_id)));

        // Update the page
        // TODO: optimise this
        let mut page_buf = vec![0u8; self.page_size as usize];
        res!((&mut page_buf[0..]).write(&u32_u8!(self.free_page_id)));
        self.write(page_id, &page_buf);
      } else {
        self.free_map.insert(page_id, (None, None));
      }

      self.free_page_id = page_id;
      self.free_count += 1;
    }

    self.sync();
  }

  // Sync metadata + free pages in page 0.
  pub fn sync(&mut self) {
    let mut buf = [0u8; METADATA_LEN];
    res!((&mut buf[0..]).write(MAGIC));
    res!((&mut buf[4..]).write(&u32_u8!(self.flags)));
    res!((&mut buf[8..]).write(&u32_u8!(self.page_size)));
    res!((&mut buf[12..]).write(&u32_u8!(self.free_page_id)));
    res!((&mut buf[16..]).write(&u32_u8!(self.free_count)));
    res!((&mut buf[20..]).write(&u32_u8!(self.page_table_root)));
    self.desc.write(0, &buf[..]);
  }

  // ==================
  // Storage statistics
  // ==================

  // Returns the configured page size for the storage manager.
  pub fn page_size(&self) -> usize {
    self.page_size as usize
  }

  // Total number of pages that is managed by the storage manager.
  pub fn num_pages(&self) -> usize {
    let num_pages = (self.desc.len() - METADATA_LEN as u64) / self.page_size as u64;
    num_pages as usize
  }

  // Number of free pages that were reclaimed.
  pub fn num_free_pages(&self) -> usize {
    self.free_count as usize
  }

  // The amount of memory (in bytes) used by the storage manager.
  pub fn estimated_mem_usage(&self) -> usize {
    let desc_mem_usage = self.desc.estimated_mem_usage();
    let free_mem_usage = self.free_map.len() * (4 /* u32 key */ + 8 /* u32 prev and next */);
    desc_mem_usage + free_mem_usage
  }
}

#[cfg(test)]
mod tests {
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

  fn with_tmp_file<F>(func: F) where F: Fn(&str) -> () {
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
    let opts = Options::new().as_mem(0).with_page_size(page_size).build();
    StorageManager::new(&opts)
  }

  fn storage_disk(page_size: u32, path: &str) -> StorageManager {
    let opts = Options::new().as_disk(path).with_page_size(page_size).build();
    StorageManager::new(&opts)
  }

  #[test]
  fn test_storage_descriptor_tmp_write() {
    with_all_descriptors(|desc| {
      desc.write(0, "Hello, world!".as_bytes());
    });
  }

  #[test]
  fn test_storage_options_default() {
    let opts = Options::new().build();
    assert!(!opts.is_disk);
    assert_eq!(opts.page_size, DEFAULT_PAGE_SIZE);
  }

  #[test]
  fn test_storage_options_mem() {
    let opts = Options::new().as_mem(128).build();
    assert!(!opts.is_disk);
    assert_eq!(opts.mem_capacity, 128);
    assert_eq!(opts.page_size, DEFAULT_PAGE_SIZE);
  }

  #[test]
  fn test_storage_options_disk() {
    with_tmp_file(|path| {
      let opts = Options::new().as_disk(path).with_page_size(32).build();
      assert!(opts.is_disk);
      assert_eq!(opts.disk_path, path.to_owned());
      assert_eq!(opts.page_size, 32);
    });
  }

  #[test]
  fn test_storage_options_chaining() {
    with_tmp_file(|path| {
      let opts = Options::new()
        .as_disk(path).with_page_size(32)
        .as_mem(128).with_page_size(64)
        .build();
      assert!(!opts.is_disk);
      assert_eq!(opts.mem_capacity, 128);
      assert_eq!(opts.page_size, 64);
    });
  }

  #[test]
  #[should_panic(expected = "Empty file path")]
  fn test_storage_options_invalid_empty_path() {
    Options::new().as_disk(&"").build();
  }

  #[test]
  #[should_panic(expected = "Invalid page size")]
  fn test_storage_options_invalid_too_small_page() {
    Options::new().as_mem(0).with_page_size(MIN_PAGE_SIZE - 1).build();
  }

  #[test]
  #[should_panic(expected = "Invalid page size")]
  fn test_storage_options_invalid_too_large_page() {
    Options::new().as_mem(0).with_page_size(MAX_PAGE_SIZE + 1).build();
  }

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
      // Truncate with larger length
      desc.truncate(100);
    });
  }

  #[test]
  #[should_panic(expected = "Failed to truncate to len 100, curr_len 3")]
  fn test_storage_descriptor_mem_truncate() {
    with_mem_descriptor(|desc| {
      desc.write(0, &[1, 2, 3]);
      // Truncate with larger length
      desc.truncate(100);
    });
  }

  #[test]
  fn test_storage_descriptor_truncate() {
    with_all_descriptors(|desc| {
      desc.write(0, &[1, 2, 3, 4, 5, 6, 7, 8]);

      // Truncate with smaller length
      desc.truncate(5);
      let mut res = vec![0; 10];
      desc.read(0, &mut res[0..5]);
      assert_eq!(&res[0..5], &[1, 2, 3, 4, 5]);

      // Truncate the same length
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

    // FileDescriptor has 0 memory usage
    with_disk_descriptor(|desc| {
      desc.write(0, &[1, 2, 3, 4, 5, 6, 7, 8]);
      assert_eq!(desc.estimated_mem_usage(), 0);
      desc.truncate(2);
      assert_eq!(desc.estimated_mem_usage(), 0);
    });
  }

  #[test]
  fn test_storage_manager_init_mem() {
    let mngr = storage_mem(24);
    assert_eq!(mngr.flags, 0);
    assert_eq!(mngr.page_size, 24);
    assert_eq!(mngr.free_page_id, 0);
    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.page_table_root, 0);
    assert_eq!(mngr.num_pages(), 0);
    assert_eq!(mngr.estimated_mem_usage(), METADATA_LEN);
  }

  #[test]
  fn test_storage_manager_init_disk() {
    with_tmp_file(|path| {
      let mngr = storage_disk(24, path);
      assert_eq!(mngr.flags, 0);
      assert_eq!(mngr.page_size, 24);
      assert_eq!(mngr.free_page_id, 0);
      assert_eq!(mngr.free_count, 0);
      assert_eq!(mngr.page_table_root, 0);
      assert_eq!(mngr.num_pages(), 0);
      assert_eq!(mngr.estimated_mem_usage(), 0);
      assert_eq!(Path::new(path).metadata().unwrap().len(), METADATA_LEN as u64);
    })
  }

  #[test]
  fn test_storage_manager_init_disk_2() {
    with_tmp_file(|path| {
      let _mngr = storage_disk(24, path);
      let mngr = storage_disk(32, path);

      assert_eq!(mngr.flags, 0);
      assert_eq!(mngr.page_size, 24);
      assert_eq!(mngr.free_page_id, 0);
      assert_eq!(mngr.free_count, 0);
      assert_eq!(mngr.page_table_root, 0);
      assert_eq!(mngr.num_pages(), 0);
      assert_eq!(mngr.estimated_mem_usage(), 0);
    })
  }

  #[test]
  fn test_storage_manager_disk_meta_sync() {
    with_tmp_file(|path| {
      {
        let mut mngr = storage_disk(32, path);
        let buf = vec![5u8; mngr.page_size as usize];

        mngr.write_next(&buf[..]);
        mngr.write_next(&buf[..]);
        mngr.free(0);
        mngr.update_page_table(Some(1));

        mngr.sync();
      }
      {
        let mngr = storage_disk(32, path);
        assert_eq!(mngr.flags, FLAG_PAGE_TABLE_IS_SET);
        assert_eq!(mngr.page_size, 32);
        assert_eq!(mngr.free_page_id, 0);
        assert_eq!(mngr.free_count, 1);
        assert_eq!(mngr.page_table_root, 1);
      }
    })
  }

  #[test]
  fn test_storage_manager_page_table_persist() {
    with_tmp_file(|path| {
      {
        let mut mngr = storage_disk(32, path);
        assert_eq!(mngr.page_table_root(), None);

        mngr.update_page_table(Some(100));
        assert_eq!(mngr.page_table_root(), Some(100));
        mngr.sync();
      }
      {
        let mngr = storage_disk(32, path);
        assert_eq!(mngr.page_table_root(), Some(100));
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

    assert_eq!(mngr.write_next(&buf[..]), 0);
    assert_eq!(mngr.write_next(&buf[..]), 1);
    assert_eq!(mngr.write_next(&buf[..]), 2);

    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.free_page_id, 0); // does not really matter since the count is 0

    mngr.free(2);
    mngr.free(0);
    mngr.free(1);

    // This is because our free map would truncate the source instead of keeping the pages
    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.free_page_id, 0); // 0 because when we truncate, we don't update free ptr
    assert_eq!(mngr.free_map.len(), 0);

    assert_eq!(mngr.write_next(&buf[..]), 0);
    assert_eq!(mngr.write_next(&buf[..]), 1);
    assert_eq!(mngr.write_next(&buf[..]), 2);

    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.free_page_id, 0);
    assert_eq!(mngr.free_map.len(), 0);
  }

  #[test]
  #[should_panic(expected = "Invalid page 100 to free")]
  fn test_storage_manager_free_out_of_bound() {
    let mut mngr = storage_mem(32);
    mngr.free(100);
  }

  #[test]
  fn test_storage_manager_free_double_free() {
    let mut mngr = storage_mem(32);
    let buf = vec![1u8; mngr.page_size as usize];

    for i in 0..3 {
      assert_eq!(mngr.write_next(&buf[..]), i);
    }

    for _ in 0..10 {
      mngr.free(1);
    }

    mngr.free(0);
    mngr.free(2);

    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.free_map.len(), 0);
  }

  #[test]
  fn test_storage_manager_free_truncate_no_evict() {
    let mut mngr = storage_mem(32);
    let buf = vec![1u8; mngr.page_size as usize];

    let page_id = mngr.write_next(&buf[..]);
    assert_eq!(mngr.num_pages(), 1);
    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.free_map.len(), 0);

    mngr.free(page_id);

    assert_eq!(mngr.num_pages(), 0);
    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.free_map.len(), 0);
  }

  #[test]
  fn test_storage_manager_free_truncate_evict() {
    let mut mngr = storage_mem(32);
    let buf = vec![1u8; mngr.page_size as usize];

    for _ in 0..9 {
      mngr.write_next(&buf[..]);
    }
    assert_eq!(mngr.write_next(&buf[..]), 9); // 10 pages in total

    for i in 0..9 {
      mngr.free(i);
    }

    assert_eq!(mngr.num_pages(), 10);
    assert_eq!(mngr.free_count, 9);
    assert_eq!(mngr.free_page_id, 8);
    assert_eq!(mngr.free_map.len(), 9);

    mngr.free(9);

    assert_eq!(mngr.num_pages(), 0);
    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.free_map.len(), 0);
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
          mngr.free(i);
        }
      }
      {
        let mngr = storage_disk(32, path);
        assert_eq!(mngr.num_pages(), 9);
        assert_eq!(mngr.free_count, 8);
        assert_eq!(mngr.free_map.len(), 8);
      }
    })
  }

  // Storage manager fuzz testing

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
        mngr.free(page);
      }

      assert_eq!(mngr.free_count, 0);
      assert_eq!(mngr.free_map.len(), 0);
      assert_eq!(mngr.num_pages(), 0);
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
        mngr.free(page);
      }
      assert_eq!(mngr.free_count as usize, mngr.free_map.len());
    }

    assert_eq!(mngr.free_count as usize, mngr.free_map.len());
    assert_eq!(mngr.free_count as usize + pages.len(), mngr.num_pages());

    while let Some(page) = pages.pop() {
      mngr.free(page);
    }
    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.free_map.len(), 0);
  }
}
