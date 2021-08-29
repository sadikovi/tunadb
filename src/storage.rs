use std::cmp;
use std::collections::BTreeMap;
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::Path;
use crate::error::Res;

enum Descriptor {
  // File-based storage.
  Disk { fd: File },
  // In-memory storage.
  Mem { data: Vec<u8> },
}

impl Descriptor {
  fn disk(path: &str) -> Res<Self> {
    let fd = OpenOptions::new().read(true).write(true).create(true).open(path)?;
    Ok(Descriptor::Disk { fd })
  }

  fn mem(capacity: usize) -> Res<Self> {
    let data = Vec::with_capacity(capacity);
    Ok(Descriptor::Mem { data })
  }

  // Reads data into the provided buffer at the position.
  fn read(&mut self, pos: u64, buf: &mut [u8]) -> Res<()> {
    if pos + buf.len() as u64 > self.len()? {
      return Err(err!("Read past EOF: pos {} len {}", pos, buf.len()));
    }

    match self {
      Descriptor::Disk { fd } => {
        fd.seek(SeekFrom::Start(pos))?;
        fd.read_exact(buf)?;
      },
      Descriptor::Mem { data } => {
        let pos = pos as usize;
        (&mut data[pos..pos + buf.len()].as_ref()).read_exact(buf)?;
      },
    }

    Ok(())
  }

  // Writes data at the specified position.
  fn write(&mut self, pos: u64, buf: &[u8]) -> Res<()> {
    if pos > self.len()? {
      return Err(err!("Write past EOF: pos {} len {}", pos, buf.len()));
    }

    match self {
      Descriptor::Disk { fd } => {
        fd.seek(SeekFrom::Start(pos))?;
        fd.write_all(buf)?;
        fd.flush()?;
        // TODO: call self.fd.sync_all()
      },
      Descriptor::Mem { data } => {
        let pos = pos as usize;
        // Write has append semantics
        let min_len = cmp::min(buf.len(), data[pos..].len());
        data[pos..pos + min_len].as_mut().write_all(&buf[0..min_len])?;
        if min_len < buf.len() {
          // Write the rest of the data
          data.extend_from_slice(&buf[min_len..]);
        }
      },
    }

    Ok(())
  }

  // Truncates to the provided length, `len` must be less than or equal to length.
  fn truncate(&mut self, len: u64) -> Res<()> {
    let curr_len = self.len()?;
    if len > curr_len {
      return Err(err!("Cannot truncate to len {}, curr_len {}", len, curr_len));
    }

    match self {
      Descriptor::Disk { fd } => {
        if len < curr_len {
          fd.set_len(len)?;
        }
      },
      Descriptor::Mem { data } => {
        if len < curr_len {
          data.truncate(len as usize);
        }
      },
    }

    Ok(())
  }

  // Total length of the file or memory buffer, used for appends.
  fn len(&self) -> Res<u64> {
    match self {
      Descriptor::Disk { fd } => Ok(fd.metadata()?.len()),
      Descriptor::Mem { data } => Ok(data.len() as u64),
    }
  }

  // Total amount of memory (in bytes) used by the descriptor.
  fn mem_usage(&self) -> usize {
    match self {
      Descriptor::Disk { .. } => 0,
      Descriptor::Mem { data } => data.len(),
    }
  }
}

const MAGIC: &[u8] = &[b'S', b'K', b'V', b'S'];
// We have a fixed metadata size, see sync() method for more information.
const METADATA_LEN: usize = 32;
const MIN_PAGE_SIZE: u32 = 16;
const MAX_PAGE_SIZE: u32 = 1 * 1024 * 1024; // 1MB
const DEFAULT_PAGE_SIZE: u32 = 4096; // 4KB

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
  pub fn build(self) -> Res<Options> {
    if self.opts.is_disk && self.opts.disk_path.len() == 0 {
      return Err(err!("Empty file path"));
    }

    if self.opts.page_size < MIN_PAGE_SIZE || self.opts.page_size > MAX_PAGE_SIZE {
      return Err(err!("Invalid page size {}", self.opts.page_size));
    }

    Ok(self.opts)
  }
}

pub struct StorageManager {
  page_size: u32, // page size on disk
  desc: Descriptor,
  free_page_id: u32, // pointer to the free list, represents the absolute position of a page
  free_count: u32, // number of pages in the free list
  free_map: BTreeMap<u32, (Option<u32>, Option<u32>)>, // page id -> (prev, next), keys are sorted
  counter: u64, // general monotonically increasing counter
}

impl StorageManager {
  pub fn new(opts: &Options) -> Res<Self> {
    if opts.is_disk {
      let path = Path::new(&opts.disk_path);

      if path.exists() {
        if !path.is_file() {
          return Err(err!("Not a file: {}", path.display()));
        }

        if path.metadata()?.len() < METADATA_LEN as u64 {
          return Err(err!("Corrupt database file, header is too small"));
        }

        let mut page_buf = vec![0u8; METADATA_LEN];
        let mut desc = Descriptor::disk(opts.disk_path.as_ref())?;
        desc.read(0, &mut page_buf[..])?;

        if &page_buf[..4] != MAGIC {
          return Err(err!("Corrupt database file, invalid MAGIC"));
        }

        let page_size = u8_u32!(&page_buf[4..8]);
        if page_size < MIN_PAGE_SIZE || page_size > MAX_PAGE_SIZE {
          return Err(err!("Corrupt database file, invalid page size {}", page_size));
        }

        let free_page_id = u8_u32!(&page_buf[8..12]);
        let free_count = u8_u32!(&page_buf[12..16]);
        let counter = u8_u64!(&page_buf[16..24]);
        let mut free_map = BTreeMap::new();

        // Reconstruct the in-memory map
        let mut cnt = 0;
        let mut prev_opt = None;
        let mut curr = free_page_id;
        let mut page_buf = vec![0u8; page_size as usize];
        while cnt < free_count {
          let next_opt = if cnt + 1 < free_count {
            desc.read(pos(curr, page_size), &mut page_buf[..]).unwrap();
            Some(u8_u32!(&page_buf[0..4]))
          } else {
            None
          };

          free_map.insert(curr, (prev_opt, next_opt));
          prev_opt = Some(curr);
          curr = next_opt.unwrap_or(u32::MAX);

          cnt += 1;
        }
        Ok(Self { page_size, desc, free_page_id, free_count, free_map, counter })
      } else {
        let mut mngr = Self {
          page_size: opts.page_size,
          desc: Descriptor::disk(opts.disk_path.as_ref())?,
          free_page_id: 0,
          free_count: 0,
          free_map: BTreeMap::new(),
          counter: 0,
        };
        mngr.sync()?;
        Ok(mngr)
      }
    } else {
      let mut mngr = Self {
        page_size: opts.page_size,
        desc: Descriptor::mem(opts.mem_capacity)?,
        free_page_id: 0,
        free_count: 0,
        free_map: BTreeMap::new(),
        counter: 0,
      };
      mngr.sync()?; // stores metadata in page 0 and advances descriptor
      Ok(mngr)
    }
  }

  // Returns the next counter.
  pub fn next_id(&mut self) -> Res<u64> {
    let value = self.counter;
    self.counter += 1;
    self.sync()?;
    Ok(value)
  }

  // Reads the content of the page with `page_id` into the buffer.
  pub fn read(&mut self, page_id: u32, buf: &mut [u8]) -> Res<()> {
    self.desc.read(pos(page_id, self.page_size), &mut buf[..self.page_size as usize])
  }

  // Writes data in the page with `page_id`.
  pub fn write(&mut self, page_id: u32, buf: &[u8]) -> Res<()> {
    self.desc.write(pos(page_id, self.page_size), &buf[..self.page_size as usize])
  }

  // Writes data to the next available page and returns its page id.
  pub fn write_next(&mut self, buf: &[u8]) -> Res<u32> {
    let page_id = if self.free_count > 0 {
      let (&next_page_id, _) = self.free_map.first_key_value().unwrap();
      self.remove_free_page(next_page_id)?;
      self.sync()?;
      next_page_id
    } else {
      self.num_pages()? as u32
    };
    self.write(page_id, buf)?;
    Ok(page_id)
  }

  // Removes the provided page id from free list and free map.
  // Does not perform sync.
  fn remove_free_page(&mut self, page_id: u32) -> Res<()> {
    println!("{:?}, remove {}", self.free_map, page_id);
    if let Some(value) = self.free_map.remove(&page_id) {
      self.free_count -= 1;

      match value {
        (Some(prev), Some(next)) => {
          // TODO: optimise this
          let mut page_buf = vec![0u8; self.page_size as usize];
          (&mut page_buf[0..]).write(&u32_u8!(next))?;
          self.write(prev, &page_buf)?;
          // Point prev to next
          self.free_map.get_mut(&prev).unwrap().1 = Some(next);
          self.free_map.get_mut(&next).unwrap().0 = Some(prev);
        },
        (Some(prev), None) => {
          // It is the tail of the free list, there is no need to override the page data.
          self.free_map.get_mut(&prev).unwrap().1 = None; // next = None
        },
        (None, Some(next)) => {
          // Current head of the free list.
          self.free_page_id = next;
          self.free_map.get_mut(&next).unwrap().0 = None; // prev = None
        },
        (None, None) => {
          // Free list only had one element.
          assert_eq!(self.free_count, 0);
          assert_eq!(self.free_map.len(), 0);
        },
      }

      Ok(())
    } else {
      Err(err!("Free page {} is not found", page_id))
    }
  }

  // Marks page as free so it can be reused.
  pub fn free(&mut self, page_id: u32) -> Res<()> {
    let num_pages = self.num_pages()?;

    if page_id as usize >= num_pages {
      return Err(err!("Invalid page {} to free", page_id));
    }

    // If the page is the last page, truncate instead of adding to the free list.
    if num_pages - 1 == page_id as usize {
      let mut last_page_id = page_id;
      while let Some((&curr, _)) = self.free_map.last_key_value() {
        if curr + 1 == last_page_id {
          last_page_id = curr;
          self.remove_free_page(curr)?;
        } else {
          break;
        }
      }
      self.desc.truncate(pos(last_page_id, self.page_size))?;
    } else {
      if self.free_count > 0 {
        // Update free map
        self.free_map.get_mut(&self.free_page_id).unwrap().0 = Some(page_id);
        self.free_map.insert(page_id, (None, Some(self.free_page_id)));

        // Update the page
        // TODO: optimise this
        let mut page_buf = vec![0u8; self.page_size as usize];
        (&mut page_buf[0..]).write(&u32_u8!(self.free_page_id))?;
        self.write(page_id, &page_buf)?;
      } else {
        self.free_map.insert(page_id, (None, None));
      }

      self.free_page_id = page_id;
      self.free_count += 1;
    }

    self.sync()
  }

  // Sync metadata + free pages in page 0.
  pub fn sync(&mut self) -> Res<()> {
    let mut buf = vec![0u8; METADATA_LEN];
    (&mut buf[0..]).write(MAGIC)?;
    (&mut buf[4..]).write(&u32_u8!(self.page_size))?;
    (&mut buf[8..]).write(&u32_u8!(self.free_page_id))?;
    (&mut buf[12..]).write(&u32_u8!(self.free_count))?;
    (&mut buf[16..]).write(&u64_u8!(self.counter))?;
    self.desc.write(0, &buf[..])
  }

  // ==================
  // Storage statistics
  // ==================

  // Returns the configured page size for the storage manager.
  pub fn page_size(&self) -> usize {
    self.page_size as usize
  }

  // Total number of pages that is managed by the storage manager.
  pub fn num_pages(&self) -> Res<usize> {
    let num_pages = (self.desc.len()? - METADATA_LEN as u64) / self.page_size as u64;
    Ok(num_pages as usize)
  }

  // Number of free pages that were reclaimed.
  pub fn num_free_pages(&self) -> Res<usize> {
    Ok(self.free_count as usize)
  }

  // The amount of memory (in bytes) used by the storage manager.
  pub fn mem_usage(&self) -> usize {
    let desc_mem_usage = self.desc.mem_usage();
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

  fn with_descriptor<F>(func: F) where F: Fn(&mut Descriptor) -> () {
    println!("Started testing FileDescriptor");
    with_tmp_file(|path| {
      let mut desc = Descriptor::disk(path).unwrap();
      func(&mut desc);
    });
    println!("Finished testing FileDescriptor");

    println!("Started testing MemDescriptor");
    let mut desc = Descriptor::mem(0).unwrap();
    func(&mut desc);
    println!("Finished testing MemDescriptor");
  }

  fn storage_mem(page_size: u32) -> StorageManager {
    let opts = Options::new().as_mem(0).with_page_size(page_size).build().unwrap();
    StorageManager::new(&opts).unwrap()
  }

  fn storage_disk(page_size: u32, path: &str) -> StorageManager {
    let opts = Options::new().as_disk(path).with_page_size(page_size).build().unwrap();
    StorageManager::new(&opts).unwrap()
  }

  #[test]
  fn test_storage_tmp() {
    with_descriptor(|desc| {
      desc.write(0, "Hello, world!".as_bytes()).unwrap();
    });
  }

  #[test]
  fn test_storage_options_default() {
    let opts = Options::new().build().unwrap();
    assert!(!opts.is_disk);
    assert_eq!(opts.page_size, DEFAULT_PAGE_SIZE);
  }

  #[test]
  fn test_storage_options_mem() {
    let opts = Options::new().as_mem(128).build().unwrap();
    assert!(!opts.is_disk);
    assert_eq!(opts.mem_capacity, 128);
    assert_eq!(opts.page_size, DEFAULT_PAGE_SIZE);
  }

  #[test]
  fn test_storage_options_disk() {
    with_tmp_file(|path| {
      let opts = Options::new().as_disk(path).with_page_size(32).build().unwrap();
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
        .build()
        .unwrap();

      assert!(!opts.is_disk);
      assert_eq!(opts.mem_capacity, 128);
      assert_eq!(opts.page_size, 64);
    });
  }

  #[test]
  fn test_storage_options_invalid() {
    let opts = Options::new().as_disk(&"").build();
    assert!(opts.is_err());

    let opts = Options::new().as_mem(0).with_page_size(MIN_PAGE_SIZE - 1).build();
    assert!(opts.is_err());

    let opts = Options::new().as_mem(0).with_page_size(MAX_PAGE_SIZE + 1).build();
    assert!(opts.is_err());
  }

  #[test]
  fn test_storage_descriptor_write() {
    with_descriptor(|desc| {
      assert!(desc.write(10, &[1, 2, 3]).is_err());
      assert!(desc.write(0, &[1, 2, 3]).is_ok());
      assert!(desc.write(3, &[4, 5, 6]).is_ok());
      assert!(desc.write(8, &[0, 0, 0]).is_err());
    });
  }

  #[test]
  fn test_storage_descriptor_read() {
    with_descriptor(|desc| {
      assert!(desc.write(0, &[1, 2, 3, 4, 5, 6, 7, 8]).is_ok());

      let mut res = vec![0; 5];
      assert!(desc.read(0, &mut res[0..4]).is_ok());
      assert_eq!(res, vec![1, 2, 3, 4, 0]);

      // Invalid reads
      assert!(desc.read(100, &mut res[0..4]).is_err());
      assert!(desc.read(7, &mut res[0..4]).is_err());
    });
  }

  #[test]
  fn test_storage_descriptor_truncate() {
    with_descriptor(|desc| {
      assert!(desc.write(0, &[1, 2, 3, 4, 5, 6, 7, 8]).is_ok());

      // Truncate with larger length
      assert!(desc.truncate(100).is_err());

      // Truncate with smaller length
      assert!(desc.truncate(5).is_ok());
      let mut res = vec![0; 10];
      assert!(desc.read(0, &mut res[0..5]).is_ok());
      assert_eq!(&res[0..5], &[1, 2, 3, 4, 5]);
      assert!(desc.read(0, &mut res[0..6]).is_err());

      // Truncate the same length
      assert!(desc.truncate(5).is_ok());
      assert_eq!(desc.len(), Ok(5));
    });
  }

  #[test]
  fn test_storage_descriptor_len() {
    with_descriptor(|desc| {
      assert!(desc.write(0, &[1, 2, 3, 4, 5, 6, 7, 8]).is_ok());

      assert_eq!(desc.len(), Ok(8));
      for len in (0..desc.len().unwrap()).rev() {
        assert!(desc.truncate(len).is_ok());
        assert_eq!(desc.len(), Ok(len));
      }
    });
  }

  #[test]
  fn test_storage_descriptor_mem_usage() {
    let mut desc = Descriptor::mem(0).unwrap();
    assert!(desc.write(0, &[1, 2, 3, 4, 5, 6, 7, 8]).is_ok());
    assert_eq!(desc.mem_usage(), 8);

    assert!(desc.truncate(2).is_ok());
    assert_eq!(desc.mem_usage(), 2);

    // FileDescriptor has 0 memory usage
    with_tmp_file(|path| {
      let mut desc = Descriptor::disk(path).unwrap();
      assert!(desc.write(0, &[1, 2, 3, 4, 5, 6, 7, 8]).is_ok());
      assert_eq!(desc.mem_usage(), 0);
      assert!(desc.truncate(2).is_ok());
      assert_eq!(desc.mem_usage(), 0);
    })
  }

  #[test]
  fn test_storage_manager_init_mem() {
    let mngr = storage_mem(24);
    assert_eq!(mngr.page_size, 24);
    assert_eq!(mngr.free_page_id, 0);
    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.counter, 0);
    assert_eq!(mngr.num_pages().unwrap(), 0);
    assert_eq!(mngr.mem_usage(), METADATA_LEN);
  }

  #[test]
  fn test_storage_manager_init_disk() {
    with_tmp_file(|path| {
      let mngr = storage_disk(24, path);
      assert_eq!(mngr.page_size, 24);
      assert_eq!(mngr.free_page_id, 0);
      assert_eq!(mngr.free_count, 0);
      assert_eq!(mngr.counter, 0);
      assert_eq!(mngr.num_pages().unwrap(), 0);
      assert_eq!(mngr.mem_usage(), 0);
      assert_eq!(Path::new(path).metadata().unwrap().len(), METADATA_LEN as u64);
    })
  }

  #[test]
  fn test_storage_manager_init_disk_2() {
    with_tmp_file(|path| {
      let _mngr = storage_disk(24, path);
      let mngr = storage_disk(32, path);

      assert_eq!(mngr.page_size, 24);
      assert_eq!(mngr.free_page_id, 0);
      assert_eq!(mngr.free_count, 0);
      assert_eq!(mngr.counter, 0);
      assert_eq!(mngr.num_pages().unwrap(), 0);
      assert_eq!(mngr.mem_usage(), 0);
    })
  }

  #[test]
  fn test_storage_manager_disk_meta_sync() {
    with_tmp_file(|path| {
      {
        let mut mngr = storage_disk(32, path);
        let buf = vec![5u8; mngr.page_size as usize];

        mngr.write_next(&buf[..]).unwrap();
        mngr.write_next(&buf[..]).unwrap();
        mngr.free(0).unwrap();
        mngr.next_id().unwrap();

        mngr.sync().unwrap();
      }
      {
        let mngr = storage_disk(32, path);
        assert_eq!(mngr.page_size, 32);
        assert_eq!(mngr.free_page_id, 0);
        assert_eq!(mngr.free_count, 1);
        assert_eq!(mngr.counter, 1);
      }
    })
  }

  #[test]
  fn test_storage_manager_counter_persist() {
    with_tmp_file(|path| {
      {
        let mut mngr = storage_disk(32, path);
        for i in 0..10 {
          assert_eq!(mngr.next_id(), Ok(i));
        }
      }
      {
        let mut mngr = storage_disk(32, path);
        assert_eq!(mngr.next_id(), Ok(10));
      }
    })
  }

  #[test]
  fn test_storage_manager_write_read() {
    let mut mngr = storage_mem(32);
    let mut buf = vec![5u8; mngr.page_size as usize];
    (&mut buf[..]).write(&[1, 2, 3, 4]).unwrap();

    let page_id = mngr.write_next(&buf[..]).unwrap();
    assert_eq!(page_id, 0);

    (&mut buf[4..]).write(&[8, 9, 0]).unwrap();
    mngr.write(page_id, &buf[..]).unwrap();

    mngr.read(page_id, &mut buf[..]).unwrap();
    assert_eq!(&buf[..8], &[1, 2, 3, 4, 8, 9, 0, 5]);
  }

  #[test]
  fn test_storage_manager_write_free() {
    let mut mngr = storage_mem(32);
    let buf = vec![5u8; mngr.page_size as usize];

    assert_eq!(mngr.write_next(&buf[..]), Ok(0));
    assert_eq!(mngr.write_next(&buf[..]), Ok(1));
    assert_eq!(mngr.write_next(&buf[..]), Ok(2));

    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.free_page_id, 0); // does not really matter since the count is 0

    mngr.free(2).unwrap();
    mngr.free(0).unwrap();
    mngr.free(1).unwrap();

    // This is because our free map would truncate the source instead of keeping the pages
    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.free_page_id, 0); // 0 because when we truncate, we don't update free ptr
    assert_eq!(mngr.free_map.len(), 0);

    assert_eq!(mngr.write_next(&buf[..]), Ok(0));
    assert_eq!(mngr.write_next(&buf[..]), Ok(1));
    assert_eq!(mngr.write_next(&buf[..]), Ok(2));

    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.free_page_id, 0);
    assert_eq!(mngr.free_map.len(), 0);
  }

  #[test]
  fn test_storage_manager_free_out_of_bound() {
    let mut mngr = storage_mem(32);
    assert!(mngr.free(100).is_err());
  }

  #[test]
  fn test_storage_manager_free_double_free() {
    let mut mngr = storage_mem(32);
    let buf = vec![1u8; mngr.page_size as usize];

    for i in 0..3 {
      assert_eq!(mngr.write_next(&buf[..]).unwrap(), i);
    }

    for _ in 0..10 {
      mngr.free(1).unwrap();
    }

    mngr.free(0).unwrap();
    mngr.free(2).unwrap();

    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.free_map.len(), 0);
  }

  #[test]
  fn test_storage_manager_free_truncate_no_evict() {
    let mut mngr = storage_mem(32);
    let buf = vec![1u8; mngr.page_size as usize];

    let page_id = mngr.write_next(&buf[..]).unwrap();
    assert_eq!(mngr.num_pages(), Ok(1));
    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.free_map.len(), 0);

    mngr.free(page_id).unwrap();

    assert_eq!(mngr.num_pages(), Ok(0));
    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.free_map.len(), 0);
  }

  #[test]
  fn test_storage_manager_free_truncate_evict() {
    let mut mngr = storage_mem(32);
    let buf = vec![1u8; mngr.page_size as usize];

    for _ in 0..9 {
      mngr.write_next(&buf[..]).unwrap();
    }
    assert_eq!(mngr.write_next(&buf[..]).unwrap(), 9); // 10 pages in total

    for i in 0..9 {
      mngr.free(i).unwrap();
    }

    assert_eq!(mngr.num_pages(), Ok(10));
    assert_eq!(mngr.free_count, 9);
    assert_eq!(mngr.free_page_id, 8);
    assert_eq!(mngr.free_map.len(), 9);

    mngr.free(9).unwrap();

    assert_eq!(mngr.num_pages(), Ok(0));
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
          assert_eq!(mngr.write_next(&buf[..]).unwrap(), i);
        }

        for i in 0..8 {
          mngr.free(i).unwrap();
        }
      }
      {
        let mngr = storage_disk(32, path);
        assert_eq!(mngr.num_pages(), Ok(9));
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
        pages.push(mngr.write_next(&buf[..]).unwrap());
      }

      shuffle(&mut pages);

      while let Some(page) = pages.pop() {
        mngr.free(page).unwrap();
      }

      assert_eq!(mngr.free_count, 0);
      assert_eq!(mngr.free_map.len(), 0);
      assert_eq!(mngr.num_pages(), Ok(0));
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
        pages.push(mngr.write_next(&buf[..]).unwrap());
      }

      shuffle(&mut pages);

      while pages.len() > num_pages_to_keep {
        let page = pages.pop().unwrap();
        mngr.free(page).unwrap();
      }
      assert_eq!(mngr.free_count as usize, mngr.free_map.len());
    }

    assert_eq!(mngr.free_count as usize, mngr.free_map.len());
    assert_eq!(mngr.free_count as usize + pages.len(), mngr.num_pages().unwrap());

    while let Some(page) = pages.pop() {
      mngr.free(page).unwrap();
    }
    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.free_map.len(), 0);
  }
}
