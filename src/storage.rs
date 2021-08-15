use std::cmp;
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
  fn mem_usage(&self) -> Res<usize> {
    match self {
      Descriptor::Disk { .. } => Ok(0),
      Descriptor::Mem { data } => Ok(data.len()),
    }
  }
}

const MAGIC: &[u8] = &[b'S', b'K', b'V', b'S'];
const METADATA_LEN: usize = 16; // 4 bytes magic + 4 bytes page size + (4 + 4) bytes on free pages

pub struct StorageManager {
  page_size: u32, // page size on disk
  desc: Descriptor,
  free_page_id: u32, // pointer to the free list, represents the absolute position of a page
  free_count: u32, // number of pages in the free list
}

impl StorageManager {
  pub fn disk(page_size: u32, path_str: &str) -> Res<Self> {
    let path = Path::new(path_str);

    if path.exists() {
      if !path.is_file() {
        return Err(err!("Not a file: {}", path_str));
      }
      if path.metadata()?.len() < METADATA_LEN as u64 {
        return Err(err!("Corrupt database file, header is too small"));
      }
      // Because we don't know our page size, we need to read the minimum amount
      // to load our metadata: 4 bytes magic + 4 bytes page size + (4 + 4) bytes on free pages
      let mut page_buf = vec![0u8; METADATA_LEN];
      let mut desc = Descriptor::disk(path_str)?;
      desc.read(0, &mut page_buf[..])?;

      if &page_buf[..4] != MAGIC {
        return Err(err!("Corrupt database file, invalid MAGIC"));
      }

      let page_size = u8_u32!(&page_buf[4..8]);
      if page_size == 0 {
        return Err(err!("Invalid page size {}", page_size));
      }

      let mngr = Self {
        page_size,
        desc,
        free_page_id: u8_u32!(&page_buf[8..12]),
        free_count: u8_u32!(&page_buf[12..16]),
      };
      Ok(mngr)
    } else {
      if page_size == 0 {
        return Err(err!("Invalid page size {}", page_size));
      }

      let desc = Descriptor::disk(path_str)?;
      let mut mngr = Self { page_size, desc, free_page_id: 0, free_count: 0 };
      mngr.sync()?;
      Ok(mngr)
    }
  }

  pub fn mem(page_size: u32, capacity: usize) -> Res<Self> {
    if page_size == 0 {
      return Err(err!("Invalid page size {}", page_size));
    }
    let desc = Descriptor::mem(capacity)?;
    let mut mngr = Self { page_size, desc, free_page_id: 0, free_count: 0 };
    mngr.sync()?; // stores metadata in page 0 and advances descriptor
    Ok(mngr)
  }

  #[inline]
  fn pos(&self, page_id: u32) -> u64 {
    page_id as u64 * self.page_size as u64
  }

  // Reads the content of the page with `page_id` into the buffer.
  pub fn read(&mut self, page_id: u32, buf: &mut [u8]) -> Res<()> {
    self.desc.read(self.pos(page_id), &mut buf[..self.page_size as usize])
  }

  // Writes data in the page with `page_id`.
  pub fn write(&mut self, page_id: u32, buf: &[u8]) -> Res<()> {
    self.desc.write(self.pos(page_id), &buf[..self.page_size as usize])
  }

  // Writes data to the next available page and returns its page id.
  pub fn write_next(&mut self, buf: &[u8]) -> Res<u32> {
    let page_id = if self.free_count > 0 {
      // TODO: optimise this
      let mut page_buf = vec![0u8; self.page_size as usize];
      self.read(self.free_page_id, &mut page_buf[..])?;
      let next_page_id = self.free_page_id;
      self.free_page_id = u8_u32!(&page_buf[0..4]);
      self.free_count -= 1;
      self.sync()?;
      next_page_id
    } else {
      self.num_pages()? as u32
    };
    self.write(page_id, buf)?;
    Ok(page_id)
  }

  // Marks page as free so it can be reused.
  pub fn free(&mut self, page_id: u32) -> Res<()> {
    if self.free_count > 0 {
      // TODO: optimise this
      let mut page_buf = vec![0u8; self.page_size as usize];
      (&mut page_buf[0..]).write(&u32_u8!(self.free_page_id))?;
      self.write(page_id, &page_buf)?;
    }
    self.free_page_id = page_id;
    self.free_count += 1;
    self.sync()
  }

  // Sync metadata + free pages in page 0.
  pub fn sync(&mut self) -> Res<()> {
    let mut page_buf = vec![0u8; self.page_size as usize];
    (&mut page_buf[0..]).write(MAGIC)?;
    (&mut page_buf[4..]).write(&u32_u8!(self.page_size))?;
    (&mut page_buf[8..]).write(&u32_u8!(self.free_page_id))?;
    (&mut page_buf[12..]).write(&u32_u8!(self.free_count))?;
    self.write(0, &page_buf[..])
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
    Ok(self.desc.len()? as usize / self.page_size as usize)
  }

  // Number of free pages that were reclaimed.
  pub fn num_free_pages(&self) -> Res<usize> {
    Ok(self.free_count as usize)
  }

  // The amount of memory (in bytes) used by the storage manager.
  pub fn mem_usage(&self) -> Res<usize> {
    self.desc.mem_usage()
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::env::temp_dir;
  use std::fs::remove_file;
  use std::path::Path;

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

  #[test]
  fn test_storage_tmp() {
    with_descriptor(|desc| {
      desc.write(0, "Hello, world!".as_bytes()).unwrap();
    });
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
    assert_eq!(desc.mem_usage(), Ok(8));

    assert!(desc.truncate(2).is_ok());
    assert_eq!(desc.mem_usage(), Ok(2));

    // FileDescriptor has 0 memory usage
    with_tmp_file(|path| {
      let mut desc = Descriptor::disk(path).unwrap();
      assert!(desc.write(0, &[1, 2, 3, 4, 5, 6, 7, 8]).is_ok());
      assert_eq!(desc.mem_usage(), Ok(0));
      assert!(desc.truncate(2).is_ok());
      assert_eq!(desc.mem_usage(), Ok(0));
    })
  }

  #[test]
  fn test_storage_manager_init_mem() {
    let mngr = StorageManager::mem(24, 0).unwrap();
    assert_eq!(mngr.page_size, 24);
    assert_eq!(mngr.free_page_id, 0);
    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.num_pages().unwrap(), 1);
    assert_eq!(mngr.mem_usage().unwrap(), 24);
  }

  #[test]
  fn test_storage_manager_init_mem_invalid_page_size() {
    assert!(StorageManager::mem(0, 0).is_err());
  }

  #[test]
  fn test_storage_manager_init_disk() {
    with_tmp_file(|path| {
      let mngr = StorageManager::disk(24, path).unwrap();
      assert_eq!(mngr.page_size, 24);
      assert_eq!(mngr.free_page_id, 0);
      assert_eq!(mngr.free_count, 0);
      assert_eq!(mngr.num_pages().unwrap(), 1);
      assert_eq!(mngr.mem_usage().unwrap(), 0);
    })
  }

  #[test]
  fn test_storage_manager_init_disk_2() {
    with_tmp_file(|path| {
      let _mngr = StorageManager::disk(24, path).unwrap();
      let mngr = StorageManager::disk(32, path).unwrap();

      assert_eq!(mngr.page_size, 24);
      assert_eq!(mngr.free_page_id, 0);
      assert_eq!(mngr.free_count, 0);
      assert_eq!(mngr.num_pages().unwrap(), 1);
      assert_eq!(mngr.mem_usage().unwrap(), 0);
    })
  }

  #[test]
  fn test_storage_manager_init_disk_invalid_page_size() {
    with_tmp_file(|path| {
      assert!(StorageManager::disk(0, path).is_err());
    })
  }

  #[test]
  fn test_storage_manager_write_read() {
    let mut mngr = StorageManager::mem(32, 0).unwrap();
    let mut buf = vec![5u8; mngr.page_size as usize];
    (&mut buf[..]).write(&[1, 2, 3, 4]).unwrap();

    let page_id = mngr.write_next(&buf[..]).unwrap();
    assert_eq!(page_id, 1);

    (&mut buf[4..]).write(&[8, 9, 0]).unwrap();
    mngr.write(page_id, &buf[..]).unwrap();

    mngr.read(page_id, &mut buf[..]).unwrap();
    assert_eq!(&buf[..8], &[1, 2, 3, 4, 8, 9, 0, 5]);
  }

  #[test]
  fn test_storage_manager_write_free() {
    let mut mngr = StorageManager::mem(32, 0).unwrap();
    let buf = vec![5u8; mngr.page_size as usize];

    assert_eq!(mngr.write_next(&buf[..]), Ok(1));
    assert_eq!(mngr.write_next(&buf[..]), Ok(2));
    assert_eq!(mngr.write_next(&buf[..]), Ok(3));

    assert_eq!(mngr.free_count, 0);
    assert_eq!(mngr.free_page_id, 0);

    mngr.free(3).unwrap();
    mngr.free(1).unwrap();
    mngr.free(2).unwrap();

    assert_eq!(mngr.free_count, 3);
    assert_eq!(mngr.free_page_id, 2);

    assert_eq!(mngr.write_next(&buf[..]), Ok(2));
    assert_eq!(mngr.write_next(&buf[..]), Ok(1));
    assert_eq!(mngr.write_next(&buf[..]), Ok(3));

    assert_eq!(mngr.free_count, 0);
    assert_ne!(mngr.free_page_id, 0);
  }

  #[test]
  fn test_storage_manager_disk_meta_sync() {
    with_tmp_file(|path| {
      let mut mngr = StorageManager::disk(32, path).unwrap();
      mngr.page_size = 64;
      mngr.free_page_id = 100;
      mngr.free_count = 2;

      mngr.sync().unwrap();

      let mngr = StorageManager::disk(32, path).unwrap();
      assert_eq!(mngr.page_size, 64);
      assert_eq!(mngr.free_page_id, 100);
      assert_eq!(mngr.free_count, 2);
    })
  }
}
