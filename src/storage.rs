use std::cell::RefCell;
use std::cmp;
use std::collections::BTreeMap;
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::rc::Rc;
use crate::error::Res;
use crate::btree;

// Abstract storage interface to write data.
trait Descriptor {
  // Reads data into the provided buffer at the position.
  fn read(&mut self, pos: u64, buf: &mut [u8]) -> Res<()>;
  // Writes data at the specified position.
  fn write(&mut self, pos: u64, buf: &[u8]) -> Res<()>;
  // Truncates to the provided length, `len` must be less than or equal to length.
  fn truncate(&mut self, len: u64) -> Res<()>;
  // Total length of the file or memory buffer, used for appends.
  fn len(&self) -> Res<u64>;
  // Total amount of memory (in bytes) used by the descriptor.
  fn mem_usage(&self) -> Res<usize>;
}

// File-based storage.
struct FileDescriptor {
  fd: File,
}

impl FileDescriptor {
  fn new(path: &str) -> Res<Self> {
    let fd = OpenOptions::new().read(true).write(true).create(true).open(path)?;
    Ok(Self { fd })
  }
}

impl Descriptor for FileDescriptor {
  fn read(&mut self, pos: u64, buf: &mut [u8]) -> Res<()> {
    if pos + buf.len() as u64 > self.len()? {
      return Err(err!("Read past EOF: pos {} len {}", pos, buf.len()));
    }
    self.fd.seek(SeekFrom::Start(pos))?;
    self.fd.read_exact(buf)?;
    Ok(())
  }

  fn write(&mut self, pos: u64, buf: &[u8]) -> Res<()> {
    if pos > self.len()? {
      return Err(err!("Write past EOF: pos {} len {}", pos, buf.len()));
    }
    self.fd.seek(SeekFrom::Start(pos))?;
    self.fd.write_all(buf)?;
    self.fd.flush()?;
    // TODO: call self.fd.sync_all()
    Ok(())
  }

  fn truncate(&mut self, len: u64) -> Res<()> {
    let curr_len = self.len()?;
    if len > curr_len {
      return Err(err!("Cannot truncate to len {}, curr_len {}", len, curr_len));
    } else if len < curr_len {
      self.fd.set_len(len)?;
    }
    Ok(())
  }

  fn len(&self) -> Res<u64> {
    Ok(self.fd.metadata()?.len())
  }

  fn mem_usage(&self) -> Res<usize> {
    Ok(0)
  }
}

// In-memory storage.
struct MemDescriptor {
  data: Vec<u8>,
}

impl MemDescriptor {
  fn new(capacity: usize) -> Res<Self> {
    Ok(Self { data: Vec::with_capacity(capacity) })
  }
}

impl Descriptor for MemDescriptor {
  fn read(&mut self, pos: u64, buf: &mut [u8]) -> Res<()> {
    let pos = pos as usize;
    if pos + buf.len() > self.data.len() {
      return Err(err!("Read past EOF: pos {} len {}", pos, buf.len()));
    }
    (&mut self.data[pos..pos + buf.len()].as_ref()).read_exact(buf)?;
    Ok(())
  }

  fn write(&mut self, pos: u64, buf: &[u8]) -> Res<()> {
    let pos = pos as usize;
    if pos > self.data.len() {
      return Err(err!("Write past EOF: pos {} len {}", pos, buf.len()));
    }
    // Write has append semantics
    let min_len = cmp::min(buf.len(), self.data[pos..].len());
    self.data[pos..pos + min_len].as_mut().write_all(&buf[0..min_len])?;
    if min_len < buf.len() {
      // Write the rest of the data
      self.data.extend_from_slice(&buf[min_len..]);
    }
    Ok(())
  }

  fn truncate(&mut self, len: u64) -> Res<()> {
    let curr_len = self.len()?;
    if len > curr_len {
      return Err(err!("Cannot truncate to len {}, curr_len {}", len, curr_len));
    } else if len < curr_len {
      self.data.truncate(len as usize);
    }
    Ok(())
  }

  fn len(&self) -> Res<u64> {
    Ok(self.data.len() as u64)
  }

  fn mem_usage(&self) -> Res<usize> {
    Ok(self.data.len())
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

  fn with_descriptor<F>(func: F) where F: Fn(&mut dyn Descriptor) -> () {
    println!("Started testing FileDescriptor");
    with_tmp_file(|path| {
      let mut desc = FileDescriptor::new(path).unwrap();
      func(&mut desc);
    });
    println!("Finished testing FileDescriptor");

    println!("Started testing MemDescriptor");
    let mut desc = MemDescriptor::new(0).unwrap();
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
    let mut desc = MemDescriptor::new(0).unwrap();
    assert!(desc.write(0, &[1, 2, 3, 4, 5, 6, 7, 8]).is_ok());
    assert_eq!(desc.mem_usage(), Ok(8));

    assert!(desc.truncate(2).is_ok());
    assert_eq!(desc.mem_usage(), Ok(2));

    // FileDescriptor has 0 memory usage
    with_tmp_file(|path| {
      let mut desc = FileDescriptor::new(path).unwrap();
      assert!(desc.write(0, &[1, 2, 3, 4, 5, 6, 7, 8]).is_ok());
      assert_eq!(desc.mem_usage(), Ok(0));
      assert!(desc.truncate(2).is_ok());
      assert_eq!(desc.mem_usage(), Ok(0));
    })
  }
}
