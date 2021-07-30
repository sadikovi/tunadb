use std::cmp;
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use crate::error::Res;

// Abstract storage interface to write data.
pub trait Storage {
  // Reads data into the provided buffer at the position.
  fn read(&mut self, pos: u64, buf: &mut [u8]) -> Res<()>;
  // Writes data at the specified position.
  fn write(&mut self, pos: u64, buf: &[u8]) -> Res<()>;
}

// File-based storage.
pub struct FileStorage {
  handle: File,
}

impl FileStorage {
  pub fn new(path: &str) -> Res<Self> {
    let handle = OpenOptions::new().read(true).write(true).create(true).open(path)?;
    Ok(Self { handle })
  }

  fn meta_len(&self) -> Res<u64> {
    Ok(self.handle.metadata()?.len())
  }
}

impl Storage for FileStorage {
  fn read(&mut self, pos: u64, buf: &mut [u8]) -> Res<()> {
    if pos + buf.len() as u64 > self.meta_len()? {
      return Err(err!("Read past EOF: pos {} len {}", pos, buf.len()));
    }
    self.handle.seek(SeekFrom::Start(pos))?;
    self.handle.read_exact(buf)?;
    Ok(())
  }

  fn write(&mut self, pos: u64, buf: &[u8]) -> Res<()> {
    if pos > self.meta_len()? {
      return Err(err!("Write past EOF: pos {} len {}", pos, buf.len()));
    }
    self.handle.seek(SeekFrom::Start(pos))?;
    self.handle.write_all(buf)?;
    self.handle.flush()?;
    // TODO: call self.handle.sync_all()
    Ok(())
  }
}

// In-memory storage.
pub struct MemStorage {
  data: Vec<u8>,
}

impl MemStorage {
  pub fn new(capacity: usize) -> Res<Self> {
    Ok(Self { data: Vec::with_capacity(capacity) })
  }
}

impl Storage for MemStorage {
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
}
