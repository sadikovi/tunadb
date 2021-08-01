use std::cell::RefCell;
use std::cmp;
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::rc::Rc;
use crate::error::Res;

// Abstract storage interface to write data.
trait Descriptor {
  // Reads data into the provided buffer at the position.
  fn read(&mut self, pos: u64, buf: &mut [u8]) -> Res<()>;
  // Writes data at the specified position.
  fn write(&mut self, pos: u64, buf: &[u8]) -> Res<()>;
  // Total length of the file or memory buffer, used for appends.
  fn len(&self) -> Res<u64>;
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

  fn len(&self) -> Res<u64> {
    Ok(self.fd.metadata()?.len())
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

  fn len(&self) -> Res<u64> {
    Ok(self.data.len() as u64)
  }
}

const INVALID_PAGE_ID: u64 = u64::MAX;
const PAGE_MAGIC: &[u8] = &[b'P', b'A', b'G', b'E'];
const PAGE_META_LEN: usize = 16; // 4 bytes magic + 4 bytes len + 8 bytes cont

struct Page {
  len: usize, // actual length of the data (< page_size)
  cont_page_id: u64, // continuation page id (free -> free, active -> overflow)
  data: Vec<u8>, // vector of page_size len, must be used as &mut [u8]
}

impl Page {
  // Creates an empty page with length 0 and no continuation
  fn empty(page_size: usize) -> Page {
    Self { len: 0, cont_page_id: INVALID_PAGE_ID, data: vec![0; page_size] }
  }

  fn offset(&self) -> usize {
    PAGE_META_LEN + self.len
  }

  fn capacity(&self) -> usize {
    self.data.len() - self.offset()
  }

  // Writes bytes into page and returns the number of bytes written.
  fn write(&mut self, buf: &[u8]) -> Res<usize> {
    let offset = self.offset();
    let len = cmp::min(buf.len(), self.capacity());
    (&mut self.data[offset..offset + len]).write(&buf[..len])?;
    self.len += len;
    Ok(len)
  }

  // Reads full page content into the mutable buffer.
  fn read(&self, buf: &mut Vec<u8>) -> Res<()> {
    buf.extend(&self.data[PAGE_META_LEN..PAGE_META_LEN + self.len]);
    Ok(())
  }

  // Converts byte buffer into Page.
  fn from(buf: Vec<u8>) -> Res<Self> {
    if buf.len() < PAGE_META_LEN {
      return Err(err!("Page buffer is too small ({})", buf.len()));
    }
    if &buf[0..4] != PAGE_MAGIC {
      return Err(err!("Invalid page magic: {:?}", &buf[0..4]));
    }
    // Read length of the data in the page
    let len = u32_le!(&buf[4..8]) as usize;
    if len > buf.len() {
      return Err(err!("Invalid page length: {}", len));
    }
    // Read continuation position for the page
    let cont_page_id = u64_le!(&buf[8..16]);
    Ok(Self { len, cont_page_id, data: buf })
  }

  // Stores page metadata into the byte buffer and returns it.
  fn into(mut self) -> Res<Vec<u8>> {
    if self.data.len() < PAGE_META_LEN {
      return Err(err!("Page buffer is too small ({})", self.data.len()));
    }
    (&mut self.data[0..4]).write_all(&PAGE_MAGIC)?;
    if self.len > self.data.len() {
      return Err(err!("Invalid page length: {}", self.len));
    }
    (&mut self.data[4..8]).write_all(&(self.len as u32).to_le_bytes())?;
    (&mut self.data[8..16]).write_all(&self.cont_page_id.to_le_bytes())?;
    Ok(self.data)
  }
}

// Free pages are not stored in the page table, they are stored in a separate data structure.
pub struct StorageManager {
  page_size: usize, // page size on disk
  page_counter: u64, // ephemeral page counter
  desc: Rc<RefCell<dyn Descriptor>>,
}

impl StorageManager {
  // Returns the next page id.
  //
  // Page ids are always monotonically increasing numbers.
  // They might be reused after a crash but will never conflict with existing page ids.
  pub fn new_page_id(&mut self) -> u64 {
    assert_ne!(self.page_counter, INVALID_PAGE_ID, "INVALID_PAGE_ID");
    let next_id = self.page_counter;
    self.page_counter += 1;
    next_id
  }

  // Writes the data for page id.
  //
  // We don't overwrite the existing pages, so the provided page id must not exist in the
  // page table.
  pub fn write(&mut self, mut page_id: u64, buf: &[u8]) -> Res<()> {
    // We cannot write a page that has been written already
    if let Ok(pos) = self.page_table_lookup(page_id) {
      return Err(err!("Page {} already exists at pos {}", page_id, pos));
    }

    let mut buf_len = 0;
    while buf_len < buf.len() {
      let (pos, mut page) = self.free_list_pop()?;
      self.page_table_insert(page_id, pos)?;
      buf_len += page.write(&buf)?;
      page_id = if buf_len < buf.len() { self.new_page_id() } else { INVALID_PAGE_ID };
      page.cont_page_id = page_id;
      self.pstore(pos, page)?;
    }

    self.sync()
  }

  // Reads stored data for the page id.
  //
  // Page id must have been written prior calling this method.
  pub fn read(&mut self, mut page_id: u64, buf: &mut Vec<u8>) -> Res<()> {
    while page_id != INVALID_PAGE_ID {
      let pos = self.page_table_lookup(page_id)?;
      let page = self.pload(pos)?;
      page.read(buf)?;
      page_id = page.cont_page_id;
    }
    Ok(())
  }

  // Frees the page and its overflow pages.
  pub fn free(&mut self, mut page_id: u64) -> Res<()> {
    while page_id != INVALID_PAGE_ID {
      let pos = self.page_table_lookup(page_id)?;
      let page = self.pload(pos)?;
      self.page_table_delete(page_id)?;
      self.free_list_push(pos)?;
      page_id = page.cont_page_id;
    }
    self.sync()
  }

  // ==========================
  // Positional page operations
  // ==========================

  // Returns a new page and its offset position in the file.
  fn pappend(&mut self) -> Res<(u64, Page)> {
    let buf = Page::empty(self.page_size).into()?;
    let pos = self.desc.borrow().len()?;
    self.desc.borrow_mut().write(pos, &buf[..])?;
    let page = Page::from(buf)?;
    Ok((pos, page))
  }

  // Returns a page at position `pos`.
  fn pload(&mut self, pos: u64) -> Res<Page> {
    let mut buf = vec![0; self.page_size];
    self.desc.borrow_mut().read(pos, &mut buf[..])?;
    Page::from(buf)
  }

  // Returns a page at position `pos`.
  fn pstore(&mut self, pos: u64, page: Page) -> Res<()> {
    let buf = page.into()?;
    self.desc.borrow_mut().write(pos, &buf[..])
  }

  // =====================
  // Page table operations
  // =====================
  // page table:
  //   btree (page id -> pos): gives the ability to check the largest page id
  // free pages:
  //   btree (pos -> n/a), allows to order positions for sequential access

  fn page_table_lookup(&self, page_id: u64) -> Res<u64> {
    unimplemented!()
  }

  fn page_table_insert(&mut self, page_id: u64, pos: u64) -> Res<()> {
    unimplemented!()
  }

  fn page_table_delete(&mut self, page_id: u64) -> Res<()> {
    unimplemented!()
  }

  // ====================
  // Free list operations
  // ====================

  // Free list will give positions in sorted (ascending) order to ensure sequential writes.

  fn free_list_pop(&mut self) -> Res<(u64, Page)> {
    unimplemented!()
  }

  fn free_list_push(&mut self, pos: u64) -> Res<()> {
    unimplemented!()
  }

  // ========================
  // Metadata sync operations
  // ========================

  // Sync metadata + page table + free pages.
  fn sync(&mut self) -> Res<()> {
    // get page 0
    unimplemented!()
  }
}
