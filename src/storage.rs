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
      return Err(err!("Cannot truncate to len {}, current len {}", len, curr_len));
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
      return Err(err!("Cannot truncate to len {}, current len {}", len, curr_len));
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

const NULL: u64 = u64::MAX;
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
    Self { len: 0, cont_page_id: NULL, data: vec![0; page_size] }
  }

  // Resets the page as empty.
  fn reset(&mut self) {
    self.len = 0;
    self.cont_page_id = NULL;
  }

  fn offset(&self) -> usize {
    PAGE_META_LEN + self.len
  }

  fn capacity(&self) -> usize {
    self.data.len() - self.offset()
  }

  fn data(&self) -> &[u8] {
    &self.data[PAGE_META_LEN..PAGE_META_LEN + self.len]
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
    buf.extend(self.data());
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
  free_ptr: u64, // pointer to the free list, represents the absolute position of a page
  free_count: usize, // number of pages in the free list
  free_map: BTreeMap<u64, u64>, // in-memory BTree to return pages in sequential order
  page_dir: btree::BTree, // page directory
  page_dir_size: usize, // number of page ids in the page directory
}

impl StorageManager {
  // Returns the next page id.
  //
  // Page ids are always monotonically increasing numbers.
  // They might be reused after a crash but will never conflict with existing page ids.
  pub fn new_page_id(&mut self) -> u64 {
    assert_ne!(self.page_counter, NULL, "Page counter is NULL");
    let next_id = self.page_counter;
    self.page_counter += 1;
    next_id
  }

  // Writes the data for page id.
  //
  // Writes are performed with overflow pages if `buf.len()` exceeds the page size.
  // We don't overwrite the existing pages, so the provided page id must not exist in the
  // page table.
  pub fn write(&mut self, mut page_id: u64, buf: &[u8]) -> Res<()> {
    // We cannot write a page that has been written already
    if let Ok(pos) = self.page_dir_lookup(page_id) {
      return Err(err!("Page {} already exists at pos {}", page_id, pos));
    }

    let mut buf_len = 0;
    while buf_len < buf.len() {
      let (pos, mut page) = self.free_list_pop()?;
      self.page_dir_insert(page_id, pos)?;
      buf_len += page.write(&buf)?;
      page_id = if buf_len < buf.len() { self.new_page_id() } else { NULL };
      page.cont_page_id = page_id;
      self.pstore(pos, page)?;
    }

    self.sync()
  }

  // Reads stored data for the page id.
  //
  // All overflow pages that are linked to the page with `page_id` will be read to reconstruct
  // the original data.
  // Page id must exist prior calling this method.
  pub fn read(&mut self, mut page_id: u64, buf: &mut Vec<u8>) -> Res<()> {
    while page_id != NULL {
      let pos = self.page_dir_lookup(page_id)?;
      let page = self.pload(pos)?;
      page.read(buf)?;
      page_id = page.cont_page_id;
    }
    Ok(())
  }

  // Frees the page and its overflow pages if exist.
  //
  // Page id must exist prior calling this method.
  pub fn free(&mut self, mut page_id: u64) -> Res<()> {
    while page_id != NULL {
      let pos = self.page_dir_lookup(page_id)?;
      let page = self.pload(pos)?;
      self.page_dir_delete(page_id)?;
      page_id = page.cont_page_id;
      self.free_list_push(pos, page)?;
    }
    self.sync()
  }

  // ==================
  // Storage statistics
  // ==================

  pub fn page_size(&self) -> usize {
    self.page_size
  }

  pub fn num_total_pages(&self) -> Res<usize> {
    Ok(self.desc.borrow().len()? as usize / self.page_size)
  }

  pub fn num_free_pages(&self) -> Res<usize> {
    Ok(self.free_count)
  }

  pub fn num_used_pages(&self) -> Res<usize> {
    Ok(self.page_dir_size)
  }

  // The amount of memory (in bytes) used by the storage manager.
  pub fn mem_usage(&self) -> Res<usize> {
    Ok(self.desc.borrow().mem_usage()? + self.free_map.len() * (8 /* key */ + 8 /* value */))
  }

  // ==========================
  // Positional page operations
  // ==========================

  // Returns a new page and its offset position in the file.
  fn pappend(&mut self) -> Res<(u64, Page)> {
    let page = Page::empty(self.page_size);
    let pos = self.desc.borrow().len()?;
    self.desc.borrow_mut().write(pos, page.data())?;
    Ok((pos, page))
  }

  // Returns a page at position `pos`.
  fn pload(&mut self, pos: u64) -> Res<Page> {
    let mut buf = vec![0; self.page_size];
    self.desc.borrow_mut().read(pos, &mut buf[..])?;
    Page::from(buf)
  }

  // Stores the page at position `pos`.
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

  fn page_dir_lookup(&self, page_id: u64) -> Res<u64> {
    match btree::get(&self.page_dir, &page_id.to_le_bytes())? {
      Some(value) => Ok(u64_le!(&value[..])),
      None => Err(err!("Page {} is not found", page_id))
    }
  }

  fn page_dir_insert(&mut self, page_id: u64, pos: u64) -> Res<()> {
    if let Some(_) = btree::get(&self.page_dir, &page_id.to_le_bytes())? {
      return Err(err!("Page {} already exists, page overwrite is not allowed", page_id));
    }
    self.page_dir = btree::put(&self.page_dir, &page_id.to_le_bytes(), &pos.to_le_bytes())?;
    self.page_dir_size += 1;
    Ok(())
  }

  fn page_dir_delete(&mut self, page_id: u64) -> Res<()> {
    if let None = btree::get(&self.page_dir, &page_id.to_le_bytes())? {
      return Err(err!("Page {} does not exist, no-op delete is not allowed", page_id));
    }
    self.page_dir = btree::del(&self.page_dir, &page_id.to_le_bytes())?;
    self.page_dir_size -= 1;
    Ok(())
  }

  // ====================
  // Free list operations
  // ====================

  // Free list will give positions in sorted (ascending) order to ensure sequential writes.

  // Returns the next free page to use and its position.
  fn free_list_pop(&mut self) -> Res<(u64, Page)> {
    if self.free_ptr == NULL {
      self.pappend()
    } else {
      // Next position for sequential access
      let (&pos, &parent_pos) = self.free_map.first_key_value().unwrap(); // guaranteed to exist
      // Load pages and update pointers
      let mut page = self.pload(pos)?;
      let next_pos = u64_le!(&page.data()[0..8]);

      if pos == self.free_ptr {
        // Remove the head of the list
        self.free_map.remove(&pos);
        if next_pos != NULL {
          self.free_map.insert(next_pos, NULL); // previously pointed to `pos`
        }
        self.free_ptr = next_pos;
      } else {
        let mut parent = self.pload(parent_pos)?;
        parent.reset();
        parent.write(&next_pos.to_le_bytes())?;
        self.pstore(parent_pos, parent)?;
        self.free_map.remove(&pos);
        self.free_map.insert(next_pos, parent_pos);
      }
      page.reset();
      self.free_count -= 1;

      Ok((pos, page))
    }
  }

  // Stores the page and its corresponding position in the free list.
  fn free_list_push(&mut self, pos: u64, mut page: Page) -> Res<()> {
    page.reset();
    page.write(&self.free_ptr.to_le_bytes())?;
    self.pstore(pos, page)?;
    // Update free map
    if self.free_ptr != NULL {
      self.free_map.insert(self.free_ptr, pos);
    }
    self.free_map.insert(pos, NULL); // head of the list
    // Update the pointer
    self.free_ptr = pos;
    self.free_count += 1;

    // self.op_truncate()
    Ok(())
  }

  // Truncates the underlying descriptor depending on the positions in the free list.
  fn op_truncate(&mut self) -> Res<()> {
    let mut desc_len = self.desc.borrow().len()?;
    let mut stack: Vec<(u64, u64)> = Vec::new();
    while let Some((pos, parent_pos)) = self.free_map.pop_last() {
      assert!(pos < desc_len, "unexpected pos {} >= desc length {}", pos, desc_len);
      if pos + self.page_size as u64 >= desc_len {
        // We can truncate the descriptor.
        stack.push((pos, parent_pos));
        desc_len = pos;
      } else {
        self.free_map.insert(pos, parent_pos);
        break;
      }
    }

    // We have collected at least one position to remove.
    let do_truncate = stack.len() > 0;

    while let Some((pos, parent_pos)) = stack.pop() {
      // Load pages and update pointers
      let page = self.pload(pos)?;
      let next_pos = u64_le!(&page.data()[0..8]);
      if pos == self.free_ptr {
        // Remove the head of the list
        self.free_ptr = next_pos;
        self.free_map.remove(&pos);
        self.free_map.insert(next_pos, NULL);
      } else {
        let mut parent = self.pload(parent_pos)?;
        parent.reset();
        parent.write(&next_pos.to_le_bytes())?;
        self.pstore(parent_pos, parent)?;
        self.free_map.remove(&pos);
        self.free_map.insert(next_pos, parent_pos);
      }
      self.free_count -= 1;
    }


    if do_truncate {
      self.desc.borrow_mut().truncate(desc_len)?;
    }

    Ok(())
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
