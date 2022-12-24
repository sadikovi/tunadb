// SerDe version, this should be updated whenever changes are made to the serialisation protocol.
pub const SERDE_VERSION_1: u8 = 1;

// Trait to serialise structs except `Row`s as they have their own serialisation logic.
pub trait SerDe {
  // Serialises data using writer.
  fn serialise(&self, writer: &mut Writer);
  // Deserialises data using reader, returns a new instance of Self.
  fn deserialise(reader: &mut Reader) -> Self;
}

// Writer that is a wrapper on the vector of bytes.
pub struct Writer {
  buf: Vec<u8>,
}

impl Writer {
  // Creates a new writer with an empty buffer.
  pub fn new() -> Self {
    Self { buf: Vec::new() }
  }

  // Ensures that the version is added at the beginning.
  #[inline]
  fn ensure_version(&mut self) {
    if self.buf.len() == 0 {
      self.buf.extend_from_slice(&[SERDE_VERSION_1]);
    }
  }

  // Writes u8 value to the buffer.
  #[inline]
  pub fn write_u8(&mut self, value: u8) {
    self.ensure_version();
    self.buf.push(value);
  }

  // Writes bool value to the buffer.
  #[inline]
  pub fn write_bool(&mut self, value: bool) {
    self.write_u8(value as u8);
  }

  // Writes u32 value to the buffer.
  #[inline]
  pub fn write_u32(&mut self, value: u32) {
    self.ensure_version();
    let bytes = u32_u8!(value);
    self.buf.extend_from_slice(&bytes);
  }

  // Writes u64 value to the buffer.
  #[inline]
  pub fn write_u64(&mut self, value: u64) {
    self.ensure_version();
    let bytes = u64_u8!(value);
    self.buf.extend_from_slice(&bytes);
  }

  // Writes an arbitrary sequence of bytes to the buffer.
  // This method writes length (4 bytes) followed by the content.
  #[inline]
  pub fn write_bytes(&mut self, value: &[u8]) {
    self.ensure_version();
    // Write length as 4 bytes.
    self.buf.extend_from_slice(&u32_u8!(value.len() as u32));
    self.buf.extend_from_slice(value);
  }

  // Writes string into the buffer.
  #[inline]
  pub fn write_str(&mut self, value: &str) {
    self.write_bytes(value.as_bytes());
  }

  // Returns the serialised vector of bytes.
  #[inline]
  pub fn to_vec(mut self) -> Vec<u8> {
    self.ensure_version();
    self.buf
  }
}

// Reader, used to reconstruct the object from the serialised data.
pub struct Reader {
  buf: Vec<u8>,
  off: usize, // current offset
  version: u8, // version of the serialised buffer
}

impl Reader {
  // Creates a new reader.
  pub fn from_buf(buf: Vec<u8>) -> Self {
    assert!(buf.len() > 0, "Expected non-empty buffer");
    let version = buf[0];
    let off = 1;
    Self { buf, off, version }
  }

  // Returns the version of the serialised buffer.
  #[inline]
  pub fn version(&self) -> u8 {
    self.version
  }

  // Returns u8 value.
  #[inline]
  pub fn read_u8(&mut self) -> u8 {
    let value = self.buf[self.off];
    self.off += 1;
    value
  }

  // Returns bool value.
  #[inline]
  pub fn read_bool(&mut self) -> bool {
    self.read_u8() != 0
  }

  // Returns u32 value.
  #[inline]
  pub fn read_u32(&mut self) -> u32 {
    let value = u8_u32!(&self.buf[self.off..self.off + 4]);
    self.off += 4;
    value
  }

  // Returns u64 value.
  #[inline]
  pub fn read_u64(&mut self) -> u64 {
    let value = u8_u64!(&self.buf[self.off..self.off + 8]);
    self.off += 8;
    value
  }

  // Returns the u8 slice.
  #[inline]
  pub fn read_bytes(&mut self) -> &[u8] {
    let len = u8_u32!(self.buf[self.off..self.off + 4]) as usize;
    let off = self.off + 4;
    self.off += 4 + len;
    &self.buf[off..off + len]
  }

  // Returns str reference.
  #[inline]
  pub fn read_str(&mut self) -> &str {
    let bytes = self.read_bytes();
    std::str::from_utf8(bytes).expect("Valid UTF8 string")
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_serde_writer_new() {
    let writer = Writer::new();
    assert_eq!(writer.buf.len(), 0)
  }

  #[test]
  fn test_serde_writer_ensure_version_idempotent() {
    let mut writer = Writer::new();
    for _ in 0..10 {
      writer.ensure_version();
      assert_eq!(writer.buf, vec![SERDE_VERSION_1]);
    }
  }

  #[test]
  fn test_serde_writer_write_check_bytes() {
    let mut writer = Writer::new();
    writer.write_u8(2);
    assert_eq!(writer.to_vec(), vec![SERDE_VERSION_1, 2]);

    let mut writer = Writer::new();
    writer.write_bool(true);
    assert_eq!(writer.to_vec(), vec![SERDE_VERSION_1, 1]);

    let mut writer = Writer::new();
    writer.write_u32(123);
    assert_eq!(writer.to_vec(), vec![SERDE_VERSION_1, 123, 0, 0, 0]);

    let mut writer = Writer::new();
    writer.write_u64(123);
    assert_eq!(writer.to_vec(), vec![SERDE_VERSION_1, 123, 0, 0, 0, 0, 0, 0, 0]);

    let mut writer = Writer::new();
    writer.write_u64(123);
    assert_eq!(writer.to_vec(), vec![SERDE_VERSION_1, 123, 0, 0, 0, 0, 0, 0, 0]);

    let mut writer = Writer::new();
    writer.write_bytes(&[1, 2, 3, 4]);
    assert_eq!(writer.to_vec(), vec![SERDE_VERSION_1, 4, 0, 0, 0, 1, 2, 3, 4]);

    let mut writer = Writer::new();
    writer.write_str("ABC");
    assert_eq!(writer.to_vec(), vec![SERDE_VERSION_1, 3, 0, 0, 0, 65, 66, 67]);
  }

  #[test]
  fn test_serde_writer_to_vec_empty() {
    let writer = Writer::new();
    assert_eq!(writer.to_vec(), vec![SERDE_VERSION_1]);
  }

  #[test]
  fn test_serde_writer_to_vec() {
    let mut writer = Writer::new();
    writer.write_bool(false);
    writer.write_bool(true);
    writer.write_u32(2);
    writer.write_str("ABC");
    assert_eq!(writer.to_vec(), vec![SERDE_VERSION_1, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0, 65, 66, 67]);
  }

  #[test]
  #[should_panic(expected = "Expected non-empty buffer")]
  fn test_serde_reader_from_buf_empty_buf() {
    Reader::from_buf(Vec::new());
  }

  #[test]
  fn test_serde_reader_from_buf_empty_writer() {
    let writer = Writer::new();
    let reader = Reader::from_buf(writer.to_vec());
    assert_eq!(reader.version(), SERDE_VERSION_1);
  }

  #[test]
  fn test_serde_reader_from_buf() {
    let mut writer = Writer::new();
    writer.write_u32(123);

    let reader = Reader::from_buf(writer.to_vec());
    assert_eq!(reader.version(), SERDE_VERSION_1);
  }

  #[test]
  fn test_serde_reader_read_values() {
    let mut writer = Writer::new();
    writer.write_bool(true);
    writer.write_bool(false);
    writer.write_u8(1);
    writer.write_u32(2);
    writer.write_u64(3);
    writer.write_bytes(&[1, 2, 3, 4, 5]);
    writer.write_str("ABCD");

    let mut reader = Reader::from_buf(writer.to_vec());
    assert_eq!(reader.version(), SERDE_VERSION_1);
    assert_eq!(reader.read_bool(), true);
    assert_eq!(reader.read_bool(), false);
    assert_eq!(reader.read_u8(), 1);
    assert_eq!(reader.read_u32(), 2);
    assert_eq!(reader.read_u64(), 3);
    assert_eq!(reader.read_bytes(), &[1, 2, 3, 4, 5]);
    assert_eq!(reader.read_str(), "ABCD");

    assert_eq!(reader.off, reader.buf.len());
  }
}
