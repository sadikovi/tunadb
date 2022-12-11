use std::io::Write;

//======
// Rows
//======

// Generic row interface.
// Depending on the implementation, certain methods may not be available.

// Serialised row format:
// [fixed part, nulls (byte-aligned), variable length]
//
// Each field takes 8 bytes in the fixed part and 1 bit in the nulls bitset.
// Variable length is reserved for fields that require byte arrays, e.g. TEXT.

pub trait Row {
  // Returns the number of fields in the row.
  fn num_fields(&self) -> usize;
  // Returns true if the field `i` is null.
  // Depending on the implementation, getter methods below may panic when the field is null.
  // Use this method to check before getter access.
  fn is_null(&self, i: usize) -> bool;
  // Returns BOOL value for the field `i`.
  fn get_bool(&self, i: usize) -> bool;
  // Returns INT value for the field `i`.
  fn get_i32(&self, i: usize) -> i32;
  // Returns BIGINT value for the field `i`.
  fn get_i64(&self, i: usize) -> i64;
  // Returns REAL value for the field `i`.
  fn get_f32(&self, i: usize) -> f32;
  // Returns DOUBLE value for the field `i`.
  fn get_f64(&self, i: usize) -> f64;
  // Returns TEXT value for the field `i`.
  fn get_str(&self, i: usize) -> &str;
  // Marks field `i` as null, after this call, the value of the field is undefined.
  fn set_null(&mut self, i: usize, is_null: bool);
  // Sets field `i` to the BOOL value.
  fn set_bool(&mut self, i: usize, value: bool);
  // Sets field `i` to the INT value.
  fn set_i32(&mut self, i: usize, value: i32);
  // Sets field `i` to the BIGINT value.
  fn set_i64(&mut self, i: usize, value: i64);
  // Sets field `i` to the REAL value.
  fn set_f32(&mut self, i: usize, value: f32);
  // Sets field `i` to the DOUBLE value.
  fn set_f64(&mut self, i: usize, value: f64);
  // Sets field `i` to the TEXT value.
  fn set_str(&mut self, i: usize, value: &str);
  // Returns the serialised version of the row.
  fn to_vec(self) -> Vec<u8>;
}

// Length of the fixed slot.
// Each field takes 8 bytes.
const FIXED_FIELD_LEN: usize = 8;

// Calculates byte length of the fixed part of the row.
#[inline]
fn fixed_part_len(num_fields: usize) -> usize {
  num_fields * FIXED_FIELD_LEN
}

// Calculates byte length of the nulls part for the row.
#[inline]
fn nulls_part_len(num_fields: usize) -> usize {
  (num_fields >> 3) + (num_fields & 7 != 0) as usize
}

// Returns fixed slot for the field `i`.
#[inline]
fn get_fixed_slot(buf: &Vec<u8>, i: usize) -> &[u8] {
  let start = FIXED_FIELD_LEN * i;
  &buf[start..start + FIXED_FIELD_LEN]
}

// Returns mutable fixed slot for the field `i`.
#[inline]
fn get_fixed_slot_mut(buf: &mut Vec<u8>, i: usize) -> &mut [u8] {
  let start = FIXED_FIELD_LEN * i;
  &mut buf[start..start + FIXED_FIELD_LEN]
}

// Returns null bit for the field `i`.
// `true` for 1 and `false` for 0.
#[inline]
fn get_null_bit(nulls_buf: &[u8], i: usize) -> bool {
  let byte_pos = i >> 3; // i / 8
  let bit_pos = i & 7; // i % 8
  let value = nulls_buf[byte_pos];
  (value & (1 << bit_pos)) != 0
}

// Sets null bit for the field `i`.
// `true` for 1 and `false` for 0.
// Nulls buffer is a slice into the nulls bytes.
#[inline]
fn set_null_bit(nulls_buf: &mut [u8], i: usize, is_null: bool) {
  let byte_pos = i >> 3; // i / 8
  let bit_pos = i & 7; // i % 8
  // Clear the position.
  nulls_buf[byte_pos] &= !(1 << bit_pos);
  // Set null.
  nulls_buf[byte_pos] |= (is_null as u8) << bit_pos;
}

// Read-write row used to manually construct records for writes.
#[derive(Clone, Debug)]
pub struct MutableRow {
  num_fields: usize,
  is_fixed: Vec<bool>,
  fixed: Vec<u64>,
  nulls: Vec<bool>,
  var: Vec<Vec<u8>>,
}

impl MutableRow {
  // Creates a new mutable row with the provided number of fields.
  // All values are NULL initially.
  pub fn new(num_fields: usize) -> Self {
    Self {
      num_fields: num_fields,
      is_fixed: vec![true; num_fields],
      fixed: vec![0u64; num_fields],
      nulls: vec![true; num_fields], // all fields are null initially
      var: vec![Vec::new(); num_fields],
    }
  }

  // Asserts if the value at the ordinal `i` is not null.
  // Panics if the value is null.
  #[inline]
  fn assert_is_not_null(&self, i: usize) {
    assert!(!self.nulls[i], "Field {} is null", i);
  }
}

impl Row for MutableRow {
  #[inline]
  fn num_fields(&self) -> usize {
    self.num_fields
  }

  #[inline]
  fn is_null(&self, i: usize) -> bool {
    self.nulls[i]
  }

  #[inline]
  fn get_bool(&self, i: usize) -> bool {
    self.assert_is_not_null(i);
    self.fixed[i] != 0
  }

  #[inline]
  fn get_i32(&self, i: usize) -> i32 {
    self.assert_is_not_null(i);
    self.fixed[i] as i32
  }

  #[inline]
  fn get_i64(&self, i: usize) -> i64 {
    self.assert_is_not_null(i);
    self.fixed[i] as i64
  }

  #[inline]
  fn get_f32(&self, i: usize) -> f32 {
    self.assert_is_not_null(i);
    let bytes = u64_u8!(self.fixed[i]);
    u8_f64!(&bytes) as f32
  }

  #[inline]
  fn get_f64(&self, i: usize) -> f64 {
    self.assert_is_not_null(i);
    let bytes = u64_u8!(self.fixed[i]);
    u8_f64!(bytes)
  }

  #[inline]
  fn get_str(&self, i: usize) -> &str {
    self.assert_is_not_null(i);
    std::str::from_utf8(&self.var[i]).expect(&format!("Could not read UTF8 string at pos {}", i))
  }

  #[inline]
  fn set_null(&mut self, i: usize, is_null: bool) {
    self.nulls[i] = is_null;
  }

  #[inline]
  fn set_bool(&mut self, i: usize, value: bool) {
    if !self.is_fixed[i] {
      self.var[i].clear();
      self.is_fixed[i] = true;
    }
    self.nulls[i] = false;
    self.fixed[i] = value as u64;
  }

  #[inline]
  fn set_i32(&mut self, i: usize, value: i32) {
    if !self.is_fixed[i] {
      self.var[i].clear();
      self.is_fixed[i] = true;
    }
    self.nulls[i] = false;
    self.fixed[i] = value as u64;
  }

  #[inline]
  fn set_i64(&mut self, i: usize, value: i64) {
    if !self.is_fixed[i] {
      self.var[i].clear();
      self.is_fixed[i] = true;
    }
    self.nulls[i] = false;
    self.fixed[i] = value as u64;
  }

  #[inline]
  fn set_f32(&mut self, i: usize, value: f32) {
    if !self.is_fixed[i] {
      self.var[i].clear();
      self.is_fixed[i] = true;
    }
    self.nulls[i] = false;
    let val = f64_u8!(value as f64);
    self.fixed[i] = u8_u64!(val);
  }

  #[inline]
  fn set_f64(&mut self, i: usize, value: f64) {
    if !self.is_fixed[i] {
      self.var[i].clear();
      self.is_fixed[i] = true;
    }
    self.nulls[i] = false;
    let val = f64_u8!(value);
    self.fixed[i] = u8_u64!(val);
  }

  #[inline]
  fn set_str(&mut self, i: usize, value: &str) {
    self.is_fixed[i] = false;
    self.nulls[i] = false;
    self.var[i].clear();
    self.var[i].extend_from_slice(value.as_bytes());
  }

  #[inline]
  fn to_vec(self) -> Vec<u8> {
    let fixed_len = fixed_part_len(self.num_fields);
    let nulls_len = nulls_part_len(self.num_fields);

    let mut buf = vec![0u8; fixed_len + nulls_len];
    for i in 0..self.num_fields {
      if self.nulls[i] {
        let nulls_buf = &mut buf[fixed_len..fixed_len + nulls_len];
        set_null_bit(nulls_buf, i, true);
      } else if self.is_fixed[i] {
        let mut slot = get_fixed_slot_mut(&mut buf, i);
        write_u64!(slot, self.fixed[i]);
      } else {
        let off = buf.len() as u64;
        let len = self.var[i].len() as u64;
        let val = off << 32 | len;
        let mut slot = get_fixed_slot_mut(&mut buf, i);
        write_u64!(slot, val);
        buf.extend_from_slice(&self.var[i]);
      }
    }
    buf
  }
}

// Buffer row is a read-only row that wraps the raw bytes from BTree.
#[derive(Clone, Debug)]
pub struct BufferRow {
  num_fields: usize,
  buf: Vec<u8>,
}

impl BufferRow {
  // Creates a new row from number of fields and buffer.
  pub fn from_buf(num_fields: usize, buf: Vec<u8>) -> Self {
    let fixed_len = fixed_part_len(num_fields);
    let nulls_len = nulls_part_len(num_fields);
    assert!(
      buf.len() >= fixed_len + nulls_len,
      "The provided row buffer is too short: buf {} < fixed {} + nulls {}",
      buf.len(), fixed_len, nulls_len
    );
    Self { num_fields, buf }
  }
}

impl Row for BufferRow {
  #[inline]
  fn num_fields(&self) -> usize {
    self.num_fields
  }

  #[inline]
  fn is_null(&self, i: usize) -> bool {
    let fixed_len = fixed_part_len(self.num_fields);
    let nulls_len = nulls_part_len(self.num_fields);
    let nulls_buf = &self.buf[fixed_len..fixed_len + nulls_len];
    get_null_bit(nulls_buf, i)
  }

  #[inline]
  fn get_bool(&self, i: usize) -> bool {
    let slot = get_fixed_slot(&self.buf, i);
    u8_u64!(slot) != 0
  }

  #[inline]
  fn get_i32(&self, i: usize) -> i32 {
    let slot = get_fixed_slot(&self.buf, i);
    u8_u64!(slot) as i32
  }

  #[inline]
  fn get_i64(&self, i: usize) -> i64 {
    let slot = get_fixed_slot(&self.buf, i);
    u8_u64!(slot) as i64
  }

  #[inline]
  fn get_f32(&self, i: usize) -> f32 {
    let slot = get_fixed_slot(&self.buf, i);
    u8_f64!(slot) as f32
  }

  #[inline]
  fn get_f64(&self, i: usize) -> f64 {
    let slot = get_fixed_slot(&self.buf, i);
    u8_f64!(slot)
  }

  fn get_str(&self, i: usize) -> &str {
    let slot = get_fixed_slot(&self.buf, i);
    let fixed_part = u8_u64!(slot);
    let off = (fixed_part >> 32) as usize;
    let len = (fixed_part & ((1 << 32) - 1)) as usize;
    std::str::from_utf8(&self.buf[off..off + len])
      .expect(&format!("Could not read UTF8 string at pos {}", i))
  }

  #[inline]
  fn set_null(&mut self, _i: usize, _is_null: bool) {
    unimplemented!("BufferRow does not support set_null");
  }

  #[inline]
  fn set_bool(&mut self, _i: usize, _value: bool) {
    unimplemented!("BufferRow does not support set_bool");
  }

  #[inline]
  fn set_i32(&mut self, _i: usize, _value: i32) {
    unimplemented!("BufferRow does not support set_i32");
  }

  #[inline]
  fn set_i64(&mut self, _i: usize, _value: i64) {
    unimplemented!("BufferRow does not support set_i64");
  }

  #[inline]
  fn set_f32(&mut self, _i: usize, _value: f32) {
    unimplemented!("BufferRow does not support set_f32");
  }

  #[inline]
  fn set_f64(&mut self, _i: usize, _value: f64) {
    unimplemented!("BufferRow does not support set_f64");
  }

  #[inline]
  fn set_str(&mut self, _i: usize, _value: &str) {
    unimplemented!("BufferRow does not support set_str");
  }

  #[inline]
  fn to_vec(self) -> Vec<u8> {
    self.buf
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_row_fixed_part_len() {
    assert_eq!(fixed_part_len(0), 0);
    assert_eq!(fixed_part_len(1), FIXED_FIELD_LEN);
    assert_eq!(fixed_part_len(2), 2 * FIXED_FIELD_LEN);
    assert_eq!(fixed_part_len(128), 128 * FIXED_FIELD_LEN);
  }

  #[test]
  fn test_row_nulls_part_len() {
    assert_eq!(nulls_part_len(0), 0);
    for num_fields in 1..1000 {
      let mut num_bytes = num_fields / 8;
      if num_fields % 8 != 0 {
        num_bytes += 1;
      }
      assert_eq!(nulls_part_len(num_fields), num_bytes);
    }
  }

  #[test]
  fn test_row_mutable_new() {
    // All fields must be null.
    let row = MutableRow::new(128);
    assert_eq!(row.num_fields(), 128);

    for i in 0..row.num_fields() {
      assert!(row.is_null(i));
    }
  }

  #[test]
  fn test_row_mutable_new_zero_fields() {
    let row = MutableRow::new(0);
    assert_eq!(row.num_fields(), 0);
    assert_eq!(row.to_vec(), Vec::new());
  }

  #[test]
  fn test_row_mutable_simple_set_get_positive() {
    let mut row = MutableRow::new(6);
    row.set_bool(0, true);
    row.set_i32(1, 1i32);
    row.set_i64(2, 2i64);
    row.set_f32(3, 1.2f32);
    row.set_f64(4, 2.4f64);
    row.set_str(5, "test");

    assert_eq!(row.get_bool(0), true);
    assert_eq!(row.get_i32(1), 1i32);
    assert_eq!(row.get_i64(2), 2i64);
    assert_eq!(row.get_f32(3), 1.2f32);
    assert_eq!(row.get_f64(4), 2.4f64);
    assert_eq!(row.get_str(5), "test");
  }

  #[test]
  fn test_row_mutable_simple_set_get_negative() {
    let mut row = MutableRow::new(6);
    row.set_bool(0, false);
    row.set_i32(1, -1i32);
    row.set_i64(2, -2i64);
    row.set_f32(3, -1.2f32);
    row.set_f64(4, -2.4f64);
    row.set_str(5, "");

    assert_eq!(row.get_bool(0), false);
    assert_eq!(row.get_i32(1), -1i32);
    assert_eq!(row.get_i64(2), -2i64);
    assert_eq!(row.get_f32(3), -1.2f32);
    assert_eq!(row.get_f64(4), -2.4f64);
    assert_eq!(row.get_str(5), "");
  }

  #[test]
  fn test_row_mutable_override_values() {
    let mut row = MutableRow::new(6);
    row.set_null(0, true);
    assert_eq!(row.is_null(0), true);

    row.set_i32(0, 123);
    assert_eq!(row.is_null(0), false);
    assert_eq!(row.get_i32(0), 123);

    row.set_str(0, "123");
    assert_eq!(row.is_null(0), false);
    assert_eq!(row.get_str(0), "123");
    // Check the variable vector length.
    assert_eq!(row.var[0].len(), 3);

    row.set_i64(0, 234);
    assert_eq!(row.is_null(0), false);
    assert_eq!(row.get_i64(0), 234);
    // Check that the variable vector has been cleared.
    assert_eq!(row.var[0].len(), 0);
  }

  #[test]
  fn test_row_mutable_to_vec() {
    let row = MutableRow::new(3);
    assert_eq!(row.to_vec().len(), fixed_part_len(3) + nulls_part_len(3));

    let mut row = MutableRow::new(3);
    row.set_str(0, "123");
    assert_eq!(row.to_vec().len(), fixed_part_len(3) + nulls_part_len(3) + 3);

    let mut row = MutableRow::new(3);
    row.set_i32(0, 1);
    row.set_i32(1, 2);
    row.set_i32(2, 3);
    row.set_str(0, "123");
    assert_eq!(row.to_vec().len(), fixed_part_len(3) + nulls_part_len(3) + 3);
  }

  #[test]
  #[should_panic(expected = "row buffer is too short")]
  fn test_row_buffer_buf_is_too_short() {
    BufferRow::from_buf(3, Vec::new());
  }

  #[test]
  fn test_row_buffer_from_buf_zero_fields() {
    let row = BufferRow::from_buf(0, Vec::new());
    assert_eq!(row.num_fields(), 0);
    assert_eq!(row.to_vec(), Vec::new());
  }

  #[test]
  fn test_row_buffer_from_buf() {
    let mut row = MutableRow::new(7);
    row.set_bool(0, true);
    row.set_i32(1, 1i32);
    row.set_i64(2, 2i64);
    row.set_f32(3, 1.2f32);
    row.set_f64(4, 2.4f64);
    row.set_str(5, "123");
    row.set_null(6, true);

    let row = BufferRow::from_buf(7, row.to_vec());
    assert_eq!(row.num_fields(), 7);

    assert_eq!(row.is_null(0), false);
    assert_eq!(row.is_null(1), false);
    assert_eq!(row.is_null(2), false);
    assert_eq!(row.is_null(3), false);
    assert_eq!(row.is_null(4), false);
    assert_eq!(row.is_null(5), false);
    assert_eq!(row.is_null(6), true);

    assert_eq!(row.get_bool(0), true);
    assert_eq!(row.get_i32(1), 1);
    assert_eq!(row.get_i64(2), 2);
    assert_eq!(row.get_f32(3), 1.2);
    assert_eq!(row.get_f64(4), 2.4);
    assert_eq!(row.get_str(5), "123");
  }

  #[test]
  fn test_row_buffer_to_vec() {
    let mut row = MutableRow::new(10);
    row.set_str(5, "123");
    let expected = row.to_vec();

    let row = BufferRow::from_buf(10, expected.clone());
    assert_eq!(row.to_vec(), expected);
  }
}
