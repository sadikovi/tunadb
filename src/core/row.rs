use std::io::Write;

//======
// Rows
//======

const ROW_SERDE_VERSION_1: u8 = 1;

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

// Asserts if the value at the ordinal `i` is not null in a MutableRow.
#[inline]
fn assert_is_not_null(nulls: &[bool], i: usize) {
  assert!(!nulls[i], "Field {} is null", i);
}

// Generic row interface.
// Depending on the implementation, certain methods may not be available.

// Serialised row format:
// [fixed part, nulls (byte-aligned), variable length]
//
// Each field takes 8 bytes in the fixed part and 1 bit in the nulls bitset.
// Variable length is reserved for fields that require byte arrays, e.g. TEXT.
#[derive(Clone, Debug)]
pub enum Row {
  // Read-write row used to manually construct records for writes.
  MutableRow {
    version: u8,
    num_fields: usize,
    is_fixed: Vec<bool>,
    fixed: Vec<u64>,
    nulls: Vec<bool>,
    var: Vec<Vec<u8>>,
  },
  // Buffer row is a read-only row that wraps the raw bytes from BTree.
  BufferRow {
    version: u8,
    num_fields: usize,
    buf: Vec<u8>,
  },
}

impl Row {
  // Creates a new mutable row with the provided number of fields.
  // All values are NULL initially.
  pub fn new(num_fields: usize) -> Self {
    Self::MutableRow {
      version: ROW_SERDE_VERSION_1,
      num_fields: num_fields,
      is_fixed: vec![true; num_fields],
      fixed: vec![0u64; num_fields],
      nulls: vec![true; num_fields], // all fields start as NULL
      var: vec![Vec::new(); num_fields],
    }
  }

  // Creates a new row from the number of fields and the buffer.
  // Buffer content must match the number of fields.
  pub fn from_buf(num_fields: usize, buf: Vec<u8>) -> Self {
    let fixed_len = fixed_part_len(num_fields);
    let nulls_len = nulls_part_len(num_fields);
    assert!(
      buf.len() >= fixed_len + nulls_len + 1 /* version */,
      "The provided row buffer is too short: buf {} < version + fixed {} + nulls {}",
      buf.len(), fixed_len, nulls_len
    );
    let version = buf[buf.len() - 1]; // version is written last
    Self::BufferRow { version, num_fields, buf }
  }

  // Row serialisation version.
  #[inline]
  pub fn version(&self) -> u8 {
    match self {
      Row::MutableRow { version, .. } => *version,
      Row::BufferRow { version, .. } => *version,
    }
  }

  // Returns the number of fields in the row.
  #[inline]
  pub fn num_fields(&self) -> usize {
    match self {
      Row::MutableRow { num_fields, .. } => *num_fields,
      Row::BufferRow { num_fields, .. } => *num_fields,
    }
  }

  // Returns true if the field `i` is null.
  // Depending on the implementation, getter methods below may panic when the field is null.
  // Use this method to check before getter access.
  #[inline]
  pub fn is_null(&self, i: usize) -> bool {
    match self {
      Row::MutableRow { ref nulls, .. } => nulls[i],
      Row::BufferRow { num_fields, ref buf, .. } => {
        let fixed_len = fixed_part_len(*num_fields);
        let nulls_len = nulls_part_len(*num_fields);
        let nulls_buf = &buf[fixed_len..fixed_len + nulls_len];
        get_null_bit(nulls_buf, i)
      },
    }
  }

  // Returns BOOL value for the field `i`.
  #[inline]
  pub fn get_bool(&self, i: usize) -> bool {
    match self {
      Row::MutableRow { ref nulls, ref fixed, .. } => {
        assert_is_not_null(nulls, i);
        fixed[i] != 0
      },
      Row::BufferRow { ref buf, .. } => {
        let slot = get_fixed_slot(buf, i);
        u8_u64!(slot) != 0
      },
    }
  }

  // Returns INT value for the field `i`.
  #[inline]
  pub fn get_i32(&self, i: usize) -> i32 {
    match self {
      Row::MutableRow { ref nulls, ref fixed, .. } => {
        assert_is_not_null(nulls, i);
        fixed[i] as i32
      },
      Row::BufferRow { ref buf, .. } => {
        let slot = get_fixed_slot(buf, i);
        u8_u64!(slot) as i32
      },
    }
  }

  // Returns BIGINT value for the field `i`.
  #[inline]
  pub fn get_i64(&self, i: usize) -> i64 {
    match self {
      Row::MutableRow { ref nulls, ref fixed, .. } => {
        assert_is_not_null(nulls, i);
        fixed[i] as i64
      },
      Row::BufferRow { ref buf, .. } => {
        let slot = get_fixed_slot(buf, i);
        u8_u64!(slot) as i64
      },
    }
  }

  // Returns REAL value for the field `i`.
  #[inline]
  pub fn get_f32(&self, i: usize) -> f32 {
    match self {
      Row::MutableRow { ref nulls, ref fixed, .. } => {
        assert_is_not_null(nulls, i);
        let bytes = u64_u8!(fixed[i]);
        u8_f64!(&bytes) as f32
      },
      Row::BufferRow { ref buf, .. } => {
        let slot = get_fixed_slot(buf, i);
        u8_f64!(slot) as f32
      },
    }
  }

  // Returns DOUBLE value for the field `i`.
  #[inline]
  pub fn get_f64(&self, i: usize) -> f64 {
    match self {
      Row::MutableRow { ref nulls, ref fixed, .. } => {
        assert_is_not_null(nulls, i);
        let bytes = u64_u8!(fixed[i]);
        u8_f64!(bytes)
      },
      Row::BufferRow { ref buf, .. } => {
        let slot = get_fixed_slot(buf, i);
        u8_f64!(slot)
      },
    }
  }

  // Returns TEXT value for the field `i`.
  #[inline]
  pub fn get_str(&self, i: usize) -> &str {
    match self {
      Row::MutableRow { ref nulls, ref var, .. } => {
        assert_is_not_null(nulls, i);
        std::str::from_utf8(&var[i])
          .expect(&format!("Could not read UTF8 string at pos {}", i))
      },
      Row::BufferRow { ref buf, .. } => {
        let slot = get_fixed_slot(buf, i);
        let fixed_part = u8_u64!(slot);
        let off = (fixed_part >> 32) as usize;
        let len = (fixed_part & ((1 << 32) - 1)) as usize;
        std::str::from_utf8(&buf[off..off + len])
          .expect(&format!("Could not read UTF8 string at pos {}", i))
      },
    }
  }

  // Marks field `i` as null, after this call, the value of the field is undefined.
  #[inline]
  pub fn set_null(&mut self, i: usize, is_null: bool) {
    match self {
      Row::MutableRow { ref mut nulls, .. } => nulls[i] = is_null,
      Row::BufferRow { .. } => unimplemented!("BufferRow does not support set_null"),
    }
  }

  // Sets field `i` to the BOOL value.
  #[inline]
  pub fn set_bool(&mut self, i: usize, value: bool) {
    match self {
      Row::MutableRow { ref mut is_fixed, ref mut nulls, ref mut fixed, ref mut var, .. } => {
        if !is_fixed[i] {
          var[i].clear();
          is_fixed[i] = true;
        }
        nulls[i] = false;
        fixed[i] = value as u64;
      },
      Row::BufferRow { .. } => unimplemented!("BufferRow does not support set_bool"),
    }
  }

  // Sets field `i` to the INT value.
  #[inline]
  pub fn set_i32(&mut self, i: usize, value: i32) {
    match self {
      Row::MutableRow { ref mut is_fixed, ref mut nulls, ref mut fixed, ref mut var, .. } => {
        if !is_fixed[i] {
          var[i].clear();
          is_fixed[i] = true;
        }
        nulls[i] = false;
        fixed[i] = value as u64;
      },
      Row::BufferRow { .. } => unimplemented!("BufferRow does not support set_i32"),
    }
  }

  // Sets field `i` to the BIGINT value.
  #[inline]
  pub fn set_i64(&mut self, i: usize, value: i64) {
    match self {
      Row::MutableRow { ref mut is_fixed, ref mut nulls, ref mut fixed, ref mut var, .. } => {
        if !is_fixed[i] {
          var[i].clear();
          is_fixed[i] = true;
        }
        nulls[i] = false;
        fixed[i] = value as u64;
      },
      Row::BufferRow { .. } => unimplemented!("BufferRow does not support set_i64"),
    }
  }

  // Sets field `i` to the REAL value.
  #[inline]
  pub fn set_f32(&mut self, i: usize, value: f32) {
    match self {
      Row::MutableRow { ref mut is_fixed, ref mut nulls, ref mut fixed, ref mut var, .. } => {
        if !is_fixed[i] {
          var[i].clear();
          is_fixed[i] = true;
        }
        nulls[i] = false;
        let val = f64_u8!(value as f64);
        fixed[i] = u8_u64!(val);
      },
      Row::BufferRow { .. } => unimplemented!("BufferRow does not support set_f32"),
    }
  }

  // Sets field `i` to the DOUBLE value.
  #[inline]
  pub fn set_f64(&mut self, i: usize, value: f64) {
    match self {
      Row::MutableRow { ref mut is_fixed, ref mut nulls, ref mut fixed, ref mut var, .. } => {
        if !is_fixed[i] {
          var[i].clear();
          is_fixed[i] = true;
        }
        nulls[i] = false;
        let val = f64_u8!(value);
        fixed[i] = u8_u64!(val);
      },
      Row::BufferRow { .. } => unimplemented!("BufferRow does not support set_f64"),
    }
  }

  // Sets field `i` to the TEXT value.
  #[inline]
  pub fn set_str(&mut self, i: usize, value: &str) {
    match self {
      Row::MutableRow { ref mut is_fixed, ref mut nulls, ref mut var, .. } => {
        is_fixed[i] = false;
        nulls[i] = false;
        var[i].clear();
        var[i].extend_from_slice(value.as_bytes());
      },
      Row::BufferRow { .. } => unimplemented!("BufferRow does not support set_str"),
    }
  }

  // Returns the serialised version of the row.
  #[inline]
  pub fn to_vec(self) -> Vec<u8> {
    match self {
      Row::MutableRow { version, num_fields, ref is_fixed, ref nulls, ref fixed, ref var, .. } => {
        let fixed_len = fixed_part_len(num_fields);
        let nulls_len = nulls_part_len(num_fields);

        let mut buf = vec![0u8; fixed_len + nulls_len];
        for i in 0..num_fields {
          if nulls[i] {
            let nulls_buf = &mut buf[fixed_len..fixed_len + nulls_len];
            set_null_bit(nulls_buf, i, true);
          } else if is_fixed[i] {
            let mut slot = get_fixed_slot_mut(&mut buf, i);
            write_u64!(slot, fixed[i]);
          } else {
            // Write variable length data.
            let off = buf.len() as u64;
            let len = var[i].len() as u64;
            let val = off << 32 | len;
            let mut slot = get_fixed_slot_mut(&mut buf, i);
            write_u64!(slot, val);
            buf.extend_from_slice(&var[i]);
          }
        }
        // Add version.
        buf.push(version);
        buf
      },
      Row::BufferRow { buf, .. } => buf,
    }
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
    let row = Row::new(128);
    assert_eq!(row.num_fields(), 128);

    for i in 0..row.num_fields() {
      assert!(row.is_null(i));
    }
  }

  #[test]
  fn test_row_mutable_version() {
    // All fields must be null.
    let row = Row::new(4);
    assert_eq!(row.version(), ROW_SERDE_VERSION_1);
  }

  #[test]
  fn test_row_mutable_new_zero_fields() {
    let row = Row::new(0);
    assert_eq!(row.num_fields(), 0);
    assert_eq!(row.to_vec(), vec![ROW_SERDE_VERSION_1]);
  }

  #[test]
  fn test_row_mutable_simple_set_get_positive() {
    let mut row = Row::new(6);
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
    let mut row = Row::new(6);
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
    let mut row = Row::new(6);
    row.set_null(0, true);
    assert_eq!(row.is_null(0), true);

    row.set_i32(0, 123);
    assert_eq!(row.is_null(0), false);
    assert_eq!(row.get_i32(0), 123);

    row.set_str(0, "123");
    assert_eq!(row.is_null(0), false);
    assert_eq!(row.get_str(0), "123");
    // Check the variable vector length.
    match row {
      Row::MutableRow { ref var, .. } => assert_eq!(var[0].len(), 3),
      _ => assert!(false, "Expected MutableRow"),
    }

    row.set_i64(0, 234);
    assert_eq!(row.is_null(0), false);
    assert_eq!(row.get_i64(0), 234);
    // Check that the variable vector has been cleared.
    match row {
      Row::MutableRow { ref var, .. } => assert_eq!(var[0].len(), 0),
      _ => assert!(false, "Expected MutableRow"),
    }
  }

  #[test]
  fn test_row_mutable_to_vec() {
    let row = Row::new(3);
    assert_eq!(row.to_vec().len(), 1 /* version */ + fixed_part_len(3) + nulls_part_len(3));

    let mut row = Row::new(3);
    row.set_str(0, "123");
    assert_eq!(row.to_vec().len(), 1 /* version */ + fixed_part_len(3) + nulls_part_len(3) + 3);

    let mut row = Row::new(3);
    row.set_i32(0, 1);
    row.set_i32(1, 2);
    row.set_i32(2, 3);
    row.set_str(0, "123");
    assert_eq!(row.to_vec().len(), 1 /* version */ + fixed_part_len(3) + nulls_part_len(3) + 3);
  }

  #[test]
  #[should_panic(expected = "row buffer is too short")]
  fn test_row_buffer_buf_is_too_short() {
    Row::from_buf(3, Vec::new());
  }

  #[test]
  #[should_panic(expected = "row buffer is too short")]
  fn test_row_buffer_buf_is_too_short_no_version() {
    Row::from_buf(0, Vec::new());
  }

  #[test]
  fn test_row_buffer_version() {
    for num_fields in 0..128 {
      let row = Row::new(num_fields);
      let original_version = row.version();

      let row = Row::from_buf(num_fields, row.to_vec());
      assert_eq!(row.version(), original_version);
    }
  }

  #[test]
  fn test_row_buffer_from_buf_zero_fields() {
    // In this case only version is written.
    let row = Row::from_buf(0, vec![ROW_SERDE_VERSION_1]);
    assert_eq!(row.num_fields(), 0);
    assert_eq!(row.to_vec(), vec![ROW_SERDE_VERSION_1]);
  }

  #[test]
  fn test_row_buffer_from_buf() {
    let mut row = Row::new(7);
    row.set_bool(0, true);
    row.set_i32(1, 1i32);
    row.set_i64(2, 2i64);
    row.set_f32(3, 1.2f32);
    row.set_f64(4, 2.4f64);
    row.set_str(5, "123");
    row.set_null(6, true);

    let row = Row::from_buf(7, row.to_vec());
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
    let mut row = Row::new(5);
    row.set_i32(0, 123);
    row.set_str(3, "123");
    let expected = row.to_vec();

    let row = Row::from_buf(5, expected);
    assert_eq!(
      row.to_vec(),
      vec![
        123, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        3, 0, 0, 0, 41, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        22, 49, 50, 51, 1
      ],
    );
  }
}
