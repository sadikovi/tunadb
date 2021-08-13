// Converts byte slice into u32 (little endian)
macro_rules! u8_u32 {
  ($buf:expr) => {
    u32::from_le_bytes([$buf[0], $buf[1], $buf[2], $buf[3]])
  };
}

// Converts u32 to byte array (little endian)
macro_rules! u32_u8 {
  ($num:expr) => {{
    let arr: [u8; 4] = $num.to_le_bytes();
    arr
  }};
}

// Converts byte slice into u64 (little endian)
macro_rules! u8_u64 {
  ($buf:expr) => {
    u64::from_le_bytes([$buf[0], $buf[1], $buf[2], $buf[3], $buf[4], $buf[5], $buf[6], $buf[7]])
  };
}

// Converts u32 to byte array (little endian)
macro_rules! u64_u8 {
  ($num:expr) => {{
    let arr: [u8; 8] = $num.to_le_bytes();
    arr
  }};
}
