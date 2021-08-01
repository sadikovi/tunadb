// Converts byte slice into u32 little endian
macro_rules! u32_le {
  ($buf:expr) => {
    u32::from_le_bytes([$buf[0], $buf[1], $buf[2], $buf[3]])
  };
}

// Converts byte slice into u64 little endian
macro_rules! u64_le {
  ($buf:expr) => {
    u64::from_le_bytes([$buf[0], $buf[1], $buf[2], $buf[3], $buf[4], $buf[5], $buf[6], $buf[7]])
  };
}
