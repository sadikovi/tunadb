// =========
// Versions
// =========

pub const DB_VERSION: &str = env!("CARGO_PKG_VERSION"); // extracted from Cargo.toml

//======
// Misc
//======

// Macro to render binary data as hex.
macro_rules! hex {
  ($slice:expr) => {{
    $slice.iter().map(|x| format!("{:02x}", x)).collect::<Vec<String>>().join("")
  }}
}

//==============
// Error macros
//==============

macro_rules! internal_err {
  ($fmt:expr) =>
    (crate::common::error::Error::InternalError($fmt.to_owned()));
  ($fmt:expr, $($args:expr),*) =>
    (crate::common::error::Error::InternalError(format!($fmt, $($args),*)));
}


macro_rules! already_exists_err {
  ($fmt:expr) =>
    (crate::common::error::Error::InternalAlreadyExists($fmt.to_owned()));
  ($fmt:expr, $($args:expr),*) =>
    (crate::common::error::Error::InternalAlreadyExists(format!($fmt, $($args),*)));
}


macro_rules! res {
  ($e:expr) => ($e.unwrap());
  ($e:expr, $fmt:expr) => ($e.expect(&format!($fmt)));
  ($e:expr, $fmt:expr, $($args:expr),*) => ($e.expect(&format!($fmt, $($args),*)));
}

//=============
// Conversions
//=============

// Converts byte slice into u32 (little endian).

macro_rules! u8_u32 {
  ($buf:expr) => {
    u32::from_le_bytes([$buf[0], $buf[1], $buf[2], $buf[3]])
  };
}

// Converts u32 to byte array (little endian).

macro_rules! u32_u8 {
  ($num:expr) => {{
    let arr: [u8; 4] = $num.to_le_bytes();
    arr
  }};
}

// Converts byte slice into u64 (little endian).

macro_rules! u8_u64 {
  ($buf:expr) => {
    u64::from_le_bytes([$buf[0], $buf[1], $buf[2], $buf[3], $buf[4], $buf[5], $buf[6], $buf[7]])
  };
}

// Converts u64 to byte array (little endian).

macro_rules! u64_u8 {
  ($num:expr) => {{
    let arr: [u8; 8] = $num.to_le_bytes();
    arr
  }};
}

// Converts byte slice into f64 (little endian).

macro_rules! u8_f64 {
  ($buf:expr) => {
    f64::from_le_bytes([$buf[0], $buf[1], $buf[2], $buf[3], $buf[4], $buf[5], $buf[6], $buf[7]])
  };
}

// Converts f64 to byte array (little endian).

macro_rules! f64_u8 {
  ($num:expr) => {{
    let arr: [u8; 8] = $num.to_le_bytes();
    arr
  }};
}

// Writes u32 into a slice.

macro_rules! write_u32 {
  ($slice:expr, $num:expr) => {{
    res!(($slice).write(&u32_u8!($num)));
  }}
}

// Writes u64 into a slice.

macro_rules! write_u64 {
  ($slice:expr, $num:expr) => {{
    res!(($slice).write(&u64_u8!($num)));
  }}
}

// Writes byte array into a slice.

macro_rules! write_bytes {
  ($slice:expr, $data:expr) => {{
    res!(($slice).write($data));
  }}
}

pub mod error;
pub mod lru;
pub mod row;
pub mod serde;
pub mod trees;
