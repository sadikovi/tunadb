use crate::common::error::{Error, Res};

// Returns a valid identifier that is used throughout the database.
// The identifier conforms to [A-Za-z][A-Za-z0-9_] pattern.
#[inline]
pub fn to_valid_identifier(name: &str) -> Res<String> {
  if name.len() == 0 {
    return Err(Error::InvalidIdentifier(format!("Empty identifier")));
  } else if name.len() > 128 {
    return Err(Error::InvalidIdentifier(format!("Identifier is too long ({})", name.len())));
  }

  let arr = name.as_bytes();
  for &b in arr {
    let is_valid =
      b >= b'0' && b <= b'9' ||
      b >= b'A' && b <= b'Z' ||
      b == b'_' ||
      b >= b'a' && b <= b'z';

    if !is_valid {
      return Err(Error::InvalidIdentifier(format!("Identifier {} contains illegal characters", name)));
    }
  }

  let starts_with_letter =
    arr[0] >= b'A' && arr[0] <= b'Z' ||
    arr[0] >= b'a' && arr[0] <= b'z';

  if !starts_with_letter {
    return Err(Error::InvalidIdentifier(format!("Identifier {} must start with a letter", name)));
  }

  Ok(name.to_uppercase())
}

#[cfg(test)]
pub mod tests {
  use super::*;

  #[test]
  fn test_catalog_to_valid_identifier() {
    // Invalid values.
    assert!(to_valid_identifier("").is_err());
    assert!(to_valid_identifier("_").is_err());
    assert!(to_valid_identifier("01234").is_err());
    assert!(to_valid_identifier("abc def").is_err());
    assert!(to_valid_identifier("ABC DEF").is_err());
    assert!(to_valid_identifier("_123").is_err());
    assert!(to_valid_identifier("_abc").is_err());
    assert!(to_valid_identifier("1abc").is_err());
    assert!(to_valid_identifier(" abc").is_err());
    assert!(to_valid_identifier(&"a".repeat(129)).is_err());

    // Valid values.
    assert_eq!(to_valid_identifier("summary"), Ok("SUMMARY".to_owned()));
    assert_eq!(to_valid_identifier("s123456"), Ok("S123456".to_owned()));
    assert_eq!(to_valid_identifier("s1_2_3_4"), Ok("S1_2_3_4".to_owned()));
    assert_eq!(to_valid_identifier("aBcDeF_123"), Ok("ABCDEF_123".to_owned()));
    assert_eq!(to_valid_identifier("s"), Ok("S".to_owned()));
    assert!(to_valid_identifier(&"a".repeat(128)).is_ok());
  }
}
