use std::collections::HashMap;
use std::fmt;
use crate::common::error::{Error, Res};
use crate::common::serde::{Reader, SerDe, Writer};
use crate::core::util::to_valid_identifier;

const TYPE_BOOL: u8 = 1;
const TYPE_INT: u8 = 2;
const TYPE_BIGINT: u8 = 3;
const TYPE_FLOAT: u8 = 4;
const TYPE_DOUBLE: u8 = 5;
const TYPE_TEXT: u8 = 6;
const TYPE_STRUCT: u8 = 254;
const TYPE_STRUCT_FIELD: u8 = 255;

// Enum represents column type and/or table schema.
#[derive(Debug, PartialEq)]
pub enum Type {
  BOOL, // bool
  INT, // i32
  BIGINT, // i64
  FLOAT, // f32,
  DOUBLE, // f64
  TEXT, // String
  STRUCT(Fields), // can represent table schema
}

impl Type {
  // Returns true if the type is STRUCT, i.e. can be used as a table schema.
  #[inline]
  pub fn is_struct(&self) -> bool {
    match self {
      Type::STRUCT(_) => true,
      _ => false,
    }
  }

  // Returns the number of fields in the type.
  #[inline]
  pub fn num_fields(&self) -> usize {
    match self {
      Type::STRUCT(ref fields) => fields.get().len(),
      _ => 0,
    }
  }
}

impl SerDe for Type {
  fn serialise(&self, writer: &mut Writer) {
    match self {
      Type::BOOL => writer.write_u8(TYPE_BOOL),
      Type::INT => writer.write_u8(TYPE_INT),
      Type::BIGINT => writer.write_u8(TYPE_BIGINT),
      Type::FLOAT => writer.write_u8(TYPE_FLOAT),
      Type::DOUBLE => writer.write_u8(TYPE_DOUBLE),
      Type::TEXT => writer.write_u8(TYPE_TEXT),
      Type::STRUCT(ref fields) => {
        writer.write_u8(TYPE_STRUCT);
        fields.serialise(writer);
      },
    }
  }

  fn deserialise(reader: &mut Reader) -> Self {
    match reader.read_u8() {
      TYPE_BOOL => Type::BOOL,
      TYPE_INT => Type::INT,
      TYPE_BIGINT => Type::BIGINT,
      TYPE_FLOAT => Type::FLOAT,
      TYPE_DOUBLE => Type::DOUBLE,
      TYPE_TEXT => Type::TEXT,
      TYPE_STRUCT => Type::STRUCT(Fields::deserialise(reader)),
      invalid_tpe => panic!("Unknown type: {}", invalid_tpe),
    }
  }
}

impl fmt::Display for Type {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Type::BOOL => write!(f, "BOOL"),
      Type::INT => write!(f, "INT"),
      Type::BIGINT => write!(f, "BIGINT"),
      Type::FLOAT => write!(f, "FLOAT"),
      Type::DOUBLE => write!(f, "DOUBLE"),
      Type::TEXT => write!(f, "TEXT"),
      Type::STRUCT(ref fields) => write!(f, "STRUCT({})", fields),
    }
  }
}

// Field of a STRUCT.
#[derive(Debug, PartialEq)]
pub struct Field {
  name: String,
  data_type: Type,
  nullable: bool,
}

impl Field {
  // Creates a new Field.
  pub fn new(name: &str, data_type: Type, nullable: bool) -> Res<Self> {
    let name = to_valid_identifier(name)?;
    Ok(Self { name, data_type, nullable })
  }

  // Returns name of the field.
  #[inline]
  pub fn name(&self) -> &str {
    &self.name
  }

  // Returns data type of the field.
  #[inline]
  pub fn data_type(&self) -> &Type {
    &self.data_type
  }

  // Returns true if the field is nullable.
  #[inline]
  pub fn nullable(&self) -> bool {
    self.nullable
  }
}

impl SerDe for Field {
  fn serialise(&self, writer: &mut Writer) {
    writer.write_u8(TYPE_STRUCT_FIELD);
    writer.write_str(&self.name);
    self.data_type.serialise(writer);
    writer.write_bool(self.nullable);
  }

  fn deserialise(reader: &mut Reader) -> Self {
    let tpe = reader.read_u8();
    assert_eq!(
      tpe,
      TYPE_STRUCT_FIELD,
      "Invalid type, expected {}, found {}", TYPE_STRUCT_FIELD, tpe
    );
    let name = reader.read_str().to_string();
    let data_type = Type::deserialise(reader);
    let nullable = reader.read_bool();
    Self { name, data_type, nullable }
  }
}

impl fmt::Display for Field {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if self.nullable {
      write!(f, "{} {} NULL", self.name, self.data_type)
    } else {
      write!(f, "{} {}", self.name, self.data_type)
    }
  }
}

#[derive(Debug, PartialEq)]
pub struct Fields {
  fields: Vec<Field>,
  index: HashMap<String, usize>,
}

impl Fields {
  // Creates a new list of fields.
  pub fn new(fields: Vec<Field>) -> Res<Self> {
    Self::from(fields, false)
  }

  // Constructs `Fields` struct with an optional check on duplicates.
  // The check is disabled when deserialising fields.
  #[inline]
  fn from(fields: Vec<Field>, ignore_duplicates: bool) -> Res<Self> {
    let mut index = HashMap::new();
    for i in 0..fields.len() {
      let field = &fields[i];
      let field_name = field.name.to_string();
      if !index.contains_key(&field_name) {
        index.insert(field_name, i);
      } else if !ignore_duplicates {
        return Err(Error::DuplicateFieldName(field_name))
      }
    }
    Ok(Self { fields, index })
  }

  #[inline]
  pub fn get(&self) -> &[Field] {
    &self.fields
  }

  #[inline]
  pub fn get_field(&self, name: &str) -> Option<&Field> {
    match self.index.get(name) {
      Some(idx) => Some(&self.fields[*idx]),
      None => None,
    }
  }

  #[inline]
  pub fn len(&self) -> usize {
    self.fields.len()
  }
}

impl SerDe for Fields {
  fn serialise(&self, writer: &mut Writer) {
    // We only need to serialise fields, index is reconstructed.
    writer.write_u32(self.fields.len() as u32);
    for field in &self.fields {
      field.serialise(writer);
    }
  }

  fn deserialise(reader: &mut Reader) -> Self {
    let len = reader.read_u32() as usize;
    let mut fields = Vec::with_capacity(len);
    for _ in 0..len {
      fields.push(Field::deserialise(reader));
    }
    match Self::from(fields, true /* ignore_duplicates */) {
      Ok(res) => res,
      // This error should never happen because we always serialise the correct schema.
      Err(err) => unreachable!("Fields deserialisation failed with err {:?}", err),
    }
  }
}

impl fmt::Display for Fields {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "[")?;
    for i in 0..self.fields.len() {
      if i > 0 {
        write!(f, ", ")?;
      }
      write!(f, "{}", &self.fields[i])?;
    }
    write!(f, "]")
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  // Helper method to test serialisation and deserialisation of types.
  fn test_types_convert_roundtrip(tpe: Type) {
    let mut writer = Writer::new();
    tpe.serialise(&mut writer);
    let mut reader = Reader::from_buf(writer.to_vec());
    assert_eq!(Type::deserialise(&mut reader), tpe);
  }

  #[test]
  fn test_types_convert() {
    test_types_convert_roundtrip(Type::BOOL);
    test_types_convert_roundtrip(Type::INT);
    test_types_convert_roundtrip(Type::BIGINT);
    test_types_convert_roundtrip(Type::FLOAT);
    test_types_convert_roundtrip(Type::DOUBLE);
    test_types_convert_roundtrip(Type::TEXT);
    test_types_convert_roundtrip(Type::STRUCT(Fields::new(Vec::new()).unwrap()));

    // Struct type.
    let fields = vec![
      Field::new("f0", Type::BOOL, true).unwrap(),
      Field::new("f1", Type::INT, false).unwrap(),
      Field::new("f2", Type::TEXT, true).unwrap(),
      Field::new("f3", Type::BIGINT, false).unwrap(),
      Field::new("f4", Type::FLOAT, true).unwrap(),
      Field::new("f5", Type::DOUBLE, true).unwrap(),
    ];
    test_types_convert_roundtrip(Type::STRUCT(Fields::new(fields).unwrap()));

    // Nested types.
    let fields = vec![
      Field::new("f1", Type::STRUCT(Fields::new(Vec::new()).unwrap()), true).unwrap(),
      Field::new(
        "f2",
        Type::STRUCT(
          Fields::new(
            vec![
              Field::new("f20", Type::BOOL, true).unwrap(),
              Field::new("f21", Type::INT, false).unwrap(),
              Field::new("f22", Type::TEXT, true).unwrap(),
              Field::new("f23", Type::BIGINT, false).unwrap(),
              Field::new("f24", Type::FLOAT, true).unwrap(),
              Field::new("f25", Type::DOUBLE, false).unwrap(),
            ]
          ).unwrap()
        ),
        true
      ).unwrap(),
    ];
    test_types_convert_roundtrip(Type::STRUCT(Fields::new(fields).unwrap()));
  }

  #[test]
  fn test_types_is_struct() {
    assert_eq!(Type::BOOL.is_struct(), false);
    assert_eq!(Type::INT.is_struct(), false);
    assert_eq!(Type::BIGINT.is_struct(), false);
    assert_eq!(Type::FLOAT.is_struct(), false);
    assert_eq!(Type::DOUBLE.is_struct(), false);
    assert_eq!(Type::TEXT.is_struct(), false);
    assert_eq!(Type::STRUCT(Fields::new(vec![]).unwrap()).is_struct(), true);
  }

  #[test]
  fn test_types_num_fields() {
    assert_eq!(Type::BOOL.num_fields(), 0);
    assert_eq!(Type::INT.num_fields(), 0);
    assert_eq!(Type::BIGINT.num_fields(), 0);
    assert_eq!(Type::FLOAT.num_fields(), 0);
    assert_eq!(Type::DOUBLE.num_fields(), 0);
    assert_eq!(Type::TEXT.num_fields(), 0);
    assert_eq!(Type::STRUCT(Fields::new(vec![]).unwrap()).num_fields(), 0);
    assert_eq!(
      Type::STRUCT(
        Fields::new(
          vec![
            Field::new("a", Type::INT, false).unwrap(),
            Field::new("b", Type::TEXT, false).unwrap(),
          ]
        ).unwrap()
      ).num_fields(),
      2
    );
  }

  #[test]
  fn test_types_field_requires_valid_identifier() {
    assert!(Field::new("a b c", Type::INT, true).is_err());
    assert!(Field::new("123", Type::INT, true).is_err());
    assert!(Field::new("_", Type::INT, true).is_err());
    assert!(Field::new("a+b", Type::INT, true).is_err());
  }

  #[test]
  fn test_types_duplicate_field() {
    let fields = Fields::new(
      vec![
        Field::new("f1", Type::INT, true).unwrap(),
        Field::new("F1", Type::TEXT, false).unwrap(),
      ]
    );
    assert_eq!(fields, Err(Error::DuplicateFieldName("F1".to_string())));
  }

  #[test]
  fn test_types_get_field_by_name() {
    let fields = Fields::new(
      vec![
        Field::new("f1", Type::INT, true).unwrap(),
        Field::new("f2", Type::TEXT, false).unwrap(),
      ]
    ).unwrap();

    assert!(fields.get_field("F1").is_some());
    assert!(fields.get_field("F2").is_some());

    assert!(fields.get_field("f1").is_none());
    assert!(fields.get_field("f2").is_none());
    assert!(fields.get_field("F3").is_none());
  }

  #[test]
  fn test_types_display() {
    assert_eq!(format!("{}", Type::BOOL), "BOOL");
    assert_eq!(format!("{}", Type::INT), "INT");
    assert_eq!(format!("{}", Type::BIGINT), "BIGINT");
    assert_eq!(format!("{}", Type::FLOAT), "FLOAT");
    assert_eq!(format!("{}", Type::DOUBLE), "DOUBLE");
    assert_eq!(format!("{}", Type::TEXT), "TEXT");
    assert_eq!(format!("{}", Type::STRUCT(Fields::new(vec![]).unwrap())), "STRUCT([])");
    assert_eq!(
      format!(
        "{}",
        Type::STRUCT(
          Fields::new(
            vec![
              Field::new("f1", Type::INT, true).unwrap(),
              Field::new("f2", Type::TEXT, false).unwrap(),
              Field::new("f3", Type::STRUCT(Fields::new(vec![]).unwrap()), true).unwrap(),
            ]
          ).unwrap()
        )
      ),
      "STRUCT([F1 INT NULL, F2 TEXT, F3 STRUCT([]) NULL])"
    );
  }
}
