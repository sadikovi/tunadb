use std::collections::HashMap;
use crate::common::error::{Error, Res};
use crate::common::serde::{Reader, SerDe, Writer};
use crate::common::util::to_valid_identifier;

const TYPE_INT: u8 = 1;
const TYPE_BIGINT: u8 = 2;
const TYPE_TEXT: u8 = 3;
const TYPE_STRUCT: u8 = 4;
const TYPE_STRUCT_FIELD: u8 = 5;

// Enum represents column type and/or table schema.
#[derive(Clone, Debug, PartialEq)]
pub enum Type {
  INT, // i32
  BIGINT, // i64
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
}

impl SerDe for Type {
  fn serialise(&self, writer: &mut Writer) {
    match self {
      Type::INT => writer.write_u8(TYPE_INT),
      Type::BIGINT => writer.write_u8(TYPE_BIGINT),
      Type::TEXT => writer.write_u8(TYPE_TEXT),
      Type::STRUCT(ref fields) => {
        writer.write_u8(TYPE_STRUCT);
        fields.serialise(writer);
      },
    }
  }

  fn deserialise(reader: &mut Reader) -> Self {
    match reader.read_u8() {
      TYPE_INT => Type::INT,
      TYPE_BIGINT => Type::BIGINT,
      TYPE_TEXT => Type::TEXT,
      TYPE_STRUCT => Type::STRUCT(Fields::deserialise(reader)),
      invalid_tpe => panic!("Unknown type: {}", invalid_tpe),
    }
  }
}

#[derive(Clone, Debug, PartialEq)]
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
      if !index.contains_key(&field.name) {
        // TODO: Improve clone of the string
        index.insert(field.name.clone(), i);
      } else if !ignore_duplicates {
        return Err(Error::DuplicateFieldName(field.name.clone()))
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
    // TODO: Improve the error message.
    Self::from(fields, true /* ignore_duplicates */).expect("Correct deserialisation")
  }
}

// Field of a STRUCT.
#[derive(Clone, Debug, PartialEq)]
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
    test_types_convert_roundtrip(Type::INT);
    test_types_convert_roundtrip(Type::BIGINT);
    test_types_convert_roundtrip(Type::TEXT);
    test_types_convert_roundtrip(Type::STRUCT(Fields::new(Vec::new()).unwrap()));

    // Struct type.
    let fields = vec![
      Field::new("f1", Type::INT, false).unwrap(),
      Field::new("f2", Type::TEXT, true).unwrap(),
      Field::new("f3", Type::BIGINT, false).unwrap(),
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
              Field::new("f21", Type::INT, false).unwrap(),
              Field::new("f22", Type::TEXT, true).unwrap(),
              Field::new("f23", Type::BIGINT, false).unwrap(),
            ]
          ).unwrap()
        ),
        true
      ).unwrap(),
    ];
    test_types_convert_roundtrip(Type::STRUCT(Fields::new(fields).unwrap()));
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
}
