use crate::common::serde::{Reader, SerDe, Writer};

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
  STRUCT(Vec<StructField>), // can represent table schema
}

impl SerDe for Type {
  fn serialise(&self, writer: &mut Writer) {
    match self {
      Type::INT => writer.write_u8(TYPE_INT),
      Type::BIGINT => writer.write_u8(TYPE_BIGINT),
      Type::TEXT => writer.write_u8(TYPE_TEXT),
      Type::STRUCT(ref fields) => {
        writer.write_u8(TYPE_STRUCT);
        writer.write_u32(fields.len() as u32);
        for field in fields {
          field.serialise(writer);
        }
      },
    }
  }

  fn deserialise(reader: &mut Reader) -> Self {
    match reader.read_u8() {
      TYPE_INT => Type::INT,
      TYPE_BIGINT => Type::BIGINT,
      TYPE_TEXT => Type::TEXT,
      TYPE_STRUCT => {
        let len = reader.read_u32() as usize;
        let mut fields = Vec::with_capacity(len);
        for _ in 0..len {
          fields.push(StructField::deserialise(reader));
        }
        Type::STRUCT(fields)
      },
      invalid_tpe => panic!("Unknown type: {}", invalid_tpe),
    }
  }
}

// Field of the StructType.
#[derive(Clone, Debug, PartialEq)]
pub struct StructField {
  name: String,
  data_type: Type,
  nullable: bool,
}

impl StructField {
  // Creates a new StructField.
  pub fn new(name: String, data_type: Type, nullable: bool) -> Self {
    Self { name, data_type, nullable }
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

impl SerDe for StructField {
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
    let name = reader.read_str().to_owned();
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
    test_types_convert_roundtrip(Type::STRUCT(Vec::new()));

    // Struct type.
    let fields = vec![
      StructField::new("f1".to_owned(), Type::INT, false),
      StructField::new("f2".to_owned(), Type::TEXT, true),
      StructField::new("f3".to_owned(), Type::BIGINT, false),
    ];
    test_types_convert_roundtrip(Type::STRUCT(fields));

    // Nested types.
    let fields = vec![
      StructField::new("f1".to_owned(), Type::STRUCT(Vec::new()), true),
      StructField::new(
        "f2".to_owned(),
        Type::STRUCT(
          vec![
            StructField::new("f21".to_owned(), Type::INT, false),
            StructField::new("f22".to_owned(), Type::TEXT, true),
            StructField::new("f23".to_owned(), Type::BIGINT, false),
          ]
        ),
        true
      ),
    ];
    test_types_convert_roundtrip(Type::STRUCT(fields));
  }
}
