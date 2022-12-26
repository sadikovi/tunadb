use crate::common::error::{Error, Res};
use crate::common::serde::{Reader, SerDe, Writer};
use crate::exec::types::{Field, Type};
use crate::storage::btree::BTreeIter;
use crate::storage::txn::{Set, TransactionRef, create_set, drop_set, get_set, next_object_id};

// Returns a valid identifier that is used throughout the database.
// The identifier conforms to [A-Za-z][A-Za-z0-9_] pattern.
#[inline]
fn to_valid_identifier(name: &str) -> Res<String> {
  if name.len() == 0 {
    return Err(Error::InvalidIdentifier(format!("Empty identifier")));
  }

  let mut first_char = true;
  let mut chars = name.chars();
  while let Some(c) = chars.next() {
    let is_letter =
      c >= 'A' && c <= 'Z' ||
      c >= 'a' && c <= 'z';
    let is_digit_or_underscore =
      c >= '0' && c <= '9' ||
      c == '_';

    // An identifier must start with a letter.
    if first_char && !is_letter {
      return Err(Error::InvalidIdentifier(format!("Identifier {} must start with a letter", name)));
    }

    // An identifier must only contain "A-Za-z0-9_" characters.
    if !is_letter && !is_digit_or_underscore {
      return Err(Error::InvalidIdentifier(format!("Identifier {} contains illegal characters", name)));
    }

    first_char = false;
  }

  Ok(name.to_uppercase())
}

// Returns a unique table key to store in the set.
// This allows us to locate a table using "exists" and "get" API while still being able to rename
// the schema.
#[inline]
fn to_unique_table_key(schema_id: u64, table_identifier: &str) -> Vec<u8> {
  let id_bytes = &u64_u8!(schema_id);
  let ident_bytes = table_identifier.as_bytes();
  let mut key = Vec::with_capacity(id_bytes.len() + ident_bytes.len());
  key.extend_from_slice(id_bytes);
  key.extend_from_slice(ident_bytes);
  key
}

// Table type to differentiate between base tables and views.
// Used in analysis.
#[derive(Clone, Copy, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum TableType {
  TABLE /* 1 */,
  SYSTEM_VIEW /* 2 */,
}

impl SerDe for TableType {
  fn serialise(&self, writer: &mut Writer) {
    match self {
      TableType::TABLE => writer.write_u8(1),
      TableType::SYSTEM_VIEW => writer.write_u8(2),
    }
  }

  fn deserialise(reader: &mut Reader) -> Self {
    match reader.read_u8() {
      1 => TableType::TABLE,
      2 => TableType::SYSTEM_VIEW,
      _ => unreachable!(),
    }
  }
}

#[derive(Clone, Debug, PartialEq)]
pub struct SchemaDesc {
  id: u64,
  schema_ident: String,
}

impl SchemaDesc {
  #[inline]
  pub fn id(&self) -> u64 {
    self.id
  }

  #[inline]
  pub fn schema_identifier(&self) -> &str {
    &self.schema_ident
  }
}

impl SerDe for SchemaDesc {
  fn serialise(&self, writer: &mut Writer) {
    writer.write_u64(self.id);
    writer.write_str(&self.schema_ident);
  }

  fn deserialise(reader: &mut Reader) -> Self {
    let id = reader.read_u64();
    let schema_ident = reader.read_str().to_owned();
    Self { id, schema_ident }
  }
}

#[derive(Clone, Debug, PartialEq)]
pub struct TableDesc {
  id: u64,
  schema_id: u64,
  table_ident: String,
  table_type: TableType,
  table_schema: Type,
}

impl TableDesc {
  #[inline]
  pub fn id(&self) -> u64 {
    self.id
  }

  #[inline]
  pub fn schema_id(&self) -> u64 {
    self.schema_id
  }

  #[inline]
  pub fn table_identifier(&self) -> &str {
    &self.table_ident
  }

  #[inline]
  pub fn table_type(&self) -> TableType {
    self.table_type
  }

  #[inline]
  pub fn table_schema(&self) -> &Type {
    &self.table_schema
  }
}

impl SerDe for TableDesc {
  fn serialise(&self, writer: &mut Writer) {
    writer.write_u64(self.id);
    writer.write_u64(self.schema_id);
    writer.write_str(&self.table_ident);
    self.table_type.serialise(writer);
    self.table_schema.serialise(writer);
  }

  fn deserialise(reader: &mut Reader) -> Self {
    let id = reader.read_u64();
    let schema_id = reader.read_u64();
    let table_ident = reader.read_str().to_owned();
    let table_type = TableType::deserialise(reader);
    let table_schema = Type::deserialise(reader);
    Self { id, schema_id, table_ident, table_type, table_schema }
  }
}

//===================================================================================
// System tables.
// IDs must be longer than 8 bytes to avoid collision with object ids which are u64.
//===================================================================================

// Schema information.
const SYSTEM_SCHEMAS: &[u8] = b"SYSTEM_SCHEMAS";
// Table information.
const SYSTEM_TABLES: &[u8] = b"SYSTEM_TABLES";

// Helper method to get SYSTEM_SCHEMAS.
#[inline]
fn get_system_schemas(txn: &TransactionRef) -> Res<Set> {
  match get_set(&txn, SYSTEM_SCHEMAS) {
    Some(set) => Ok(set),
    None => Err(internal_err!("SYSTEM_SCHEMAS does not exist")),
  }
}

// Helper method to get SYSTEM_TABLES.
#[inline]
fn get_system_tables(txn: &TransactionRef) -> Res<Set> {
  match get_set(&txn, SYSTEM_TABLES) {
    Some(set) => Ok(set),
    None => Err(internal_err!("SYSTEM_TABLES does not exist")),
  }
}

//=============
// Catalog API
//=============

const INFORMATION_SCHEMA: &str = "INFORMATION_SCHEMA";

// Assert if the current schema is information schema.
// We don't allow any modifications in the information schema.
fn assert_information_schema(schema_ident: &str) -> Res<()> {
  if schema_ident == INFORMATION_SCHEMA {
    Err(Error::OperationIsNotAllowed(format!("Cannot modify {}", INFORMATION_SCHEMA)))
  } else {
    Ok(())
  }
}

// Initialise catalog and system tables.
// This method is only called once during the database setup.
#[inline]
pub fn init_catalog(txn: &TransactionRef) -> Res<()> {
  create_set(txn, SYSTEM_SCHEMAS)?;
  create_schema0(txn, INFORMATION_SCHEMA, false, false /* enable_assert */)?;
  create_set(txn, SYSTEM_TABLES)?;
  create_table0(
    txn,
    INFORMATION_SCHEMA,
    "SCHEMATA",
    TableType::SYSTEM_VIEW,
    Type::STRUCT(
      vec![
        Field::new(String::from("SCHEMA_NAME"), Type::TEXT, false),
      ]
    ),
    false,
    false /* enable_assert */
  )?;
  create_table0(
    txn,
    INFORMATION_SCHEMA,
    "TABLES",
    TableType::SYSTEM_VIEW,
    Type::STRUCT(
      vec![
        Field::new(String::from("TABLE_SCHEMA"), Type::TEXT, false),
        Field::new(String::from("TABLE_NAME"), Type::TEXT, false),
        Field::new(String::from("TABLE_TYPE"), Type::TEXT, false),
      ]
    ),
    false,
    false /* enable_assert */
  )?;
  Ok(())
}

// Internal method to create a schema.
// Do not use it directly, assertion must be enabled.
#[inline]
fn create_schema0(
  txn: &TransactionRef,
  schema_name: &str,
  optional: bool,
  enable_assert: bool
) -> Res<()> {
  let schema_ident = to_valid_identifier(schema_name)?;
  if enable_assert {
    assert_information_schema(&schema_ident)?;
  }

  let set = get_system_schemas(&txn)?;
  if set.exists(&schema_ident.as_bytes()) {
    if !optional {
      Err(Error::SchemaAlreadyExists(schema_ident))
    } else {
      Ok(()) // the schema already exists
    }
  } else {
    let schema = SchemaDesc {
      id: next_object_id(&txn),
      schema_ident: schema_ident
    };
    // Serialise to store in the set.
    let mut writer = Writer::new();
    schema.serialise(&mut writer);
    // Store in the sys table, the key must be the schema identifier.
    let mut set = get_system_schemas(&txn)?;
    set.put(&schema.schema_identifier().as_bytes(), &writer.to_vec());
    Ok(())
  }
}

// Catalog API: Creates schema with the provided name.
// When `optional` is set to true, ignores the operation if the schema already exists.
pub fn create_schema(txn: &TransactionRef, schema_name: &str, optional: bool) -> Res<()> {
  create_schema0(txn, schema_name, optional, true /* enable_assert */)
}

// Catalog API: Returns schema info for the name if exists.
pub fn get_schema(txn: &TransactionRef, schema_name: &str) -> Res<SchemaDesc> {
  let schema_ident = to_valid_identifier(schema_name)?;
  let set = get_system_schemas(&txn)?;
  match set.get(&schema_ident.as_bytes()) {
    Some(data) => {
      let mut reader = Reader::from_buf(data);
      Ok(SchemaDesc::deserialise(&mut reader))
    },
    None => Err(Error::SchemaDoesNotExist(schema_ident)),
  }
}

// Catalog API: Returns the list of all schemas in the catalog.
pub fn list_schemas(txn: &TransactionRef) -> Res<SchemaDescIter> {
  let mut set = get_system_schemas(&txn)?;
  let iter = set.list(None, None);
  Ok(SchemaDescIter { iter })
}

// Internal method to drop a schema.
// Do not use it directly, assertion must be enabled.
#[inline]
fn drop_schema0(
  txn: &TransactionRef,
  schema_name: &str,
  cascade: bool,
  optional: bool,
  enable_assert: bool
) -> Res<()> {
  let schema_ident = to_valid_identifier(schema_name)?;
  if enable_assert {
    assert_information_schema(&schema_ident)?;
  }

  let mut set = get_system_schemas(&txn)?;
  if set.exists(&schema_ident.as_bytes()) {
    // If the schema contains at least one table, we cannot drop it without "cascade" property.
    let has_tables;
    {
      let mut iter = list_tables(&txn, &schema_ident)?;
      has_tables = iter.next().is_some();
    }

    if has_tables && !cascade {
      Err(Error::SchemaIsNotEmpty(schema_ident))
    } else {
      let mut tables = Vec::new();
      {
        let mut iter = list_tables(&txn, &schema_ident)?;
        while let Some(table) = iter.next() {
          tables.push(table);
        }
      }
      // The "tables" vector must be empty in the case of an empty schema.
      assert!(has_tables || tables.len() == 0);

      // Drop all of the tables in the schema.
      for table in &tables {
        drop_table_internal(&txn, &table)?;
      }
      // Drop the schema.
      set.del(&schema_ident.as_bytes());
      Ok(())
    }
  } else {
    if !optional {
      Err(Error::SchemaDoesNotExist(schema_ident))
    } else {
      Ok(())
    }
  }
}

// Catalog API: Drops the schema.
// If `optional` is set to true, no operation is performed if the schema does not exist.
// If `cascade` is set to true, everything in the schema is also dropped (both metadata and data).
pub fn drop_schema(
  txn: &TransactionRef,
  schema_name: &str,
  cascade: bool,
  optional: bool
) -> Res<()> {
  drop_schema0(txn, schema_name, cascade, optional, true /* enable_assert */)
}

// Internal method to create a table.
// Do not use it directly, assertion must be enabled.
#[inline]
fn create_table0(
  txn: &TransactionRef,
  schema_name: &str,
  table_name: &str,
  table_type: TableType,
  table_schema: Type,
  optional: bool,
  enable_assert: bool
) -> Res<()> {
  let schema = get_schema(txn, schema_name)?;
  if enable_assert {
    assert_information_schema(&schema.schema_identifier())?;
  }

  let table_ident = to_valid_identifier(table_name)?;
  let table_key = to_unique_table_key(schema.id(), &table_ident);

  let mut set = get_system_tables(&txn)?;
  if set.exists(&table_key) {
    if !optional {
      Err(Error::TableAlreadyExists(schema.schema_identifier().to_owned(), table_ident))
    } else {
      Ok(()) // the table already exists
    }
  } else {
    if !table_schema.is_struct() {
      return Err(Error::TableInvalidSchema(format!("Invalid table schema: {:?}", table_schema)));
    }

    let table = TableDesc {
      id: next_object_id(&txn),
      schema_id: schema.id(),
      table_ident: table_ident,
      table_type: table_type,
      table_schema: table_schema,
    };
    // Serialise to store in the set.
    let mut writer = Writer::new();
    table.serialise(&mut writer);
    // Store in the sys table, the key must be the "schema_id.table".
    set.put(&table_key, &writer.to_vec());
    Ok(())
  }
}

// Catalog API: Creates a table with the provided schema name and table name.
// The schema must exist.
// If `optional` is set to true, the operation is ignored if the table already exists.
pub fn create_table(
  txn: &TransactionRef,
  schema_name: &str,
  table_name: &str,
  table_schema: Type,
  optional: bool
) -> Res<()> {
  create_table0(
    txn,
    schema_name,
    table_name,
    TableType::TABLE,
    table_schema,
    optional,
    true /* enable_assert */
  )
}

// Catalog API: Returns the table description for "schema.table".
pub fn get_table(txn: &TransactionRef, schema_name: &str, table_name: &str) -> Res<TableDesc> {
  let schema = get_schema(txn, schema_name)?;
  let table_ident = to_valid_identifier(table_name)?;
  let table_key = to_unique_table_key(schema.id(), &table_ident);

  let set = get_system_tables(&txn)?;
  match set.get(&table_key) {
    Some(data) => {
      let mut reader = Reader::from_buf(data);
      Ok(TableDesc::deserialise(&mut reader))
    },
    None => Err(Error::TableDoesNotExist(schema.schema_identifier().to_owned(), table_ident)),
  }
}

// Catalog API: Returns the list of all tables in the provided schema.
pub fn list_tables(txn: &TransactionRef, schema_name: &str) -> Res<TableDescIter> {
  let schema = get_schema(txn, schema_name)?;
  let mut set = get_system_tables(&txn)?;

  // When listing, we use a dummy empty table name as the first key to locate the schema's tables.
  let table_key = to_unique_table_key(schema.id(), "");

  let iter = set.list(Some(&table_key), None);
  Ok(TableDescIter { schema_id: schema.id(), iter: iter })
}

// Internal method to drop the table if the table exists.
// The method also drops the associated data if it exists.
fn drop_table_internal(txn: &TransactionRef, table: &TableDesc) -> Res<()> {
  // If the table has just been created, there may not be any set for the data yet.
  // Ignore if that is the case.
  if let Some(set) = get_set(&txn, &u64_u8!(table.id())) {
    drop_set(&txn, set);
  }
  // Delete table metadata.
  let table_key = to_unique_table_key(table.schema_id(), &table.table_identifier());
  let mut set = get_system_tables(&txn)?;
  set.del(&table_key);
  Ok(())
}

// Internal method to drop a table.
// Do not use it directly, assertion must be enabled.
#[inline]
fn drop_table0(
  txn: &TransactionRef,
  schema_name: &str,
  table_name: &str,
  optional: bool,
  enable_assert: bool
) -> Res<()> {
  let schema = get_schema(txn, schema_name)?;
  if enable_assert {
    assert_information_schema(&schema.schema_identifier())?;
  }

  let table_ident = to_valid_identifier(table_name)?;
  let table_key = to_unique_table_key(schema.id(), &table_ident);

  let set = get_system_tables(&txn)?;
  let table_opt = match set.get(&table_key) {
    Some(data) => {
      let mut reader = Reader::from_buf(data);
      Some(TableDesc::deserialise(&mut reader))
    },
    None => None,
  };

  if let Some(table) = table_opt {
    drop_table_internal(&txn, &table)
  } else {
    if !optional {
      Err(Error::TableDoesNotExist(schema.schema_identifier().to_owned(), table_ident))
    } else {
      Ok(())
    }
  }
}

// Catalog API: Drops a table for the provided schema and table names.
// The schema must exist.
// If `optional` is set to true, the operation is ignored if the table does not exist.
pub fn drop_table(
  txn: &TransactionRef,
  schema_name: &str,
  table_name: &str,
  optional: bool
) -> Res<()> {
  drop_table0(txn, schema_name, table_name, optional, true /* enable_assert */)
}

// Iterator for `SchemaDesc`.
pub struct SchemaDescIter {
  iter: BTreeIter,
}

impl Iterator for SchemaDescIter {
  type Item = SchemaDesc;

  fn next(&mut self) -> Option<Self::Item> {
    match self.iter.next() {
      Some((_key, data)) => {
        let mut reader = Reader::from_buf(data);
        Some(SchemaDesc::deserialise(&mut reader))
      },
      None => None,
    }
  }
}

// Iterator for `TableDesc`.
pub struct TableDescIter {
  schema_id: u64,
  iter: BTreeIter,
}

impl Iterator for TableDescIter {
  type Item = TableDesc;

  fn next(&mut self) -> Option<Self::Item> {
    match self.iter.next() {
      Some((_key, data)) => {
        let mut reader = Reader::from_buf(data);
        let table = TableDesc::deserialise(&mut reader);
        // We need to stop our search when the schema changes.
        if table.schema_id() == self.schema_id {
          Some(table)
        } else {
          // We have seen all of the tables with this schema id.
          None
        }
      },
      None => None,
    }
  }
}

#[cfg(test)]
pub mod tests {
  use super::*;
  use crate::storage::db;

  // Helper method to create and initialise the database.
  fn init_db() -> db::DB {
    let mut dbc = db::open(None).try_build().unwrap();
    dbc.with_txn(true, |txn| {
      init_catalog(&txn).unwrap();
    });
    dbc
  }

  #[test]
  fn test_catalog_to_valid_identifier() {
    assert!(to_valid_identifier("").is_err());
    assert!(to_valid_identifier("_").is_err());
    assert!(to_valid_identifier("01234").is_err());
    assert!(to_valid_identifier("abc def").is_err());
    assert!(to_valid_identifier("ABC DEF").is_err());
    assert!(to_valid_identifier("_123").is_err());
    assert!(to_valid_identifier("1abc").is_err());
    assert!(to_valid_identifier(" abc").is_err());

    assert_eq!(to_valid_identifier("summary"), Ok("SUMMARY".to_owned()));
    assert_eq!(to_valid_identifier("s123456"), Ok("S123456".to_owned()));
    assert_eq!(to_valid_identifier("s1_2_3_4"), Ok("S1_2_3_4".to_owned()));
    assert_eq!(to_valid_identifier("s"), Ok("S".to_owned()));
  }

  #[test]
  fn test_catalog_to_unique_table_key() {
    assert_eq!(to_unique_table_key(0, ""), vec![0, 0, 0, 0, 0, 0, 0, 0]);
    assert_eq!(to_unique_table_key(1, ""), vec![1, 0, 0, 0, 0, 0, 0, 0]);
    assert_eq!(to_unique_table_key(1, "1"), vec![1, 0, 0, 0, 0, 0, 0, 0, 49]);
    assert_eq!(to_unique_table_key(128, "abc"), vec![128, 0, 0, 0, 0, 0, 0, 0, 97, 98, 99]);
  }

  #[test]
  fn test_catalog_table_type_serde() {
    fn serde(tpe: TableType) -> TableType {
      let mut writer = Writer::new();
      tpe.serialise(&mut writer);
      let mut reader = Reader::from_buf(writer.to_vec());
      TableType::deserialise(&mut reader)
    }

    assert_eq!(serde(TableType::TABLE), TableType::TABLE);
    assert_eq!(serde(TableType::SYSTEM_VIEW), TableType::SYSTEM_VIEW);
  }

  #[test]
  fn test_catalog_schema_desc_serde() {
    fn serde(schema: &SchemaDesc) -> SchemaDesc {
      let mut writer = Writer::new();
      schema.serialise(&mut writer);
      let mut reader = Reader::from_buf(writer.to_vec());
      SchemaDesc::deserialise(&mut reader)
    }

    let schema = SchemaDesc { id: 0, schema_ident: String::from("") };
    assert_eq!(serde(&schema), schema);

    let schema = SchemaDesc { id: 123, schema_ident: String::from("ABC") };
    assert_eq!(serde(&schema), schema);
  }

  #[test]
  fn test_catalog_table_desc_serde() {
    fn serde(table: &TableDesc) -> TableDesc {
      let mut writer = Writer::new();
      table.serialise(&mut writer);
      let mut reader = Reader::from_buf(writer.to_vec());
      TableDesc::deserialise(&mut reader)
    }

    let table = TableDesc {
      id: 0,
      schema_id: 0,
      table_ident: String::from(""),
      table_type: TableType::SYSTEM_VIEW,
      table_schema: Type::STRUCT(vec![]),
    };
    assert_eq!(serde(&table), table);

    let table = TableDesc {
      id: 123,
      schema_id: 234,
      table_ident: String::from("TEST"),
      table_type: TableType::TABLE,
      table_schema: Type::STRUCT(
        vec![
          Field::new("c1".to_owned(), Type::INT, false),
          Field::new("c2".to_owned(), Type::TEXT, false),
          Field::new("c3".to_owned(), Type::STRUCT(vec![]), true),
        ]
      ),
    };
    assert_eq!(serde(&table), table);
  }

  #[test]
  fn test_catalog_check_sys_tables_length() {
    assert!(SYSTEM_SCHEMAS.len() > 8);
    assert!(SYSTEM_TABLES.len() > 8);
  }

  #[test]
  fn test_catalog_init_catalog() {
    let mut dbc = db::open(None).try_build().unwrap();
    dbc.with_txn(true, |txn| {
      init_catalog(&txn).unwrap();
    });

    // All system table must be created.
    dbc.with_txn(true, |txn| {
      let schema = get_schema(&txn, INFORMATION_SCHEMA).unwrap();
      assert_eq!(schema.id(), 0);
      assert_eq!(schema.schema_identifier(), INFORMATION_SCHEMA);

      let table = get_table(&txn, INFORMATION_SCHEMA, "SCHEMATA").unwrap();
      assert_eq!(table.id(), 1);
      assert_eq!(table.schema_id(), 0);
      assert_eq!(table.table_identifier(), "SCHEMATA");

      let table = get_table(&txn, INFORMATION_SCHEMA, "TABLES").unwrap();
      assert_eq!(table.id(), 2);
      assert_eq!(table.schema_id(), 0);
      assert_eq!(table.table_identifier(), "TABLES");
    });
  }

  #[test]
  fn test_catalog_information_schema_modification() {
    // The test verifies that we cannot create or drop a schema with INFORMATION_SCHEMA name.
    let err = Err(Error::OperationIsNotAllowed("Cannot modify INFORMATION_SCHEMA".to_owned()));

    let mut dbc = init_db();

    dbc.with_txn(true, |txn| {
      assert_eq!(create_schema(&txn, INFORMATION_SCHEMA, false), err);
      assert_eq!(create_schema(&txn, INFORMATION_SCHEMA, true), err);
    });

    dbc.with_txn(true, |txn| {
      assert_eq!(drop_schema(&txn, INFORMATION_SCHEMA, true, false), err);
      assert_eq!(drop_schema(&txn, INFORMATION_SCHEMA, true, true), err);
    });

    dbc.with_txn(true, |txn| {
      assert_eq!(
        create_table(&txn, INFORMATION_SCHEMA, "test", Type::STRUCT(vec![]), false),
        err
      );
      assert_eq!(
        create_table(&txn, INFORMATION_SCHEMA, "test", Type::STRUCT(vec![]), true),
        err
      );
    });
  }

  #[test]
  fn test_catalog_create_schema_already_exists_err() {
    let mut dbc = init_db();

    dbc.with_txn(true, |txn| {
      create_schema(&txn, "TEST", false).unwrap();
      assert_eq!(
        create_schema(&txn, "TEST", false),
        Err(Error::SchemaAlreadyExists("TEST".to_owned()))
      );
    });

    dbc.with_txn(true, |txn| {
      assert_eq!(
        create_schema(&txn, "TEST", false),
        Err(Error::SchemaAlreadyExists("TEST".to_owned()))
      );
    });
  }

  #[test]
  fn test_catalog_create_schema_already_exists_ok() {
    let mut dbc = init_db();

    dbc.with_txn(true, |txn| {
      create_schema(&txn, "TEST", false).unwrap();
      create_schema(&txn, "TEST", true).unwrap();

      let mut counter = 0;
      let mut iter = list_schemas(&txn).unwrap();
      while let Some(desc) = iter.next() {
        if desc.schema_identifier() != INFORMATION_SCHEMA {
          counter += 1;
        }
      }
      assert_eq!(counter, 1);
    });
  }

  #[test]
  fn test_catalog_create_schema() {
    let mut dbc = init_db();

    dbc.with_txn(true, |txn| {
      create_schema(&txn, "test1", false).unwrap();
      create_schema(&txn, "test2", false).unwrap();
      create_schema(&txn, "test3", false).unwrap();
    });
    dbc.with_txn(true, |txn| {
      let schema = get_schema(&txn, "test1").unwrap();
      assert_eq!(schema.schema_identifier(), "TEST1");

      let schema = get_schema(&txn, "test2").unwrap();
      assert_eq!(schema.schema_identifier(), "TEST2");

      let schema = get_schema(&txn, "test3").unwrap();
      assert_eq!(schema.schema_identifier(), "TEST3");

      assert!(get_schema(&txn, "test4").is_err());
    });

    // Rollback - no schema created.
    dbc.with_txn(false, |txn| {
      create_schema(&txn, "test_schema", false).unwrap();
      assert!(get_schema(&txn, "test_schema").is_ok());
      txn.borrow_mut().rollback();
    });
    dbc.with_txn(true, |txn| {
      assert!(get_schema(&txn, "test_schema").is_err());
    });

    // Test create with an already existing schema.
    dbc.with_txn(true, |txn| {
      create_schema(&txn, "existing_schema", false).unwrap();
      assert!(get_schema(&txn, "existing_schema").is_ok());
      create_schema(&txn, "existing_schema", true).unwrap();
    });
  }

  #[test]
  fn test_catalog_get_schema() {
    let mut dbc = init_db();

    dbc.with_txn(true, |txn| {
      assert!(get_schema(&txn, INFORMATION_SCHEMA).is_ok());
      assert!(get_schema(&txn, "test").is_err());
    });
  }

  #[test]
  fn test_catalog_list_schemas() {
    let mut dbc = init_db();

    dbc.with_txn(true, |txn| {
      for i in 0..1000 {
        create_schema(&txn, &format!("schema_{}", i), false).unwrap();
      }
    });

    dbc.with_txn(true, |txn| {
      let mut iter = list_schemas(&txn).unwrap();
      let mut counter = 0;
      while let Some(_) = iter.next() {
        counter += 1;
      }
      assert_eq!(counter, 1000 + 1 /* INFORMATION_SCHEMA */);
    });
  }

  #[test]
  fn test_catalog_drop_schema() {
    let mut dbc = init_db();

    // Test in the same transaction.
    dbc.with_txn(true, |txn| {
      create_schema(&txn, "test", false).unwrap();
      drop_schema(&txn, "test", false, false).unwrap();
      assert!(get_schema(&txn, "test").is_err());
    });

    // Test in a separate transaction.
    dbc.with_txn(true, |txn| {
      create_schema(&txn, "test", false).unwrap();
    });
    dbc.with_txn(true, |txn| {
      drop_schema(&txn, "test", false, false).unwrap();
    });
    dbc.with_txn(true, |txn| {
      assert!(get_schema(&txn, "test").is_err());
    });

    // Rollback - schema is not dropped.
    dbc.with_txn(true, |txn| {
      create_schema(&txn, "test_schema", false).unwrap();
      assert!(get_schema(&txn, "test_schema").is_ok());
    });
    dbc.with_txn(false, |txn| {
      drop_schema(&txn, "test_schema", false, false).unwrap();
      assert!(get_schema(&txn, "test_schema").is_err());
      txn.borrow_mut().rollback();
    });
    dbc.with_txn(true, |txn| {
      assert!(get_schema(&txn, "test_schema").is_ok());
    });

    // Test drop with non-existent schema.
    dbc.with_txn(true, |txn| {
      assert!(get_schema(&txn, "non_existent_schema").is_err());
      drop_schema(&txn, "non_existent_schema", false, true).unwrap();
    });
  }

  #[test]
  fn test_catalog_drop_schema_cascade() {
    let mut dbc = init_db();

    // Setup.
    dbc.with_txn(true, |txn| {
      create_schema(&txn, "test_schema", false).unwrap();
      create_table(&txn, "test_schema", "table1", Type::STRUCT(vec![]), false).unwrap();
      create_table(&txn, "test_schema", "table2", Type::STRUCT(vec![]), false).unwrap();
      create_table(&txn, "test_schema", "table3", Type::STRUCT(vec![]), false).unwrap();
    });

    // Drop schema with tables is not allowed.
    dbc.with_txn(true, |txn| {
      assert_eq!(
        drop_schema(&txn, "test_schema", false, false),
        Err(Error::SchemaIsNotEmpty("TEST_SCHEMA".to_owned()))
      );
      assert_eq!(
        drop_schema(&txn, "test_schema", false, true /* optional */),
        Err(Error::SchemaIsNotEmpty("TEST_SCHEMA".to_owned()))
      );
    });

    // Drop schema with cascade should drop the tables.
    dbc.with_txn(true, |txn| {
      drop_schema(&txn, "test_schema", true, false).unwrap();
      assert!(get_schema(&txn, "test_schema").is_err());
    });
    dbc.with_txn(true, |txn| {
      // Only INFORMATION_SCHEMA tables must be present.
      let mut set = get_system_tables(&txn).unwrap();
      let mut iter = set.list(None, None);
      assert_eq!(iter.next().unwrap().0, to_unique_table_key(0, "SCHEMATA"));
      assert_eq!(iter.next().unwrap().0, to_unique_table_key(0, "TABLES"));
      assert_eq!(iter.next(), None);
    });
  }

  #[test]
  fn test_catalog_create_table_schema_does_not_exist() {
    let mut dbc = init_db();

    dbc.with_txn(true, |txn| {
      assert_eq!(
        create_table(&txn, "test_schema", "table", Type::STRUCT(vec![]), false),
        Err(Error::SchemaDoesNotExist("TEST_SCHEMA".to_owned()))
      );
    });
  }

  #[test]
  fn test_catalog_create_table() {
    let mut dbc = init_db();

    // Create a new table.
    dbc.with_txn(true, |txn| {
      create_schema(&txn, "test_schema", false).unwrap();
      create_table(&txn, "test_schema", "table1", Type::STRUCT(vec![]), false).unwrap();
    });
    dbc.with_txn(true, |txn| {
      let table = get_table(&txn, "test_schema", "table1").unwrap();
      assert_eq!(table.table_identifier(), "TABLE1");
      assert_eq!(table.table_type(), TableType::TABLE);
    });

    // Create table with the same name.
    dbc.with_txn(true, |txn| {
      assert_eq!(
        create_table(&txn, "test_schema", "table1", Type::STRUCT(vec![]), false),
        Err(Error::TableAlreadyExists("TEST_SCHEMA".to_owned(), "TABLE1".to_owned()))
      );
      assert_eq!(
        create_table(&txn, "test_schema", "table1", Type::STRUCT(vec![]), true),
        Ok(())
      );
    });

    // Rollback - table should not be created.
    dbc.with_txn(false, |txn| {
      create_table(&txn, "test_schema", "table2", Type::STRUCT(vec![]), false).unwrap();
      assert!(get_table(&txn, "test_schema", "table2").is_ok());
      txn.borrow_mut().rollback();
    });
    dbc.with_txn(true, |txn| {
      assert!(get_table(&txn, "test_schema", "table2").is_err());
    });
  }

  #[test]
  fn test_catalog_get_table() {
    let mut dbc = init_db();

    dbc.with_txn(true, |txn| {
      create_schema(&txn, "test_schema", false).unwrap();
      create_table(&txn, "test_schema", "table", Type::STRUCT(vec![]), false).unwrap();
    });

    dbc.with_txn(true, |txn| {
      let table = get_table(&txn, "test_schema", "table").unwrap();
      assert_eq!(table.id(), 4);
      assert_eq!(table.schema_id(), 3);
      assert_eq!(table.table_identifier(), "TABLE");
      assert_eq!(table.table_type(), TableType::TABLE);
      assert_eq!(table.table_schema(), &Type::STRUCT(vec![]));
    });
  }

  #[test]
  fn test_catalog_list_tables() {
    let mut dbc = init_db();

    // Create different schemas and tables.
    dbc.with_txn(true, |txn| {
      create_schema(&txn, "schema1", false).unwrap();
      create_table(&txn, "schema1", "table1", Type::STRUCT(vec![]), false).unwrap();
      create_table(&txn, "schema1", "table2", Type::STRUCT(vec![]), false).unwrap();
      create_table(&txn, "schema1", "table3", Type::STRUCT(vec![]), false).unwrap();

      create_schema(&txn, "schema2", false).unwrap();
      create_table(&txn, "schema2", "table4", Type::STRUCT(vec![]), false).unwrap();
      create_table(&txn, "schema2", "table5", Type::STRUCT(vec![]), false).unwrap();
      create_table(&txn, "schema2", "table6", Type::STRUCT(vec![]), false).unwrap();
    });

    // Verify that we only return tables for the selected schema.
    dbc.with_txn(true, |txn| {
      let mut iter = list_tables(&txn, "schema1").unwrap();
      assert_eq!(iter.next().unwrap().table_identifier(), "TABLE1");
      assert_eq!(iter.next().unwrap().table_identifier(), "TABLE2");
      assert_eq!(iter.next().unwrap().table_identifier(), "TABLE3");
      assert_eq!(iter.next(), None);

      let mut iter = list_tables(&txn, "schema2").unwrap();
      assert_eq!(iter.next().unwrap().table_identifier(), "TABLE4");
      assert_eq!(iter.next().unwrap().table_identifier(), "TABLE5");
      assert_eq!(iter.next().unwrap().table_identifier(), "TABLE6");
      assert_eq!(iter.next(), None);

      let mut iter = list_tables(&txn, INFORMATION_SCHEMA).unwrap();
      assert_eq!(iter.next().unwrap().table_identifier(), "SCHEMATA");
      assert_eq!(iter.next().unwrap().table_identifier(), "TABLES");
      assert_eq!(iter.next(), None);
    });
  }

  #[test]
  fn test_catalog_drop_table() {
    let mut dbc = init_db();

    dbc.with_txn(true, |txn| {
      create_schema(&txn, "schema", false).unwrap();
    });

    // Drop table in the same transaction.
    dbc.with_txn(true, |txn| {
      create_table(&txn, "schema", "table1", Type::STRUCT(vec![]), false).unwrap();
      drop_table(&txn, "schema", "table1", false).unwrap();
      assert!(get_table(&txn, "schema", "table1").is_err());
    });

    // Drop table in a separate transaction.
    dbc.with_txn(true, |txn| {
      create_table(&txn, "schema", "table2", Type::STRUCT(vec![]), false).unwrap();
    });
    dbc.with_txn(true, |txn| {
      drop_table(&txn, "schema", "table2", false).unwrap();
      assert!(get_table(&txn, "schema", "table2").is_err());
    });

    // Drop table - table does not exist.
    dbc.with_txn(true, |txn| {
      assert_eq!(
        drop_table(&txn, "schema", "table3", false),
        Err(Error::TableDoesNotExist("SCHEMA".to_owned(), "TABLE3".to_owned()))
      );
      assert_eq!(drop_table(&txn, "schema", "table3", true), Ok(()));
    });

    // Rollback - table is not dropped.
    dbc.with_txn(true, |txn| {
      create_table(&txn, "schema", "table4", Type::STRUCT(vec![]), false).unwrap();
    });
    dbc.with_txn(false, |txn| {
      drop_table(&txn, "schema", "table4", false).unwrap();
      assert!(get_table(&txn, "schema", "table4").is_err());
      txn.borrow_mut().rollback();
    });
    dbc.with_txn(true, |txn| {
      assert!(get_table(&txn, "schema", "table4").is_ok());
    });
  }
}
