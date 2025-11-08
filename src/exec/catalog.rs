use crate::common::error::{Error, Res};
use crate::common::serde::{Reader, SerDe, Writer};
use crate::core::types::{Field, Fields, Type};
use crate::core::util::to_valid_identifier;
use crate::storage::btree::BTreeIter;
use crate::storage::txn::{Set, TransactionRef, create_set, drop_set, get_set, next_object_id};

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
// Used in query analysis.
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

#[derive(Debug, PartialEq)]
pub struct SchemaInfo {
  schema_id: u64, // globally unique id
  schema_identifier: String,
}

impl SchemaInfo {
  // Returns globally unique object id for the schema.
  #[inline]
  pub fn schema_id(&self) -> u64 {
    self.schema_id
  }

  // Returns the schema identifier.
  #[inline]
  pub fn schema_identifier(&self) -> &str {
    &self.schema_identifier
  }

  #[inline]
  pub fn into_schema_identifier(self) -> String {
    self.schema_identifier
  }
}

impl SerDe for SchemaInfo {
  fn serialise(&self, writer: &mut Writer) {
    writer.write_u64(self.schema_id);
    writer.write_str(&self.schema_identifier);
  }

  fn deserialise(reader: &mut Reader) -> Self {
    let schema_id = reader.read_u64();
    let schema_identifier = reader.read_str().to_string();
    Self { schema_id, schema_identifier }
  }
}

// Private struct that is used for serialisation/deserialisation.
// We do not store schema identifier since it can change while schema id is unique.
#[derive(Debug, PartialEq)]
pub struct TableInfo {
  schema_id: u64, // globally unique id
  table_id: u64, // globally unique id
  table_identifier: String, // unique within the schema
  table_type: TableType,
  table_fields: Fields,
}

impl TableInfo {
  // Returns globally unique id for the schema.
  #[inline]
  pub fn schema_id(&self) -> u64 {
    self.schema_id
  }

  // Returns globally unique id for the table.
  #[inline]
  pub fn table_id(&self) -> u64 {
    self.table_id
  }

  // Returns the table identifier.
  #[inline]
  pub fn table_identifier(&self) -> &str {
    &self.table_identifier
  }

  // Returns the table type.
  #[inline]
  pub fn table_type(&self) -> TableType {
    self.table_type
  }

  // Returns the table fields/schema.
  #[inline]
  pub fn table_fields(&self) -> &Fields {
    &self.table_fields
  }

  #[inline]
  pub fn into_table_identifier(self) -> String {
    self.table_identifier
  }
}

impl SerDe for TableInfo {
  fn serialise(&self, writer: &mut Writer) {
    writer.write_u64(self.schema_id);
    writer.write_u64(self.table_id);
    writer.write_str(&self.table_identifier);
    self.table_type.serialise(writer);
    self.table_fields.serialise(writer);
  }

  fn deserialise(reader: &mut Reader) -> Self {
    let schema_id = reader.read_u64();
    let table_id = reader.read_u64();
    let table_identifier = reader.read_str().to_string();
    let table_type = TableType::deserialise(reader);
    let table_fields = Fields::deserialise(reader);
    Self { table_id, schema_id, table_identifier, table_type, table_fields }
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

// Initialise catalog and system tables.
// This method must only be called once during the database setup.
pub fn init_catalog(txn: &TransactionRef) -> Res<()> {
  create_set(&txn, SYSTEM_SCHEMAS)?;
  create_set(&txn, SYSTEM_TABLES)?;

  create_schema_internal(&txn, INFORMATION_SCHEMA.to_string(), false)?;
  let schema = get_schema(&txn, INFORMATION_SCHEMA)?;

  create_table_internal(
    &txn,
    &schema,
    "SCHEMATA".to_string(),
    TableType::SYSTEM_VIEW,
    Fields::new(
      vec![
        Field::new("SCHEMA_NAME", Type::TEXT, false)?,
      ]
    )?,
    false
  )?;

  create_table_internal(
    &txn,
    &schema,
    "TABLES".to_string(),
    TableType::SYSTEM_VIEW,
    Fields::new(
      vec![
        Field::new("TABLE_SCHEMA", Type::TEXT, false)?,
        Field::new("TABLE_NAME", Type::TEXT, false)?,
        Field::new("TABLE_TYPE", Type::TEXT, false)?,
      ]
    )?,
    false
  )?;

  Ok(())
}

// Catalog API: Creates schema with the provided name.
// When `optional` is set to true, ignores the operation if the schema already exists.
pub fn create_schema(txn: &TransactionRef, schema_name: &str, optional: bool) -> Res<()> {
  let schema_identifier = to_valid_identifier(schema_name)?;
  assert_information_schema(&schema_identifier)?;
  create_schema_internal(&txn, schema_identifier, optional)
}

 // Catalog API: Returns schema info for the name if exists.
pub fn get_schema(txn: &TransactionRef, schema_name: &str) -> Res<SchemaInfo> {
  let schema_identifier = to_valid_identifier(schema_name)?;
  let set = get_system_schemas(&txn)?;
  get_schema_internal(&set, schema_identifier)
}

// Catalog API: Returns the list of all schemas in the catalog.
pub fn list_schemas(txn: &TransactionRef) -> Res<SchemaInfoIter> {
  let mut set = get_system_schemas(&txn)?;
  list_schemas_internal(&mut set)
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
  let schema_identifier = to_valid_identifier(schema_name)?;
  assert_information_schema(&schema_identifier)?;
  drop_schema_internal(&txn, schema_identifier, cascade, optional)
}

// Catalog API: Creates a table with the provided schema name and table name.
// The schema must exist.
// If `optional` is set to true, the operation is ignored if the table already exists.
pub fn create_table(
  txn: &TransactionRef,
  schema_name: &str,
  table_name: &str,
  table_fields: Fields,
  optional: bool
) -> Res<()> {
  let schema = get_schema(&txn, schema_name)?;
  assert_information_schema(&schema.schema_identifier)?;
  let table_identifier = to_valid_identifier(table_name)?;
  create_table_internal(&txn, &schema, table_identifier, TableType::TABLE, table_fields, optional)
}

// Catalog API: Returns the schema and table info for "schema.table".
pub fn get_table(
  txn: &TransactionRef,
  schema_name: &str,
  table_name: &str
) -> Res<(SchemaInfo, TableInfo)> {
  let schema = get_schema(&txn, schema_name)?;
  let table_identifier = to_valid_identifier(table_name)?;
  let set = get_system_tables(&txn)?;
  get_table_internal(&set, schema, table_identifier)
}

// Catalog API: Returns the list of all tables in the provided schema.
pub fn list_tables(txn: &TransactionRef, schema_name: &str) -> Res<(SchemaInfo, TableInfoIter)> {
  let schema = get_schema(&txn, schema_name)?;
  let mut set = get_system_tables(&txn)?;
  let iter = list_tables_internal(&mut set, &schema)?;
  Ok((schema, iter))
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
  let schema = get_schema(&txn, schema_name)?;
  assert_information_schema(&schema.schema_identifier)?;
  let table_identifier = to_valid_identifier(table_name)?;
  drop_table_internal(&txn, &schema, table_identifier, optional)
}

// Catalog API: Returns table data.
pub fn get_table_data(txn: &TransactionRef, table: &TableInfo) -> Option<Set> {
  get_set(&txn, &u64_u8!(table.table_id))
}

// Catalog API: Creates a new table data set.
// The method returns an error if the set already exists so use `get_table_data` to check first.
pub fn create_table_data(txn: &TransactionRef, table: &TableInfo) -> Res<Set> {
  create_set(&txn, &u64_u8!(table.table_id))
}

// Assert if the current schema is information schema.
// We don't allow any modifications in the information schema.
#[inline]
fn assert_information_schema(schema_identifier: &str) -> Res<()> {
  if schema_identifier == INFORMATION_SCHEMA {
    Err(Error::OperationIsNotAllowed(format!("Cannot modify {}", INFORMATION_SCHEMA)))
  } else {
    Ok(())
  }
}

#[inline]
fn create_schema_internal(
  txn: &TransactionRef,
  schema_identifier: String,
  optional: bool
) -> Res<()> {
  let mut set = get_system_schemas(&txn)?;
  if set.exists(&schema_identifier.as_bytes()) {
    if !optional {
      Err(Error::SchemaAlreadyExists(schema_identifier))
    } else {
      Ok(()) // the schema already exists
    }
  } else {
    let schema = SchemaInfo {
      schema_id: next_object_id(&txn),
      schema_identifier: schema_identifier
    };
    // Serialise to store in the set.
    let mut writer = Writer::new();
    schema.serialise(&mut writer);
    // Store in the sys table, the key must be the schema identifier.
    set.put(&schema.schema_identifier.as_bytes(), &writer.to_vec());
    Ok(())
  }
}

#[inline]
fn get_schema_internal(set: &Set, schema_identifier: String) -> Res<SchemaInfo> {
  match set.get(&schema_identifier.as_bytes()) {
    Some(data) => {
      let mut reader = Reader::from_buf(data);
      Ok(SchemaInfo::deserialise(&mut reader))
    },
    None => Err(Error::SchemaDoesNotExist(schema_identifier)),
  }
}

#[inline]
fn list_schemas_internal(set: &mut Set) -> Res<SchemaInfoIter> {
  let iter = set.list(None, None);
  Ok(SchemaInfoIter { iter })
}

// Iterator for `SchemaInfo`.
pub struct SchemaInfoIter {
  iter: BTreeIter,
}

impl Iterator for SchemaInfoIter {
  type Item = SchemaInfo;

  fn next(&mut self) -> Option<Self::Item> {
    match self.iter.next() {
      Some((_key, data)) => {
        let mut reader = Reader::from_buf(data);
        Some(SchemaInfo::deserialise(&mut reader))
      },
      None => None,
    }
  }
}

#[inline]
fn drop_schema_internal(
  txn: &TransactionRef,
  schema_identifier: String,
  cascade: bool,
  optional: bool
) -> Res<()> {
  let mut set = get_system_schemas(&txn)?;
  let schema = match get_schema_internal(&set, schema_identifier) {
    Ok(schema) => schema,
    Err(err) => {
      return if !optional { Err(err) } else { Ok(()) };
    },
  };

  // Drop all of the tables in the schema.
  let mut tables = Vec::new();
  {
    let mut table_set = get_system_tables(&txn)?;
    let mut iter = list_tables_internal(&mut table_set, &schema)?;
    while let Some(table) = iter.next() {
      // If the schema contains at least one table, we cannot drop it without "cascade" property.
      if !cascade {
        return Err(Error::SchemaIsNotEmpty(schema.schema_identifier));
      }
      tables.push(table)
    }
  }

  for table in tables {
    drop_table_internal(&txn, &schema, table.table_identifier, false)?;
  }

  // Drop the schema.
  set.del(schema.schema_identifier.as_bytes());
  Ok(())
}

#[inline]
fn create_table_internal(
  txn: &TransactionRef,
  schema: &SchemaInfo,
  table_identifier: String,
  table_type: TableType,
  table_fields: Fields,
  optional: bool
) -> Res<()> {
  let table_key = to_unique_table_key(schema.schema_id, &table_identifier);

  let mut set = get_system_tables(&txn)?;
  if set.exists(&table_key) {
    if !optional {
      Err(Error::TableAlreadyExists(schema.schema_identifier.to_string(), table_identifier))
    } else {
      Ok(()) // the table already exists
    }
  } else {
    let table = TableInfo {
      schema_id: schema.schema_id,
      table_id: next_object_id(&txn),
      table_identifier: table_identifier,
      table_type: table_type,
      table_fields: table_fields,
    };
    // Serialise to store in the set.
    let mut writer = Writer::new();
    table.serialise(&mut writer);
    // Store in the sys table, the key must be the "schema_id.table".
    set.put(&table_key, &writer.to_vec());
    Ok(())
  }
}

#[inline]
fn get_table_internal(set: &Set, schema: SchemaInfo, table_identifier: String) -> Res<(SchemaInfo, TableInfo)> {
  let table_key = to_unique_table_key(schema.schema_id, &table_identifier);
  match set.get(&table_key) {
    Some(data) => {
      let mut reader = Reader::from_buf(data);
      Ok((schema, TableInfo::deserialise(&mut reader)))
    },
    None => {
      Err(
        Error::TableDoesNotExist(
          schema.schema_identifier,
          table_identifier
        )
      )
    },
  }
}

#[inline]
fn list_tables_internal(set: &mut Set, schema: &SchemaInfo) -> Res<TableInfoIter> {
  // When listing, we use a dummy empty table name as the first key to locate the schema's tables.
  let start_table_key = to_unique_table_key(schema.schema_id, "");
  let iter = set.list(Some(&start_table_key), None);
  Ok(
    TableInfoIter {
      schema_id: schema.schema_id,
      iter: iter
    }
  )
}

// Iterator for `TableInfo`.
pub struct TableInfoIter {
  schema_id: u64,
  iter: BTreeIter,
}

impl Iterator for TableInfoIter {
  type Item = TableInfo;

  fn next(&mut self) -> Option<Self::Item> {
    match self.iter.next() {
      Some((_key, data)) => {
        let mut reader = Reader::from_buf(data);
        let table = TableInfo::deserialise(&mut reader);
        // We need to stop our search when the schema changes.
        if table.schema_id == self.schema_id {
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

#[inline]
fn drop_table_internal(
  txn: &TransactionRef,
  schema: &SchemaInfo,
  table_identifier: String,
  optional: bool
) -> Res<()> {
  let table_key = to_unique_table_key(schema.schema_id, &table_identifier);

  let mut set = get_system_tables(&txn)?;
  match set.get(&table_key) {
    Some(data) => {
      let mut reader = Reader::from_buf(data);
      let table = TableInfo::deserialise(&mut reader);
      // Delete the content of the table if it exists.
      if let Some(set) = get_set(&txn, &u64_u8!(table.table_id)) {
        drop_set(&txn, set);
      }
      // Delete table metadata.
      set.del(&table_key);
      Ok(())
    },
    None => {
      if !optional {
        Err(Error::TableDoesNotExist(schema.schema_identifier.to_string(), table_identifier))
      } else {
        Ok(())
      }
    },
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

  // Returns an empty schema for tests.
  fn empty_fields() -> Fields {
    Fields::new(vec![]).unwrap()
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
    fn serde(schema: &SchemaInfo) -> SchemaInfo {
      let mut writer = Writer::new();
      schema.serialise(&mut writer);
      let mut reader = Reader::from_buf(writer.to_vec());
      SchemaInfo::deserialise(&mut reader)
    }

    let schema = SchemaInfo { schema_id: 0, schema_identifier: String::from("") };
    assert_eq!(serde(&schema), schema);

    let schema = SchemaInfo { schema_id: 123, schema_identifier: String::from("ABC") };
    assert_eq!(serde(&schema), schema);
  }

  #[test]
  fn test_catalog_table_desc_serde() {
    fn serde(table: &TableInfo) -> TableInfo {
      let mut writer = Writer::new();
      table.serialise(&mut writer);
      let mut reader = Reader::from_buf(writer.to_vec());
      TableInfo::deserialise(&mut reader)
    }

    let table = TableInfo {
      schema_id: 0,
      table_id: 0,
      table_identifier: String::from(""),
      table_type: TableType::SYSTEM_VIEW,
      table_fields: empty_fields(),
    };
    assert_eq!(serde(&table), table);

    let table = TableInfo {
      schema_id: 123,
      table_id: 234,
      table_identifier: String::from("TEST"),
      table_type: TableType::TABLE,
      table_fields: Fields::new(
        vec![
          Field::new("c1", Type::INT, false).unwrap(),
          Field::new("c2", Type::TEXT, false).unwrap(),
          Field::new("c3", Type::STRUCT(empty_fields()), true).unwrap(),
        ]
      ).unwrap(),
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
      assert_eq!(schema.schema_id(), 0);
      assert_eq!(schema.schema_identifier(), INFORMATION_SCHEMA);

      let (schema, table) = get_table(&txn, INFORMATION_SCHEMA, "SCHEMATA").unwrap();
      assert_eq!(schema.schema_id(), 0);
      assert_eq!(schema.schema_identifier(), INFORMATION_SCHEMA);
      assert_eq!(table.table_id(), 1);
      assert_eq!(table.schema_id(), 0);
      assert_eq!(table.table_identifier(), "SCHEMATA");

      let (schema, table) = get_table(&txn, INFORMATION_SCHEMA, "TABLES").unwrap();
      assert_eq!(schema.schema_id(), 0);
      assert_eq!(schema.schema_identifier(), INFORMATION_SCHEMA);
      assert_eq!(table.table_id(), 2);
      assert_eq!(table.schema_id(), 0);
      assert_eq!(table.table_identifier(), "TABLES");
    });
  }

  #[test]
  fn test_catalog_information_schema_modification() {
    // The test verifies that we cannot create or drop a schema with INFORMATION_SCHEMA name.
    let err = Err(Error::OperationIsNotAllowed("Cannot modify INFORMATION_SCHEMA".to_string()));

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
        create_table(&txn, INFORMATION_SCHEMA, "test", empty_fields(), false),
        err
      );
      assert_eq!(
        create_table(&txn, INFORMATION_SCHEMA, "test", empty_fields(), true),
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
        Err(Error::SchemaAlreadyExists("TEST".to_string()))
      );
    });

    dbc.with_txn(true, |txn| {
      assert_eq!(
        create_schema(&txn, "TEST", false),
        Err(Error::SchemaAlreadyExists("TEST".to_string()))
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
      create_table(&txn, "test_schema", "table1", empty_fields(), false).unwrap();
      create_table(&txn, "test_schema", "table2", empty_fields(), false).unwrap();
      create_table(&txn, "test_schema", "table3", empty_fields(), false).unwrap();
    });

    // Drop schema with tables is not allowed.
    dbc.with_txn(true, |txn| {
      assert_eq!(
        drop_schema(&txn, "test_schema", false, false),
        Err(Error::SchemaIsNotEmpty("TEST_SCHEMA".to_string()))
      );
      assert_eq!(
        drop_schema(&txn, "test_schema", false, true /* optional */),
        Err(Error::SchemaIsNotEmpty("TEST_SCHEMA".to_string()))
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
        create_table(&txn, "test_schema", "table", empty_fields(), false),
        Err(Error::SchemaDoesNotExist("TEST_SCHEMA".to_string()))
      );
    });
  }

  #[test]
  fn test_catalog_create_table() {
    let mut dbc = init_db();

    // Create a new table.
    dbc.with_txn(true, |txn| {
      create_schema(&txn, "test_schema", false).unwrap();
      create_table(&txn, "test_schema", "table1", empty_fields(), false).unwrap();
    });
    dbc.with_txn(true, |txn| {
      let (schema, table) = get_table(&txn, "test_schema", "table1").unwrap();
      assert_eq!(schema.schema_id(), 3);
      assert_eq!(schema.schema_identifier(), "TEST_SCHEMA");
      assert_eq!(table.schema_id(), 3);
      assert_eq!(table.table_id(), 4);
      assert_eq!(table.table_identifier(), "TABLE1");
      assert_eq!(table.table_type(), TableType::TABLE);
    });

    // Create table with the same name.
    dbc.with_txn(true, |txn| {
      assert_eq!(
        create_table(&txn, "test_schema", "table1", empty_fields(), false),
        Err(Error::TableAlreadyExists("TEST_SCHEMA".to_string(), "TABLE1".to_string()))
      );
      assert_eq!(
        create_table(&txn, "test_schema", "table1", empty_fields(), true),
        Ok(())
      );
    });

    // Rollback - table should not be created.
    dbc.with_txn(false, |txn| {
      create_table(&txn, "test_schema", "table2", empty_fields(), false).unwrap();
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
      create_table(&txn, "test_schema", "table", empty_fields(), false).unwrap();
    });

    dbc.with_txn(true, |txn| {
      let (schema, table) = get_table(&txn, "test_schema", "table").unwrap();
      assert_eq!(schema.schema_id(), 3);
      assert_eq!(schema.schema_identifier(), "TEST_SCHEMA");
      assert_eq!(table.table_id(), 4);
      assert_eq!(table.schema_id(), 3);
      assert_eq!(table.table_identifier(), "TABLE");
      assert_eq!(table.table_type(), TableType::TABLE);
      assert_eq!(table.table_fields(), &empty_fields());
    });
  }

  #[test]
  fn test_catalog_list_tables() {
    let mut dbc = init_db();

    // Create different schemas and tables.
    dbc.with_txn(true, |txn| {
      create_schema(&txn, "schema1", false).unwrap();
      create_table(&txn, "schema1", "table1", empty_fields(), false).unwrap();
      create_table(&txn, "schema1", "table2", empty_fields(), false).unwrap();
      create_table(&txn, "schema1", "table3", empty_fields(), false).unwrap();

      create_schema(&txn, "schema2", false).unwrap();
      create_table(&txn, "schema2", "table4", empty_fields(), false).unwrap();
      create_table(&txn, "schema2", "table5", empty_fields(), false).unwrap();
      create_table(&txn, "schema2", "table6", empty_fields(), false).unwrap();
    });

    // Verify that we only return tables for the selected schema.
    dbc.with_txn(true, |txn| {
      let (schema, mut iter) = list_tables(&txn, "schema1").unwrap();
      assert_eq!(schema.schema_identifier(), "SCHEMA1");
      assert_eq!(iter.next().unwrap().table_identifier(), "TABLE1");
      assert_eq!(iter.next().unwrap().table_identifier(), "TABLE2");
      assert_eq!(iter.next().unwrap().table_identifier(), "TABLE3");
      assert_eq!(iter.next(), None);

      let (schema, mut iter) = list_tables(&txn, "schema2").unwrap();
      assert_eq!(schema.schema_identifier(), "SCHEMA2");
      assert_eq!(iter.next().unwrap().table_identifier(), "TABLE4");
      assert_eq!(iter.next().unwrap().table_identifier(), "TABLE5");
      assert_eq!(iter.next().unwrap().table_identifier(), "TABLE6");
      assert_eq!(iter.next(), None);

      let (schema, mut iter) = list_tables(&txn, INFORMATION_SCHEMA).unwrap();
      assert_eq!(schema.schema_identifier(), INFORMATION_SCHEMA);
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
      create_table(&txn, "schema", "table1", empty_fields(), false).unwrap();
      drop_table(&txn, "schema", "table1", false).unwrap();
      assert!(get_table(&txn, "schema", "table1").is_err());
    });

    // Drop table in a separate transaction.
    dbc.with_txn(true, |txn| {
      create_table(&txn, "schema", "table2", empty_fields(), false).unwrap();
    });
    dbc.with_txn(true, |txn| {
      drop_table(&txn, "schema", "table2", false).unwrap();
      assert!(get_table(&txn, "schema", "table2").is_err());
    });

    // Drop table - table does not exist.
    dbc.with_txn(true, |txn| {
      assert_eq!(
        drop_table(&txn, "schema", "table3", false),
        Err(Error::TableDoesNotExist("SCHEMA".to_string(), "TABLE3".to_string()))
      );
      assert_eq!(drop_table(&txn, "schema", "table3", true), Ok(()));
    });

    // Rollback - table is not dropped.
    dbc.with_txn(true, |txn| {
      create_table(&txn, "schema", "table4", empty_fields(), false).unwrap();
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

  #[test]
  fn test_catalog_table_data() {
    let mut dbc = init_db();

    // Setup.
    dbc.with_txn(true, |txn| {
      create_schema(&txn, "schema", false).unwrap();
      create_table(&txn, "schema", "table", empty_fields(), false).unwrap();
    });

    // Newly created table should not have a set.
    dbc.with_txn(true, |txn| {
      let (_, info) = get_table(&txn, "schema", "table").unwrap();
      let set = get_table_data(&txn, &info);
      assert!(set.is_none());
    });

    // Create a set for a table.
    dbc.with_txn(true, |txn| {
      let (_, info) = get_table(&txn, "schema", "table").unwrap();
      let set = create_table_data(&txn, &info);
      assert!(set.is_ok());

      // Set exists in the transaction.
      let mut set = get_table_data(&txn, &info).unwrap();
      set.put(&[1], &[2]);
    });

    // Get the set for an existing table.
    dbc.with_txn(true, |txn| {
      let (_, info) = get_table(&txn, "schema", "table").unwrap();
      let set = get_table_data(&txn, &info);
      assert!(set.is_some());
    });
  }
}
