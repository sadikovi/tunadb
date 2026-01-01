use crate::common::error::{Error, Res};
use crate::common::serde::{Reader, SerDe, Writer};
use crate::exec::types::{Field, Fields, Type};
use crate::storage::btree::BTreeIter;
use crate::storage::txn::{Set, TransactionRef, create_set, drop_set, get_set, next_object_id};

// Returns a unique relation key to store in the set.
// This allows us to locate a relation using "exists" and "get" API while still being able to
// rename the schema.
#[inline]
fn to_unique_relation_key(schema_id: u64, relation_name: &str) -> Vec<u8> {
  let id_bytes = &u64_u8!(schema_id);
  let ident_bytes = relation_name.as_bytes();
  let mut key = Vec::with_capacity(id_bytes.len() + ident_bytes.len());
  key.extend_from_slice(id_bytes);
  key.extend_from_slice(ident_bytes);
  key
}

// Relation type to differentiate between base tables, views, etc.
#[derive(Clone, Copy, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum RelationType {
  TABLE /* 1 */,
  SYSTEM_VIEW /* 2 */,
}

impl SerDe for RelationType {
  fn serialise(&self, writer: &mut Writer) {
    match self {
      RelationType::TABLE => writer.write_u8(1),
      RelationType::SYSTEM_VIEW => writer.write_u8(2),
    }
  }

  fn deserialise(reader: &mut Reader) -> Self {
    match reader.read_u8() {
      1 => RelationType::TABLE,
      2 => RelationType::SYSTEM_VIEW,
      _ => unreachable!(),
    }
  }
}

#[derive(Debug, PartialEq)]
pub struct SchemaInfo {
  schema_id: u64, // globally unique id
  schema_name: String,
}

impl SchemaInfo {
  // Returns globally unique object id for the schema.
  #[inline]
  pub fn schema_id(&self) -> u64 {
    self.schema_id
  }

  // Returns the schema name.
  #[inline]
  pub fn schema_name(&self) -> &str {
    &self.schema_name
  }

  // Returns schema name consuming SchemaInfo.
  #[inline]
  pub fn into_schema_name(self) -> String {
    self.schema_name
  }
}

impl SerDe for SchemaInfo {
  fn serialise(&self, writer: &mut Writer) {
    writer.write_u64(self.schema_id);
    writer.write_str(&self.schema_name);
  }

  fn deserialise(reader: &mut Reader) -> Self {
    let schema_id = reader.read_u64();
    let schema_name = reader.read_str().to_string();
    Self { schema_id, schema_name }
  }
}

// Private struct that is used for serialisation/deserialisation.
// We do not store schema identifier since it can change while schema id is unique.
#[derive(Debug, PartialEq)]
pub struct RelationInfo {
  schema_id: u64, // globally unique id
  relation_id: u64, // globally unique id
  relation_name: String, // unique within the schema
  relation_type: RelationType,
  relation_fields: Fields,
}

impl RelationInfo {
  // Returns globally unique id for the schema.
  #[inline]
  pub fn schema_id(&self) -> u64 {
    self.schema_id
  }

  // Returns globally unique id for the relation.
  #[inline]
  pub fn relation_id(&self) -> u64 {
    self.relation_id
  }

  // Returns the relation name.
  #[inline]
  pub fn relation_name(&self) -> &str {
    &self.relation_name
  }

  // Returns the relation type.
  #[inline]
  pub fn relation_type(&self) -> RelationType {
    self.relation_type
  }

  // Returns the relation fields/schema.
  #[inline]
  pub fn relation_fields(&self) -> &Fields {
    &self.relation_fields
  }

  // Returns relation name consuming RelationInfo.
  #[inline]
  pub fn into_relation_name(self) -> String {
    self.relation_name
  }
}

impl SerDe for RelationInfo {
  fn serialise(&self, writer: &mut Writer) {
    writer.write_u64(self.schema_id);
    writer.write_u64(self.relation_id);
    writer.write_str(&self.relation_name);
    self.relation_type.serialise(writer);
    self.relation_fields.serialise(writer);
  }

  fn deserialise(reader: &mut Reader) -> Self {
    let schema_id = reader.read_u64();
    let relation_id = reader.read_u64();
    let relation_name = reader.read_str().to_string();
    let relation_type = RelationType::deserialise(reader);
    let relation_fields = Fields::deserialise(reader);
    Self { schema_id, relation_id, relation_name, relation_type, relation_fields }
  }
}

//===================================================================================
// System sets.
// IDs must be longer than 8 bytes to avoid collision with object ids which are u64.
//===================================================================================

// Schema information.
const SYSTEM_SCHEMAS: &[u8] = b"SYSTEM_SCHEMAS";
// Relation information.
const SYSTEM_RELATIONS: &[u8] = b"SYSTEM_RELATIONS";

// Helper method to get SYSTEM_SCHEMAS.
#[inline]
fn get_system_schemas(txn: &TransactionRef) -> Res<Set> {
  match get_set(&txn, SYSTEM_SCHEMAS) {
    Some(set) => Ok(set),
    None => Err(internal_err!("SYSTEM_SCHEMAS does not exist")),
  }
}

// Helper method to get SYSTEM_RELATIONS.
#[inline]
fn get_system_relations(txn: &TransactionRef) -> Res<Set> {
  match get_set(&txn, SYSTEM_RELATIONS) {
    Some(set) => Ok(set),
    None => Err(internal_err!("SYSTEM_RELATIONS does not exist")),
  }
}

//=============
// Catalog API
//=============

const INFORMATION_SCHEMA: &str = "INFORMATION_SCHEMA";

// Initialise catalog and system relations.
// This method must only be called once during the database setup.
pub fn init_catalog(txn: &TransactionRef) -> Res<()> {
  create_set(&txn, SYSTEM_SCHEMAS)?;
  create_set(&txn, SYSTEM_RELATIONS)?;

  create_schema_internal(&txn, INFORMATION_SCHEMA, false)?;
  let schema = get_schema(&txn, INFORMATION_SCHEMA)?;

  create_relation_internal(
    &txn,
    &schema,
    "SCHEMATA",
    RelationType::SYSTEM_VIEW,
    Fields::new(
      vec![
        Field::new("SCHEMA_NAME".to_string(), Type::TEXT, false),
      ]
    ),
    false
  )?;

  create_relation_internal(
    &txn,
    &schema,
    "RELATIONS",
    RelationType::SYSTEM_VIEW,
    Fields::new(
      vec![
        Field::new("RELATION_SCHEMA".to_string(), Type::TEXT, false),
        Field::new("RELATION_NAME".to_string(), Type::TEXT, false),
        Field::new("RELATION_TYPE".to_string(), Type::TEXT, false),
      ]
    ),
    false
  )?;

  Ok(())
}

// Catalog API: Creates schema with the provided name.
// When `optional` is set to true, ignores the operation if the schema already exists.
pub fn create_schema(txn: &TransactionRef, schema_name: &str, optional: bool) -> Res<()> {
  assert_information_schema(&schema_name)?;
  create_schema_internal(&txn, &schema_name, optional)
}

 // Catalog API: Returns schema info for the name if exists.
pub fn get_schema(txn: &TransactionRef, schema_name: &str) -> Res<SchemaInfo> {
  let set = get_system_schemas(&txn)?;
  get_schema_internal(&set, &schema_name)
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
  assert_information_schema(&schema_name)?;
  drop_schema_internal(&txn, &schema_name, cascade, optional)
}

// Catalog API: Creates a relation with the provided schema name and relation name.
// The schema must exist.
// If `optional` is set to true, the operation is ignored if the relation already exists.
pub fn create_relation(
  txn: &TransactionRef,
  schema_name: &str,
  relation_name: &str,
  relation_type: RelationType,
  relation_fields: Fields,
  optional: bool
) -> Res<()> {
  assert_information_schema(&schema_name)?;
  let schema = get_schema(&txn, &schema_name)?;
  create_relation_internal(
    &txn,
    &schema,
    &relation_name,
    relation_type,
    relation_fields,
    optional
  )
}

// Catalog API: Returns the schema and relation info for "schema.relation".
pub fn get_relation(
  txn: &TransactionRef,
  schema_name: &str,
  relation_name: &str
) -> Res<(SchemaInfo, RelationInfo)> {
  let schema = get_schema(&txn, &schema_name)?;
  let set = get_system_relations(&txn)?;
  get_relation_internal(&set, schema, relation_name)
}

// Catalog API: Returns the list of all relations in the provided schema.
pub fn list_relations(
  txn: &TransactionRef,
  schema_name: &str
) -> Res<(SchemaInfo, RelationInfoIter)> {
  let schema = get_schema(&txn, schema_name)?;
  let mut set = get_system_relations(&txn)?;
  let iter = list_relations_internal(&mut set, &schema)?;
  Ok((schema, iter))
}

// Catalog API: Drops a relation for the provided schema and relation names.
// The schema must exist.
// If `optional` is set to true, the operation is ignored if the relation does not exist.
pub fn drop_relation(
  txn: &TransactionRef,
  schema_name: &str,
  relation_name: &str,
  optional: bool
) -> Res<()> {
  assert_information_schema(&schema_name)?;
  let schema = get_schema(&txn, &schema_name)?;
  drop_relation_internal(&txn, &schema, &relation_name, optional)
}

// Catalog API: Returns relation data.
pub fn get_relation_data(txn: &TransactionRef, relation: &RelationInfo) -> Option<Set> {
  get_set(&txn, &u64_u8!(relation.relation_id))
}

// Catalog API: Creates a new relation data set.
// The method returns an error if the set already exists so use `get_relation_data` to check first.
pub fn create_relation_data(txn: &TransactionRef, relation: &RelationInfo) -> Res<Set> {
  create_set(&txn, &u64_u8!(relation.relation_id))
}

// Assert if the current schema is information schema.
// We don't allow any modifications in the information schema.
#[inline]
fn assert_information_schema(schema_name: &str) -> Res<()> {
  if schema_name.eq_ignore_ascii_case(INFORMATION_SCHEMA) {
    Err(Error::OperationIsNotAllowed(format!("Cannot modify {}", INFORMATION_SCHEMA)))
  } else {
    Ok(())
  }
}

#[inline]
fn create_schema_internal(
  txn: &TransactionRef,
  schema_name: &str,
  optional: bool
) -> Res<()> {
  let mut set = get_system_schemas(&txn)?;
  if set.exists(&schema_name.as_bytes()) {
    if !optional {
      Err(Error::SchemaAlreadyExists(schema_name.to_string()))
    } else {
      Ok(()) // the schema already exists
    }
  } else {
    let schema = SchemaInfo {
      schema_id: next_object_id(&txn),
      schema_name: schema_name.to_string(),
    };
    // Serialise to store in the set.
    let mut writer = Writer::new();
    schema.serialise(&mut writer);
    // The key must be the schema identifier.
    set.put(&schema.schema_name.as_bytes(), &writer.to_vec());
    Ok(())
  }
}

#[inline]
fn get_schema_internal(set: &Set, schema_name: &str) -> Res<SchemaInfo> {
  match set.get(&schema_name.as_bytes()) {
    Some(data) => {
      let mut reader = Reader::from_buf(data);
      Ok(SchemaInfo::deserialise(&mut reader))
    },
    None => Err(Error::SchemaDoesNotExist(schema_name.to_string())),
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
  schema_name: &str,
  cascade: bool,
  optional: bool
) -> Res<()> {
  let mut set = get_system_schemas(&txn)?;
  let schema = match get_schema_internal(&set, &schema_name) {
    Ok(schema) => schema,
    Err(err) => {
      return if !optional { Err(err) } else { Ok(()) };
    },
  };

  // Drop all of the tables in the schema.
  let mut relations = Vec::new();
  {
    let mut relation_set = get_system_relations(&txn)?;
    let mut iter = list_relations_internal(&mut relation_set, &schema)?;
    while let Some(relation) = iter.next() {
      // If the schema contains at least one relation, we cannot drop it without "cascade".
      if !cascade {
        return Err(Error::SchemaIsNotEmpty(schema.into_schema_name()));
      }
      relations.push(relation)
    }
  }

  for relation in relations {
    drop_relation_internal(&txn, &schema, relation.relation_name(), false)?;
  }

  // Drop the schema.
  set.del(schema.schema_name.as_bytes());
  Ok(())
}

#[inline]
fn create_relation_internal(
  txn: &TransactionRef,
  schema: &SchemaInfo,
  relation_name: &str,
  relation_type: RelationType,
  relation_fields: Fields,
  optional: bool
) -> Res<()> {
  let relation_key = to_unique_relation_key(schema.schema_id, &relation_name);

  let mut set = get_system_relations(&txn)?;
  if set.exists(&relation_key) {
    if !optional {
      Err(
        Error::RelationAlreadyExists(schema.schema_name().to_string(), relation_name.to_string())
      )
    } else {
      Ok(()) // the relation already exists
    }
  } else {
    let relation = RelationInfo {
      schema_id: schema.schema_id,
      relation_id: next_object_id(&txn),
      relation_name: relation_name.to_string(),
      relation_type: relation_type,
      relation_fields: relation_fields,
    };
    // Serialise to store in the set.
    let mut writer = Writer::new();
    relation.serialise(&mut writer);
    set.put(&relation_key, &writer.to_vec());
    Ok(())
  }
}

#[inline]
fn get_relation_internal(
  set: &Set,
  schema: SchemaInfo,
  relation_name: &str
) -> Res<(SchemaInfo, RelationInfo)> {
  let relation_key = to_unique_relation_key(schema.schema_id, &relation_name);
  match set.get(&relation_key) {
    Some(data) => {
      let mut reader = Reader::from_buf(data);
      Ok((schema, RelationInfo::deserialise(&mut reader)))
    },
    None => {
      Err(Error::RelationDoesNotExist(schema.into_schema_name(), relation_name.to_string()))
    },
  }
}

#[inline]
fn list_relations_internal(set: &mut Set, schema: &SchemaInfo) -> Res<RelationInfoIter> {
  // We use a dummy empty relation name as the first key to locate the schema's relations.
  let start_key = to_unique_relation_key(schema.schema_id, "");
  let iter = set.list(Some(&start_key), None);
  Ok(
    RelationInfoIter {
      schema_id: schema.schema_id,
      iter: iter
    }
  )
}

// Iterator for `RelationInfo`.
pub struct RelationInfoIter {
  schema_id: u64,
  iter: BTreeIter,
}

impl Iterator for RelationInfoIter {
  type Item = RelationInfo;

  fn next(&mut self) -> Option<Self::Item> {
    match self.iter.next() {
      Some((_key, data)) => {
        let mut reader = Reader::from_buf(data);
        let relation = RelationInfo::deserialise(&mut reader);
        // We need to stop our search when the schema changes.
        if relation.schema_id == self.schema_id {
          Some(relation)
        } else {
          // We have seen all of the relations with this schema id.
          None
        }
      },
      None => None,
    }
  }
}

#[inline]
fn drop_relation_internal(
  txn: &TransactionRef,
  schema: &SchemaInfo,
  relation_name: &str,
  optional: bool
) -> Res<()> {
  let relation_key = to_unique_relation_key(schema.schema_id, &relation_name);

  let mut set = get_system_relations(&txn)?;
  match set.get(&relation_key) {
    Some(data) => {
      let mut reader = Reader::from_buf(data);
      let relation = RelationInfo::deserialise(&mut reader);
      // Delete the content of the relation if it exists.
      if let Some(set) = get_set(&txn, &u64_u8!(relation.relation_id)) {
        drop_set(&txn, set);
      }
      // Delete relation metadata.
      set.del(&relation_key);
      Ok(())
    },
    None => {
      if !optional {
        Err(
          Error::RelationDoesNotExist(schema.schema_name().to_string(), relation_name.to_string())
        )
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
    Fields::new(vec![])
  }

  #[test]
  fn test_catalog_to_unique_relation_key() {
    assert_eq!(to_unique_relation_key(0, ""), vec![0, 0, 0, 0, 0, 0, 0, 0]);
    assert_eq!(to_unique_relation_key(1, ""), vec![1, 0, 0, 0, 0, 0, 0, 0]);
    assert_eq!(to_unique_relation_key(1, "1"), vec![1, 0, 0, 0, 0, 0, 0, 0, 49]);
    assert_eq!(to_unique_relation_key(128, "abc"), vec![128, 0, 0, 0, 0, 0, 0, 0, 97, 98, 99]);
  }

  #[test]
  fn test_catalog_table_type_serde() {
    fn serde(tpe: RelationType) -> RelationType {
      let mut writer = Writer::new();
      tpe.serialise(&mut writer);
      let mut reader = Reader::from_buf(writer.to_vec());
      RelationType::deserialise(&mut reader)
    }

    assert_eq!(serde(RelationType::TABLE), RelationType::TABLE);
    assert_eq!(serde(RelationType::SYSTEM_VIEW), RelationType::SYSTEM_VIEW);
  }

  #[test]
  fn test_catalog_schema_desc_serde() {
    fn serde(schema: &SchemaInfo) -> SchemaInfo {
      let mut writer = Writer::new();
      schema.serialise(&mut writer);
      let mut reader = Reader::from_buf(writer.to_vec());
      SchemaInfo::deserialise(&mut reader)
    }

    let schema = SchemaInfo { schema_id: 0, schema_name: String::from("") };
    assert_eq!(serde(&schema), schema);

    let schema = SchemaInfo { schema_id: 123, schema_name: String::from("ABC") };
    assert_eq!(serde(&schema), schema);
  }

  #[test]
  fn test_catalog_table_desc_serde() {
    fn serde(relation: &RelationInfo) -> RelationInfo {
      let mut writer = Writer::new();
      relation.serialise(&mut writer);
      let mut reader = Reader::from_buf(writer.to_vec());
      RelationInfo::deserialise(&mut reader)
    }

    let relation = RelationInfo {
      schema_id: 0,
      relation_id: 0,
      relation_name: String::from(""),
      relation_type: RelationType::SYSTEM_VIEW,
      relation_fields: empty_fields(),
    };
    assert_eq!(serde(&relation), relation);

    let relation = RelationInfo {
      schema_id: 123,
      relation_id: 234,
      relation_name: String::from("TEST"),
      relation_type: RelationType::TABLE,
      relation_fields: Fields::new(
        vec![
          Field::new("c1".to_string(), Type::INT, false),
          Field::new("c2".to_string(), Type::TEXT, false),
          Field::new("c3".to_string(), Type::STRUCT(empty_fields()), true),
        ]
      ),
    };
    assert_eq!(serde(&relation), relation);
  }

  #[test]
  fn test_catalog_check_sys_tables_length() {
    assert!(SYSTEM_SCHEMAS.len() > 8);
    assert!(SYSTEM_RELATIONS.len() > 8);
  }

  #[test]
  fn test_catalog_init_catalog() {
    let mut dbc = db::open(None).try_build().unwrap();
    dbc.with_txn(true, |txn| {
      init_catalog(&txn).unwrap();
    });

    // All system relations must be created.
    dbc.with_txn(true, |txn| {
      let schema = get_schema(&txn, INFORMATION_SCHEMA).unwrap();
      assert_eq!(schema.schema_id(), 0);
      assert_eq!(schema.schema_name(), INFORMATION_SCHEMA);

      let (schema, relation) = get_relation(&txn, INFORMATION_SCHEMA, "SCHEMATA").unwrap();
      assert_eq!(schema.schema_id(), 0);
      assert_eq!(schema.schema_name(), INFORMATION_SCHEMA);
      assert_eq!(relation.relation_id(), 1);
      assert_eq!(relation.schema_id(), 0);
      assert_eq!(relation.relation_name(), "SCHEMATA");

      let (schema, relation) = get_relation(&txn, INFORMATION_SCHEMA, "RELATIONS").unwrap();
      assert_eq!(schema.schema_id(), 0);
      assert_eq!(schema.schema_name(), INFORMATION_SCHEMA);
      assert_eq!(relation.relation_id(), 2);
      assert_eq!(relation.schema_id(), 0);
      assert_eq!(relation.relation_name(), "RELATIONS");
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
        create_relation(
          &txn,
          INFORMATION_SCHEMA,
          "test",
          RelationType::TABLE,
          empty_fields(),
          false
        ),
        err
      );
      assert_eq!(
        create_relation(
          &txn,
          INFORMATION_SCHEMA,
          "test",
          RelationType::TABLE,
          empty_fields(),
          true
        ),
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
        if desc.schema_name() != INFORMATION_SCHEMA {
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
      assert_eq!(schema.schema_name(), "test1");

      let schema = get_schema(&txn, "test2").unwrap();
      assert_eq!(schema.schema_name(), "test2");

      let schema = get_schema(&txn, "test3").unwrap();
      assert_eq!(schema.schema_name(), "test3");

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
      create_relation(&txn, "test_schema", "table1", RelationType::TABLE, empty_fields(), false)
        .unwrap();
      create_relation(&txn, "test_schema", "table2", RelationType::TABLE, empty_fields(), false)
        .unwrap();
      create_relation(&txn, "test_schema", "table3", RelationType::TABLE, empty_fields(), false)
        .unwrap();
    });

    // Drop schema with tables is not allowed.
    dbc.with_txn(true, |txn| {
      assert_eq!(
        drop_schema(&txn, "test_schema", false, false),
        Err(Error::SchemaIsNotEmpty("test_schema".to_string()))
      );
      assert_eq!(
        drop_schema(&txn, "test_schema", false, true /* optional */),
        Err(Error::SchemaIsNotEmpty("test_schema".to_string()))
      );
    });

    // Drop schema with cascade should drop the tables.
    dbc.with_txn(true, |txn| {
      drop_schema(&txn, "test_schema", true, false).unwrap();
      assert!(get_schema(&txn, "test_schema").is_err());
    });
    dbc.with_txn(true, |txn| {
      // Only INFORMATION_SCHEMA relations must be present.
      let mut set = get_system_relations(&txn).unwrap();
      let mut iter = set.list(None, None);
      assert_eq!(iter.next().unwrap().0, to_unique_relation_key(0, "RELATIONS"));
      assert_eq!(iter.next().unwrap().0, to_unique_relation_key(0, "SCHEMATA"));
      assert_eq!(iter.next(), None);
    });
  }

  #[test]
  fn test_catalog_create_table_schema_does_not_exist() {
    let mut dbc = init_db();

    dbc.with_txn(true, |txn| {
      assert_eq!(
        create_relation(&txn, "test_schema", "table", RelationType::TABLE, empty_fields(), false),
        Err(Error::SchemaDoesNotExist("test_schema".to_string()))
      );
    });
  }

  #[test]
  fn test_catalog_create_table() {
    let mut dbc = init_db();

    // Create a new relation.
    dbc.with_txn(true, |txn| {
      create_schema(&txn, "test_schema", false).unwrap();
      create_relation(&txn, "test_schema", "table1", RelationType::TABLE, empty_fields(), false)
        .unwrap();
    });
    dbc.with_txn(true, |txn| {
      let (schema, relation) = get_relation(&txn, "test_schema", "table1").unwrap();
      assert_eq!(schema.schema_id(), 3);
      assert_eq!(schema.schema_name(), "test_schema");
      assert_eq!(relation.schema_id(), 3);
      assert_eq!(relation.relation_id(), 4);
      assert_eq!(relation.relation_name(), "table1");
      assert_eq!(relation.relation_type(), RelationType::TABLE);
    });

    // Create relation with the same name.
    dbc.with_txn(true, |txn| {
      assert_eq!(
        create_relation(&txn, "test_schema", "table1", RelationType::TABLE, empty_fields(), false),
        Err(Error::RelationAlreadyExists("test_schema".to_string(), "table1".to_string()))
      );
      assert_eq!(
        create_relation(&txn, "test_schema", "table1", RelationType::TABLE, empty_fields(), true),
        Ok(())
      );
    });

    // Rollback - relation should not be created.
    dbc.with_txn(false, |txn| {
      create_relation(&txn, "test_schema", "table2", RelationType::TABLE, empty_fields(), false)
        .unwrap();
      assert!(get_relation(&txn, "test_schema", "table2").is_ok());
      txn.borrow_mut().rollback();
    });
    dbc.with_txn(true, |txn| {
      assert!(get_relation(&txn, "test_schema", "table2").is_err());
    });
  }

  #[test]
  fn test_catalog_get_table() {
    let mut dbc = init_db();

    dbc.with_txn(true, |txn| {
      create_schema(&txn, "test_schema", false).unwrap();
      create_relation(&txn, "test_schema", "table", RelationType::TABLE, empty_fields(), false)
        .unwrap();
    });

    dbc.with_txn(true, |txn| {
      let (schema, relation) = get_relation(&txn, "test_schema", "table").unwrap();
      assert_eq!(schema.schema_id(), 3);
      assert_eq!(schema.schema_name(), "test_schema");
      assert_eq!(relation.relation_id(), 4);
      assert_eq!(relation.schema_id(), 3);
      assert_eq!(relation.relation_name(), "table");
      assert_eq!(relation.relation_type(), RelationType::TABLE);
      assert_eq!(relation.relation_fields(), &empty_fields());
    });
  }

  #[test]
  fn test_catalog_list_tables() {
    let mut dbc = init_db();

    // Create different schemas and tables.
    dbc.with_txn(true, |txn| {
      create_schema(&txn, "schema1", false).unwrap();
      create_relation(&txn, "schema1", "table1", RelationType::TABLE, empty_fields(), false)
        .unwrap();
      create_relation(&txn, "schema1", "table2", RelationType::TABLE, empty_fields(), false)
        .unwrap();
      create_relation(&txn, "schema1", "table3", RelationType::TABLE, empty_fields(), false)
        .unwrap();

      create_schema(&txn, "schema2", false).unwrap();
      create_relation(&txn, "schema2", "table4", RelationType::TABLE, empty_fields(), false)
        .unwrap();
      create_relation(&txn, "schema2", "table5", RelationType::TABLE, empty_fields(), false)
        .unwrap();
      create_relation(&txn, "schema2", "table6", RelationType::TABLE, empty_fields(), false)
        .unwrap();
    });

    // Verify that we only return tables for the selected schema.
    dbc.with_txn(true, |txn| {
      let (schema, mut iter) = list_relations(&txn, "schema1").unwrap();
      assert_eq!(schema.schema_name(), "schema1");
      assert_eq!(iter.next().unwrap().relation_name(), "table1");
      assert_eq!(iter.next().unwrap().relation_name(), "table2");
      assert_eq!(iter.next().unwrap().relation_name(), "table3");
      assert_eq!(iter.next(), None);

      let (schema, mut iter) = list_relations(&txn, "schema2").unwrap();
      assert_eq!(schema.schema_name(), "schema2");
      assert_eq!(iter.next().unwrap().relation_name(), "table4");
      assert_eq!(iter.next().unwrap().relation_name(), "table5");
      assert_eq!(iter.next().unwrap().relation_name(), "table6");
      assert_eq!(iter.next(), None);

      let (schema, mut iter) = list_relations(&txn, INFORMATION_SCHEMA).unwrap();
      assert_eq!(schema.schema_name(), INFORMATION_SCHEMA);
      assert_eq!(iter.next().unwrap().relation_name(), "RELATIONS");
      assert_eq!(iter.next().unwrap().relation_name(), "SCHEMATA");
      assert_eq!(iter.next(), None);
    });
  }

  #[test]
  fn test_catalog_drop_table() {
    let mut dbc = init_db();

    dbc.with_txn(true, |txn| {
      create_schema(&txn, "schema", false).unwrap();
    });

    // Drop relation in the same transaction.
    dbc.with_txn(true, |txn| {
      create_relation(&txn, "schema", "table1", RelationType::TABLE, empty_fields(), false)
        .unwrap();
      drop_relation(&txn, "schema", "table1", false).unwrap();
      assert!(get_relation(&txn, "schema", "table1").is_err());
    });

    // Drop relation in a separate transaction.
    dbc.with_txn(true, |txn| {
      create_relation(&txn, "schema", "table2", RelationType::TABLE, empty_fields(), false)
        .unwrap();
    });
    dbc.with_txn(true, |txn| {
      drop_relation(&txn, "schema", "table2", false).unwrap();
      assert!(get_relation(&txn, "schema", "table2").is_err());
    });

    // Drop relation - relation does not exist.
    dbc.with_txn(true, |txn| {
      assert_eq!(
        drop_relation(&txn, "schema", "table3", false),
        Err(Error::RelationDoesNotExist("schema".to_string(), "table3".to_string()))
      );
      assert_eq!(drop_relation(&txn, "schema", "table3", true), Ok(()));
    });

    // Rollback - relation is not dropped.
    dbc.with_txn(true, |txn| {
      create_relation(&txn, "schema", "table4", RelationType::TABLE, empty_fields(), false)
        .unwrap();
    });
    dbc.with_txn(false, |txn| {
      drop_relation(&txn, "schema", "table4", false).unwrap();
      assert!(get_relation(&txn, "schema", "table4").is_err());
      txn.borrow_mut().rollback();
    });
    dbc.with_txn(true, |txn| {
      assert!(get_relation(&txn, "schema", "table4").is_ok());
    });
  }

  #[test]
  fn test_catalog_table_data() {
    let mut dbc = init_db();

    // Setup.
    dbc.with_txn(true, |txn| {
      create_schema(&txn, "schema", false).unwrap();
      create_relation(&txn, "schema", "table", RelationType::TABLE, empty_fields(), false)
        .unwrap();
    });

    // Newly created relation should not have a set.
    dbc.with_txn(true, |txn| {
      let (_, info) = get_relation(&txn, "schema", "table").unwrap();
      let set = get_relation_data(&txn, &info);
      assert!(set.is_none());
    });

    // Create a set for a relation.
    dbc.with_txn(true, |txn| {
      let (_, info) = get_relation(&txn, "schema", "table").unwrap();
      let set = create_relation_data(&txn, &info);
      assert!(set.is_ok());

      // Set exists in the transaction.
      let mut set = get_relation_data(&txn, &info).unwrap();
      set.put(&[1], &[2]);
    });

    // Get the set for an existing relation.
    dbc.with_txn(true, |txn| {
      let (_, info) = get_relation(&txn, "schema", "table").unwrap();
      let set = get_relation_data(&txn, &info);
      assert!(set.is_some());
    });
  }
}
