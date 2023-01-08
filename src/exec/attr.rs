use std::rc::Rc;
use crate::common::error::Res;
use crate::common::row::Row;
use crate::common::trees::TreeNode;
use crate::common::types::{Field, Type};
use crate::common::util::to_valid_identifier;

// Creates a new alias for the provided attribute.
pub fn alias(child: Attribute, name: &str) -> Res<Attribute> {
  let name = to_valid_identifier(name)?;
  Ok(Attribute::Alias { child: vec![child], name: Rc::new(name) })
}

// Literal value for INT type.
pub fn lit_int(value: i32) -> Res<Attribute> {
  Ok(Attribute::LiteralInt(value))
}

// Creates a new field reference.
pub fn reference(field: &Field, ord: usize) -> Res<Attribute> {
  Ok(
    Attribute::Reference {
      ord: ord,
      name: Rc::new(field.name().to_string()),
      tpe: Rc::new(field.data_type().clone()),
      nullable: field.nullable()
    }
  )
}

#[derive(Clone, Debug, PartialEq)]
pub enum Attribute {
  Alias { child: Vec<Attribute>, name: Rc<String> },
  LiteralInt(i32),
  Reference { ord: usize, name: Rc<String>, tpe: Rc<Type>, nullable: bool },
}

impl Attribute {
  // Field name that the attribute points to.
  #[inline]
  pub fn name(&self) -> &str {
    match self {
      Attribute::Alias { ref name, .. } => name,
      Attribute::LiteralInt(_) => "LITERAL",
      Attribute::Reference { ref name, .. } => name,
    }
  }

  // Data type for the attribute.
  #[inline]
  pub fn data_type(&self) -> &Type {
    match self {
      Attribute::Alias { ref child, .. } => child[0].data_type(),
      Attribute::LiteralInt(_) => &Type::INT,
      Attribute::Reference { ref tpe, .. } => tpe,
    }
  }

  // Returns true if the attribute is nullable.
  #[inline]
  pub fn nullable(&self) -> bool {
    match self {
      Attribute::Alias { ref child, .. } => child[0].nullable(),
      Attribute::LiteralInt(_) => false,
      Attribute::Reference { nullable, .. } => *nullable,
    }
  }

  // Evaluates the value of the attribute based on the input row.
  // The result is written to the output row.
  // If `allow_nulls` is true, then we allow setting null if the attribute is nullable.
  #[inline]
  pub fn eval(&self, inp: &Row, out: &mut Row, idx: usize, allow_nulls: bool) -> Res<()> {
    match self {
      Attribute::Alias { ref child, .. } => child[0].eval(inp, out, idx, allow_nulls),
      Attribute::LiteralInt(v) => {
        out.set_i32(idx, *v);
        Ok(())
      },
      Attribute::Reference { ord, tpe, nullable, .. } => {
        if inp.is_null(*ord) {
          assert!(*nullable, "Value is null at pos {} for a non-nullable field", ord);
          if allow_nulls {
            out.set_null(idx, true);
            Ok(())
          } else {
            Err(internal_err!("Non-null constraint violation"))
          }
        } else {
          match tpe.as_ref() {
            &Type::INT => out.set_i32(idx, inp.get_i32(*ord)),
            &Type::BIGINT => out.set_i64(idx, inp.get_i64(*ord)),
            &Type::TEXT => out.set_str(idx, inp.get_str(*ord)),
            _ => todo!("Unsupported type {}", tpe),
          }
          Ok(())
        }
      },
    }
  }
}

impl TreeNode<Attribute> for Attribute {
  #[inline]
  fn debug_name(&self) -> String {
    match self {
      Attribute::Alias { name, ref child } => format!("({}) as {}", child[0].debug_name(), name),
      Attribute::LiteralInt(v) => format!("{}", v),
      Attribute::Reference { ord, name, .. } => format!("{}[{}]", name, ord),
    }
  }

  #[inline]
  fn as_ref(&self) -> &Attribute {
    self
  }

  #[inline]
  fn children(&self) -> &[Attribute] {
    match self {
      Attribute::Alias { ref child, .. } => child,
      Attribute::LiteralInt(_) => &[],
      Attribute::Reference { .. } => &[],
    }
  }

  #[inline]
  fn copy(&self, children: Vec<Attribute>) -> Attribute {
    match self {
      Attribute::Alias { child: _, name } => {
        assert_eq!(children.len(), 1, "Expected one child for Alias");
        Attribute::Alias { child: children, name: name.clone() }
      },
      Attribute::LiteralInt(v) => Attribute::LiteralInt(*v),
      Attribute::Reference { ord, name, tpe, nullable } => {
        Attribute::Reference {
          ord: *ord,
          name: name.clone(),
          tpe: tpe.clone(),
          nullable: *nullable
        }
      },
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_attr_create_alias() {
    let field = Field::new("col", Type::INT, true).unwrap();
    let attr = alias(
      reference(&field, 0).unwrap(),
      "alias"
    ).unwrap();

    assert_eq!(attr.name(), "ALIAS");
    assert_eq!(attr.data_type(), field.data_type());
    assert_eq!(attr.nullable(), field.nullable());
  }

  #[test]
  fn test_attr_create_alias_invalid_name() {
    let field = Field::new("col", Type::INT, true).unwrap();
    assert!(
      alias(
        reference(&field, 0).unwrap(),
        "a b c"
      ).is_err()
    );
  }

  #[test]
  fn test_attr_create_reference() {
    let field = Field::new("col", Type::INT, true).unwrap();
    let attr = reference(&field, 0).unwrap();

    assert_eq!(attr.name(), "COL");
    assert_eq!(attr.data_type(), field.data_type());
    assert_eq!(attr.nullable(), field.nullable());
  }

  #[test]
  #[should_panic(expected = "Expected one child for Alias")]
  fn test_attr_copy_alias_require_one_child() {
    let attr = alias(lit_int(1).unwrap(), "col").unwrap();
    attr.copy(
      vec![
        lit_int(2).unwrap(),
        lit_int(3).unwrap()
      ]
    );
  }

  #[test]
  fn test_attr_eval_reference() {
    let mut in_row = Row::new(3);
    in_row.set_i32(0, 123);
    in_row.set_i64(1, 234);
    in_row.set_str(2, "test");

    let mut out_row = Row::new(3);

    let field = Field::new("col", Type::INT, true).unwrap();
    let attr = reference(&field, 0).unwrap();
    attr.eval(&in_row, &mut out_row, 0, true).unwrap();

    let field = Field::new("col", Type::BIGINT, true).unwrap();
    let attr = reference(&field, 1).unwrap();
    attr.eval(&in_row, &mut out_row, 1, true).unwrap();

    let field = Field::new("col", Type::TEXT, true).unwrap();
    let attr = reference(&field, 2).unwrap();
    attr.eval(&in_row, &mut out_row, 2, true).unwrap();

    assert_eq!(out_row.get_i32(0), 123);
    assert_eq!(out_row.get_i64(1), 234);
    assert_eq!(out_row.get_str(2), "test");
  }

  #[test]
  fn test_attr_eval_reference_is_null_nullable_field() {
    let mut in_row = Row::new(1);
    in_row.set_null(0, true);

    // Value is null, the field is nullable, and we allow nulls.
    let mut out_row = Row::new(1);
    let field = Field::new("col", Type::INT, true).unwrap();
    let attr = reference(&field, 0).unwrap();
    attr.eval(&in_row, &mut out_row, 0, true).unwrap();
    assert!(out_row.is_null(0));

    // Value is null, the field is nullable, but we don't allow nulls.
    let mut out_row = Row::new(1);
    let field = Field::new("col", Type::INT, true).unwrap();
    let attr = reference(&field, 0).unwrap();
    assert!(attr.eval(&in_row, &mut out_row, 0, false).is_err());
  }

  #[test]
  #[should_panic(expected = "Value is null at pos 0 for a non-nullable field")]
  fn test_attr_eval_reference_is_null_non_nullable_field() {
    let mut in_row = Row::new(1);
    in_row.set_null(0, true);

    // Value is null, the field is not nullable.
    let mut out_row = Row::new(1);
    let field = Field::new("col", Type::INT, false).unwrap();
    let attr = reference(&field, 0).unwrap();
    attr.eval(&in_row, &mut out_row, 0, true).unwrap();
  }
}
