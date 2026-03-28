use std::fmt;
use std::rc::Rc;
use crate::common::error::{Error, Res};
use crate::sql::catalog::{SchemaInfo, RelationInfo};
use crate::sql::trees::TreeNode;
use crate::sql::types::{Field, Fields, Type};

pub const DEFAULT_EXPRESSION_NAME: &str = "?col?";
pub const DEFAULT_SUBQUERY_NAME: &str = "?subquery?";

// Returns the unary child from `children` while asserting the `children` length.
macro_rules! get_unary {
  ($name:expr, $children:expr) => {{
    assert_eq!(
      $children.len(),
      1,
      "Expected 1 child node for unary expression '{}' but found {}",
      $name,
      $children.len()
    );
    $children.pop().unwrap()
  }}
}

// Returns left and right nodes from `children` while asserting the `children` length.
macro_rules! get_binary {
  ($name:expr, $children:expr) => {{
    assert_eq!(
      $children.len(),
      2,
      "Expected 2 child nodes for binary expression '{}' but found {}",
      $name,
      $children.len()
    );
    let right = $children.pop().unwrap();
    let left = $children.pop().unwrap();
    (left, right)
  }}
}

macro_rules! display_unary {
  ($f:expr, $op:expr, $child:expr) => {{
    write!($f, "{}", $op)?;
    $child.display($f)
  }}
}

macro_rules! display_binary {
  ($f:expr, $left:expr, $op:expr, $right:expr) => {{
    write!($f, "(")?;
    $left.display($f)?;
    write!($f, ")")?;
    write!($f, " {} ", $op)?;
    write!($f, "(")?;
    $right.display($f)?;
    write!($f, ")")
  }}
}

#[inline]
fn identifier_display_name(parts: &[String], name: &str) -> String {
  format!("{}{}{}", parts.join("."), if parts.len() == 0 { "" } else { "." }, name)
}

#[inline]
pub fn can_numeric_and_null_upcast(from: &Type, to: &Type) -> bool {
  if from == to {
    return true;
  }

  match (from, to) {
    (&Type::INT, &Type::BIGINT) |
    (&Type::INT, &Type::FLOAT) |
    (&Type::INT, &Type::DOUBLE) => true,
    (&Type::BIGINT, &Type::FLOAT) |
    (&Type::BIGINT, &Type::DOUBLE) => true,
    (&Type::FLOAT, &Type::DOUBLE) => true,
    (&Type::NULL, _) => true,
    _ => false,
  }
}

#[inline]
fn can_numeric_and_null_downcast(from: &Type, to: &Type) -> bool {
  if from == to {
    return true;
  }

  match (from, to) {
    (&Type::BIGINT, &Type::INT) => true,
    (&Type::DOUBLE, &Type::FLOAT) |
    (&Type::DOUBLE, &Type::BIGINT) |
    (&Type::DOUBLE, &Type::INT) => true,
    (&Type::FLOAT, &Type::BIGINT) |
    (&Type::FLOAT, &Type::INT) => true,
    _ => false,
  }
}

#[inline]
fn can_upcast(from: &Type, to: &Type) -> bool {
  can_numeric_and_null_upcast(from, to) ||
  match (from, to) {
    (&Type::INT, &Type::TEXT) => true,
    (&Type::BIGINT, &Type::TEXT) => true,
    (&Type::FLOAT, &Type::TEXT) => true,
    (&Type::DOUBLE, &Type::TEXT) => true,
    (&Type::BOOL, &Type::TEXT) => true,
    _ => false,
  }
}

#[inline]
fn can_downcast(from: &Type, to: &Type) -> bool {
  can_numeric_and_null_downcast(from, to) ||
  match (from, to) {
    (&Type::TEXT, &Type::INT) |
    (&Type::TEXT, &Type::BIGINT) |
    (&Type::TEXT, &Type::FLOAT) |
    (&Type::TEXT, &Type::DOUBLE) |
    (&Type::TEXT, &Type::BOOL) => true,
    _ => false,
  }
}

#[inline]
pub fn can_cast(from: &Type, to: &Type) -> bool {
  can_upcast(from, to) || can_downcast(from, to)
}

#[inline]
pub fn promote_arithmetic_type(left: &Type, right: &Type) -> Res<Type> {
  match (left, right) {
    (&Type::NULL, &Type::NULL) => Ok(Type::NULL),
    (&Type::INT, &Type::INT) | (&Type::INT, &Type::NULL) |
    (&Type::NULL, &Type::INT) => Ok(Type::INT),

    (&Type::BIGINT, &Type::INT) | (&Type::INT, &Type::BIGINT) |
    (&Type::BIGINT, &Type::NULL) | (&Type::NULL, &Type::BIGINT) |
    (&Type::BIGINT, &Type::BIGINT) => Ok(Type::BIGINT),

    (&Type::FLOAT, &Type::INT) | (&Type::INT, &Type::FLOAT) |
    (&Type::FLOAT, &Type::BIGINT) | (&Type::BIGINT, &Type::FLOAT) |
    (&Type::FLOAT, &Type::NULL) | (&Type::NULL, &Type::FLOAT) |
    (&Type::FLOAT, &Type::FLOAT) => Ok(Type::FLOAT),

    (&Type::DOUBLE, &Type::INT) | (&Type::INT, &Type::DOUBLE) |
    (&Type::DOUBLE, &Type::BIGINT) | (&Type::BIGINT, &Type::DOUBLE) |
    (&Type::DOUBLE, &Type::FLOAT) | (&Type::FLOAT, &Type::DOUBLE) |
    (&Type::DOUBLE, &Type::NULL) | (&Type::NULL, &Type::DOUBLE) |
    (&Type::DOUBLE, &Type::DOUBLE) => Ok(Type::DOUBLE),

    (left, right) => {
      Err(
        Error::SQLAnalysisExpressionError(
          format!("Cannot reconcile data types {} and {}", left, right)
        )
      )
    },
  }
}

// Contains metadata for one or more expressions.
pub struct ExpressionContext {
  // Origin of the expression, e.g. `schema.table` or `alias` path to find the expression.
  // Does not include expression name.
  origin: Vec<String>,
}

impl ExpressionContext {
  // Creates new expression context from origin.
  fn new(origin: Vec<String>) -> Self {
    Self { origin }
  }

  // Returns true if the suffix is a subset or the context origin or is empty.
  pub fn matches_suffix(&self, suffix: &[String]) -> bool {
    let origin_len = self.origin.len();
    let suffix_len = suffix.len();

    // Suffix must be within origin.
    if suffix_len > origin_len {
      return false;
    }

    for i in 0..suffix_len {
      if &suffix[i] != &self.origin[origin_len - suffix_len + i] {
        return false;
      }
    }

    true
  }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expression {
  Add(Rc<Expression>, Rc<Expression>),
  Alias(Rc<Expression>, Rc<String> /* alias name */),
  And(Rc<Expression>, Rc<Expression>),
  Cast(Rc<Expression>, Rc<Type>),
  Concat(Rc<Expression>, Rc<Expression>),
  ColumnRef(
    Rc<SchemaInfo> /* schema info */,
    Rc<RelationInfo> /* table info */,
    Option<Rc<String>> /* alias */,
    usize /* column index */,
  ),
  Divide(Rc<Expression>, Rc<Expression>),
  Equals(Rc<Expression>, Rc<Expression>),
  GreaterThan(Rc<Expression>, Rc<Expression>),
  GreaterThanEquals(Rc<Expression>, Rc<Expression>),
  Identifier(Rc<Vec<String>> /* identifier parts/origin */, Rc<String> /* name */),
  IsNull(Rc<Expression>),
  IsNotNull(Rc<Expression>),
  LessThan(Rc<Expression>, Rc<Expression>),
  LessThanEquals(Rc<Expression>, Rc<Expression>),
  LiteralBool(bool),
  LiteralInt(i32),
  LiteralBigInt(i64),
  LiteralFloat(f32),
  LiteralDouble(f64),
  LiteralString(Rc<String> /* string value */),
  Multiply(Rc<Expression>, Rc<Expression>),
  Not(Rc<Expression>),
  NotEquals(Rc<Expression>, Rc<Expression>),
  Null,
  Or(Rc<Expression>, Rc<Expression>),
  Star(Rc<Vec<String>> /* identifier parts/origin */),
  Subtract(Rc<Expression>, Rc<Expression>),
  UnaryPlus(Rc<Expression>),
  UnaryMinus(Rc<Expression>),
}

impl Expression {
  // Returns expression name.
  pub fn name(&self) -> &str {
    match self {
      Expression::Add(_, _) => DEFAULT_EXPRESSION_NAME,
      Expression::Alias(_, ref name) => name,
      Expression::And(_, _) => DEFAULT_EXPRESSION_NAME,
      Expression::Cast(_, _) => DEFAULT_EXPRESSION_NAME,
      Expression::Concat(_, _) => DEFAULT_EXPRESSION_NAME,
      Expression::ColumnRef(_, ref table_info, _, ref idx) => table_info.field_at(*idx).name(),
      Expression::Divide(_, _) => DEFAULT_EXPRESSION_NAME,
      Expression::Equals(_, _) => DEFAULT_EXPRESSION_NAME,
      Expression::GreaterThan(_, _) => DEFAULT_EXPRESSION_NAME,
      Expression::GreaterThanEquals(_, _) => DEFAULT_EXPRESSION_NAME,
      Expression::Identifier(_, ref name) => name,
      Expression::IsNull(_) => DEFAULT_EXPRESSION_NAME,
      Expression::IsNotNull(_) => DEFAULT_EXPRESSION_NAME,
      Expression::LessThan(_, _) => DEFAULT_EXPRESSION_NAME,
      Expression::LessThanEquals(_, _) => DEFAULT_EXPRESSION_NAME,
      Expression::LiteralBool(_) => DEFAULT_EXPRESSION_NAME,
      Expression::LiteralInt(_) => DEFAULT_EXPRESSION_NAME,
      Expression::LiteralBigInt(_) => DEFAULT_EXPRESSION_NAME,
      Expression::LiteralFloat(_) => DEFAULT_EXPRESSION_NAME,
      Expression::LiteralDouble(_) => DEFAULT_EXPRESSION_NAME,
      Expression::LiteralString(_) => DEFAULT_EXPRESSION_NAME,
      Expression::Multiply(_, _) => DEFAULT_EXPRESSION_NAME,
      Expression::Not(_) => DEFAULT_EXPRESSION_NAME,
      Expression::NotEquals(_, _) => DEFAULT_EXPRESSION_NAME,
      Expression::Null => DEFAULT_EXPRESSION_NAME,
      Expression::Or(_, _) => DEFAULT_EXPRESSION_NAME,
      Expression::Star(_) => DEFAULT_EXPRESSION_NAME,
      Expression::Subtract(_, _) => DEFAULT_EXPRESSION_NAME,
      Expression::UnaryPlus(_) => DEFAULT_EXPRESSION_NAME,
      Expression::UnaryMinus(_) => DEFAULT_EXPRESSION_NAME,
    }
  }

  // Returns expression data type or promoted data type.
  pub fn data_type(&self) -> Res<Type> {
    match self {
      Expression::Add(ref left, ref right) => {
        promote_arithmetic_type(&left.data_type()?, &right.data_type()?)
      },
      Expression::Alias(ref child, _) => child.data_type(),
      Expression::And(_, _) => Ok(Type::BOOL),
      Expression::Cast(_, ref tpe) => Ok(tpe.as_ref().clone()),
      Expression::Concat(_, _) => Ok(Type::TEXT),
      Expression::ColumnRef(_, ref table_info, _, ref idx) => {
        Ok(table_info.field_at(*idx).data_type().clone())
      },
      Expression::Divide(ref left, ref right) => {
        promote_arithmetic_type(&left.data_type()?, &right.data_type()?)
      },
      Expression::Equals(_, _) => Ok(Type::BOOL),
      Expression::GreaterThan(_, _) => Ok(Type::BOOL),
      Expression::GreaterThanEquals(_, _) => Ok(Type::BOOL),
      Expression::Identifier(ref parts, ref name) => {
        Err(
          Error::SQLAnalysisExpressionError(
            format!(
              "Identifier {} does not have a data type",
              identifier_display_name(parts, name)
            )
          )
        )
      },
      Expression::IsNull(_) => Ok(Type::BOOL),
      Expression::IsNotNull(_) => Ok(Type::BOOL),
      Expression::LessThan(_, _) => Ok(Type::BOOL),
      Expression::LessThanEquals(_, _) => Ok(Type::BOOL),
      Expression::LiteralBool(_) => Ok(Type::BOOL),
      Expression::LiteralInt(_) => Ok(Type::INT),
      Expression::LiteralBigInt(_) => Ok(Type::BIGINT),
      Expression::LiteralFloat(_) => Ok(Type::FLOAT),
      Expression::LiteralDouble(_) => Ok(Type::DOUBLE),
      Expression::LiteralString(_) => Ok(Type::TEXT),
      Expression::Multiply(ref left, ref right) => {
        promote_arithmetic_type(&left.data_type()?, &right.data_type()?)
      },
      Expression::Not(_) => Ok(Type::BOOL),
      Expression::NotEquals(_, _) => Ok(Type::BOOL),
      Expression::Null => Ok(Type::NULL),
      Expression::Or(_, _) => Ok(Type::BOOL),
      Expression::Star(ref parts) => {
        Err(
          Error::SQLAnalysisExpressionError(
            format!(
              "Star expression {} does not have a data type",
              identifier_display_name(parts, "*")
            )
          )
        )
      },
      Expression::Subtract(ref left, ref right) => {
        promote_arithmetic_type(&left.data_type()?, &right.data_type()?)
      },
      Expression::UnaryPlus(ref child) => child.data_type(),
      Expression::UnaryMinus(ref child) => child.data_type(),
    }
  }

  // Returns true if the expression is nullable.
  pub fn nullable(&self) -> Res<bool> {
    match self {
      Expression::Add(ref left, ref right) => Ok(left.nullable()? || right.nullable()?),
      Expression::Alias(ref child, _) => child.nullable(),
      Expression::And(ref left, ref right) => Ok(left.nullable()? || right.nullable()?),
      Expression::Cast(ref expr, _) => expr.nullable(),
      Expression::Concat(ref left, ref right) => Ok(left.nullable()? || right.nullable()?),
      Expression::ColumnRef(_, ref table_info, _, ref idx) => {
        Ok(table_info.field_at(*idx).nullable())
      },
      Expression::Divide(ref left, ref right) => Ok(left.nullable()? || right.nullable()?),
      Expression::Equals(ref left, ref right) => Ok(left.nullable()? || right.nullable()?),
      Expression::GreaterThan(ref left, ref right) => Ok(left.nullable()? || right.nullable()?),
      Expression::GreaterThanEquals(ref left, ref right) => {
        Ok(left.nullable()? || right.nullable()?)
      },
      Expression::Identifier(ref parts, ref name) => {
        Err(
          Error::SQLAnalysisExpressionError(
            format!(
              "Identifier {} does not have nullable status",
              identifier_display_name(parts, name)
            )
          )
        )
      },
      Expression::IsNull(_) => Ok(false),
      Expression::IsNotNull(_) => Ok(false),
      Expression::LessThan(ref left, ref right) => Ok(left.nullable()? || right.nullable()?),
      Expression::LessThanEquals(ref left, ref right) => Ok(left.nullable()? || right.nullable()?),
      Expression::LiteralBool(_) => Ok(false),
      Expression::LiteralInt(_) => Ok(false),
      Expression::LiteralBigInt(_) => Ok(false),
      Expression::LiteralFloat(_) => Ok(false),
      Expression::LiteralDouble(_) => Ok(false),
      Expression::LiteralString(_) => Ok(false),
      Expression::Multiply(ref left, ref right) => Ok(left.nullable()? || right.nullable()?),
      Expression::Not(ref child) => child.nullable(),
      Expression::NotEquals(ref left, ref right) => Ok(left.nullable()? || right.nullable()?),
      Expression::Null => Ok(true),
      Expression::Or(ref left, ref right) => Ok(left.nullable()? || right.nullable()?),
      Expression::Star(ref parts) => {
        Err(
          Error::SQLAnalysisExpressionError(
            format!(
              "Star expression {} does not have nullable status",
              identifier_display_name(parts, "*")
            )
          )
        )
      },
      Expression::Subtract(ref left, ref right) => Ok(left.nullable()? || right.nullable()?),
      Expression::UnaryPlus(ref child) => child.nullable(),
      Expression::UnaryMinus(ref child) => child.nullable(),
    }
  }
}

impl TreeNode<Expression> for Expression {
  #[inline]
  fn display(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Expression::Add(ref left, ref right) => display_binary!(f, left, "+", right),
      Expression::Alias(ref child, ref name) => {
        child.display(f)?;
        write!(f, " as {}", name)
      },
      Expression::And(ref left, ref right) => display_binary!(f, left, "and", right),
      Expression::Cast(ref expr, ref tpe) => {
        write!(f, "cast(")?;
        expr.display(f)?;
        write!(f, "{})", tpe)
      },
      Expression::Concat(ref left, ref right) => display_binary!(f, left, "||", right),
      Expression::ColumnRef(_, ref table_info, _, ref index) => {
        let name = table_info.field_at(*index).name();
        let tpe = table_info.field_at(*index).data_type();
        write!(f, "{}:{}:{}", name, index, tpe)
      },
      Expression::Divide(ref left, ref right) => display_binary!(f, left, "/", right),
      Expression::Equals(ref left, ref right) => display_binary!(f, left, "=", right),
      Expression::GreaterThan(ref left, ref right) => display_binary!(f, left, ">", right),
      Expression::GreaterThanEquals(ref left, ref right) => display_binary!(f, left, ">=", right),
      Expression::Identifier(ref parts, ref name) => {
        write!(f, "${}{}{}", parts.join("."), if parts.len() == 0 { "" } else { "." }, name)
      },
      Expression::IsNull(ref expr) => { expr.display(f)?; write!(f, " is null") },
      Expression::IsNotNull(ref expr) => { expr.display(f)?; write!(f, " is not null") },
      Expression::LessThan(ref left, ref right) => display_binary!(f, left, "<", right),
      Expression::LessThanEquals(ref left, ref right) => display_binary!(f, left, "<=", right),
      Expression::LiteralBool(value) => write!(f, "{}", value),
      Expression::LiteralInt(value) => write!(f, "{}", value),
      Expression::LiteralBigInt(value) => write!(f, "{}", value),
      Expression::LiteralFloat(value) => write!(f, "{}", value),
      Expression::LiteralDouble(value) => write!(f, "{}", value),
      Expression::LiteralString(value) => write!(f, "{}", value),
      Expression::Multiply(ref left, ref right) => display_binary!(f, left, "x", right),
      Expression::Not(ref child) => display_unary!(f, "not ", child),
      Expression::NotEquals(ref left, ref right) => display_binary!(f, left, "<>", right),
      Expression::Null => write!(f, "null"),
      Expression::Or(ref left, ref right) => display_binary!(f, left, "or", right),
      Expression::Star(ref parts) => {
        write!(f, "${}{}*", parts.join("."), if parts.len() == 0 { "" } else { "." })
      },
      Expression::Subtract(ref left, ref right) => display_binary!(f, left, "-", right),
      Expression::UnaryPlus(ref child) => display_unary!(f, "+", child),
      Expression::UnaryMinus(ref child) => display_unary!(f, "-", child),
    }
  }

  #[inline]
  fn as_ref(&self) -> &Expression {
    self
  }

  #[inline]
  fn children(&self) -> Vec<&Expression> {
    match self {
      Expression::Add(ref left, ref right) => vec![left, right],
      Expression::Alias(ref child, _) => vec![child],
      Expression::And(ref left, ref right) => vec![left, right],
      Expression::Cast(ref expr, _) => vec![expr],
      Expression::Concat(ref left, ref right) => vec![left, right],
      Expression::ColumnRef(_, _, _, _) => Vec::new(),
      Expression::Divide(ref left, ref right) => vec![left, right],
      Expression::Equals(ref left, ref right) => vec![left, right],
      Expression::GreaterThan(ref left, ref right) => vec![left, right],
      Expression::GreaterThanEquals(ref left, ref right) => vec![left, right],
      Expression::Identifier(_, _) => Vec::new(),
      Expression::IsNull(ref expr) => vec![expr],
      Expression::IsNotNull(ref expr) => vec![expr],
      Expression::LessThan(ref left, ref right) => vec![left, right],
      Expression::LessThanEquals(ref left, ref right) => vec![left, right],
      Expression::LiteralBool(_) => Vec::new(),
      Expression::LiteralInt(_) => Vec::new(),
      Expression::LiteralBigInt(_) => Vec::new(),
      Expression::LiteralFloat(_) => Vec::new(),
      Expression::LiteralDouble(_) => Vec::new(),
      Expression::LiteralString(_) => Vec::new(),
      Expression::Multiply(ref left, ref right) => vec![left, right],
      Expression::Not(ref child) => vec![child],
      Expression::NotEquals(ref left, ref right) => vec![left, right],
      Expression::Null => Vec::new(),
      Expression::Or(ref left, ref right) => vec![left, right],
      Expression::Star(_) => Vec::new(),
      Expression::Subtract(ref left, ref right) => vec![left, right],
      Expression::UnaryPlus(ref child) => vec![child],
      Expression::UnaryMinus(ref child) => vec![child],
    }
  }

  #[inline]
  fn copy(&self, mut children: Vec<Expression>) -> Expression {
    match self {
      Expression::Add(_, _) => {
        let (left, right) = get_binary!("Add", children);
        Expression::Add(Rc::new(left), Rc::new(right))
      },
      Expression::Alias(_, ref name) => {
        let child = get_unary!("Alias", children);
        Expression::Alias(Rc::new(child), name.clone())
      },
      Expression::And(_, _) => {
        let (left, right) = get_binary!("And", children);
        Expression::And(Rc::new(left), Rc::new(right))
      },
      Expression::Cast(ref expr, ref tpe) => Expression::Cast(expr.clone(), tpe.clone()),
      Expression::Concat(_, _) => {
        let (left, right) = get_binary!("Concat", children);
        Expression::Concat(Rc::new(left), Rc::new(right))
      },
      Expression::ColumnRef(ref schema_info, ref table_info, ref alias, ref index) => {
        Expression::ColumnRef(schema_info.clone(), table_info.clone(), alias.clone(), *index)
      },
      Expression::Divide(_, _) => {
        let (left, right) = get_binary!("Divide", children);
        Expression::Divide(Rc::new(left), Rc::new(right))
      },
      Expression::Equals(_, _) => {
        let (left, right) = get_binary!("Equals", children);
        Expression::Equals(Rc::new(left), Rc::new(right))
      },
      Expression::GreaterThan(_, _) => {
        let (left, right) = get_binary!("GreaterThan", children);
        Expression::GreaterThan(Rc::new(left), Rc::new(right))
      },
      Expression::GreaterThanEquals(_, _) => {
        let (left, right) = get_binary!("GreaterThanEquals", children);
        Expression::GreaterThanEquals(Rc::new(left), Rc::new(right))
      },
      Expression::Identifier(parts, name) => Expression::Identifier(parts.clone(), name.clone()),
      Expression::IsNull(_) => {
        let child = get_unary!("IsNull", children);
        Expression::IsNull(Rc::new(child))
      },
      Expression::IsNotNull(_) => {
        let child = get_unary!("IsNotNull", children);
        Expression::IsNotNull(Rc::new(child))
      },
      Expression::LessThan(_, _) => {
        let (left, right) = get_binary!("LessThan", children);
        Expression::LessThan(Rc::new(left), Rc::new(right))
      },
      Expression::LessThanEquals(_, _) => {
        let (left, right) = get_binary!("LessThanEquals", children);
        Expression::LessThanEquals(Rc::new(left), Rc::new(right))
      },
      Expression::LiteralBool(value) => Expression::LiteralBool(*value),
      Expression::LiteralInt(value) => Expression::LiteralInt(*value),
      Expression::LiteralBigInt(value) => Expression::LiteralBigInt(*value),
      Expression::LiteralFloat(value) => Expression::LiteralFloat(*value),
      Expression::LiteralDouble(value) => Expression::LiteralDouble(*value),
      Expression::LiteralString(value) => Expression::LiteralString(value.clone()),
      Expression::Multiply(_, _) => {
        let (left, right) = get_binary!("Multiply", children);
        Expression::Multiply(Rc::new(left), Rc::new(right))
      },
      Expression::Not(_) => {
        let child = get_unary!("Not", children);
        Expression::Not(Rc::new(child))
      },
      Expression::NotEquals(_, _) => {
        let (left, right) = get_binary!("NotEquals", children);
        Expression::NotEquals(Rc::new(left), Rc::new(right))
      },
      Expression::Null => Expression::Null,
      Expression::Or(_, _) => {
        let (left, right) = get_binary!("Or", children);
        Expression::Or(Rc::new(left), Rc::new(right))
      },
      Expression::Star(parts) => Expression::Star(parts.clone()),
      Expression::Subtract(_, _) => {
        let (left, right) = get_binary!("Subtract", children);
        Expression::Subtract(Rc::new(left), Rc::new(right))
      },
      Expression::UnaryPlus(_) => {
        let child = get_unary!("UnaryPlus", children);
        Expression::UnaryPlus(Rc::new(child))
      },
      Expression::UnaryMinus(_) => {
        let child = get_unary!("UnaryMinus", children);
        Expression::UnaryMinus(Rc::new(child))
      },
    }
  }
}

#[derive(Debug, PartialEq)]
pub enum LogicalPlan {
  CreateSchema(Rc<String> /* schema name */),
  CreateTable(
    Rc<String> /* schema name */,
    Rc<String> /* table name */,
    Rc<Fields> /* table schema */,
  ),
  DropSchema(Rc<SchemaInfo> /* schema info */, bool /* cascade */),
  DropTable(Rc<SchemaInfo> /* schema info */, Rc<RelationInfo> /* table info */),
  Explain(
    bool /* extended */,
    Rc<LogicalPlan> /* unresolved snapshot */,
    Rc<LogicalPlan> /* child */,
  ),
  Filter(Rc<Expression> /* filter expression */, Rc<LogicalPlan> /* child */),
  InsertInto(
    Rc<SchemaInfo> /* schema info */,
    Rc<RelationInfo> /* table info */,
    Rc<Vec<usize>> /* insert order of fields' positions, guaranteed to be non-empty and valid */,
    Rc<LogicalPlan> /* query */,
  ),
  Limit(usize /* limit */, Rc<LogicalPlan> /* child */),
  LocalRelation(Rc<Vec<Vec<Expression>>> /* expressions */),
  Project(Rc<Vec<Expression>> /* expressions */, Rc<LogicalPlan> /* child */),
  Subquery(Rc<String> /* alias */, Rc<LogicalPlan> /* child */),
  TableScan(
    Rc<SchemaInfo> /* schema info */,
    Rc<RelationInfo> /* table info */,
    Option<Rc<String>> /* alias */,
  ),
  UnresolvedCreateSchema(Rc<String> /* schema name */),
  UnresolvedCreateTable(
    Option<Rc<String>> /* schema name */,
    Rc<String> /* table name */,
    Rc<Fields> /* table schema/fields */,
  ),
  UnresolvedDropSchema(Rc<String> /* schema name */, bool /* cascade */),
  UnresolvedDropTable(Option<Rc<String>> /* optional schema name */, Rc<String> /* table name */),
  UnresolvedExplain(
    bool /* extended */,
    Rc<LogicalPlan> /* snapshot */,
    Rc<LogicalPlan> /* child to resolve */,
  ),
  UnresolvedFilter(Rc<Expression> /* filter expression */, Rc<LogicalPlan> /* child */),
  UnresolvedInsertInto(
    Option<Rc<String>> /* optional schema name */,
    Rc<String> /* table name */,
    Rc<Vec<String>> /* columns */,
    Rc<LogicalPlan> /* query */,
  ),
  UnresolvedLimit(usize /* limit */, Rc<LogicalPlan> /* child */),
  UnresolvedLocalRelation(Rc<Vec<Vec<Expression>>> /* expressions */),
  UnresolvedProject(Rc<Vec<Expression>> /* expressions */, Rc<LogicalPlan> /* child */),
  UnresolvedDescribe(Option<Rc<String>> /* optional schema name */, Rc<String> /* table name */),
  UnresolvedShowSchemas,
  UnresolvedShowTables(Option<Rc<String>> /* schema */),
  UnresolvedSubquery(Option<Rc<String>> /* alias */, Rc<LogicalPlan> /* child */),
  UnresolvedTableScan(
    Option<Rc<String>> /* optional schema name */,
    Rc<String> /* table name */,
    Option<Rc<String>> /* alias */,
  ),
}

impl LogicalPlan {
  // Returns the list of output expressions available to parent nodes during analysis.
  // Used by analysis to resolve identifiers in expressions (e.g. column names in WHERE/SELECT)
  // against the columns produced by a child plan. Each entry carries an ExpressionContext
  // (the qualifier scope, e.g. schema.table or subquery alias) and the expression itself.
  // This is not the user-facing output schema — for that, see PhysicalPlan::schema().
  pub fn output(&self) -> Res<Vec<(Rc<ExpressionContext>, Expression)>> {
    match self {
      LogicalPlan::CreateSchema(_) => Ok(Vec::new()),
      LogicalPlan::CreateTable(_, _, _) => Ok(Vec::new()),
      LogicalPlan::DropSchema(_, _) => Ok(Vec::new()),
      LogicalPlan::DropTable(_, _) => Ok(Vec::new()),
      LogicalPlan::Explain(_, _, _) => Ok(Vec::new()),
      LogicalPlan::Filter(_, ref child) => child.output(),
      LogicalPlan::InsertInto(_, _, _, _) => Ok(Vec::new()),
      LogicalPlan::Limit(_, ref child) => child.output(),
      LogicalPlan::LocalRelation(ref expressions) => {
        if expressions.len() > 0 {
          let ctx = Rc::new(ExpressionContext::new(Vec::new()));
          let mut output = Vec::new();
          for expr in &expressions[0] {
            output.push((ctx.clone(), expr.clone()));
          }
          Ok(output)
        } else {
          Ok(Vec::new())
        }
      },
      LogicalPlan::Project(ref expressions, _) => {
        let ctx = Rc::new(ExpressionContext::new(Vec::new()));
        let mut output = Vec::new();
        for expr in expressions.as_ref() {
          output.push((ctx.clone(), expr.clone()));
        }
        Ok(output)
      },
      LogicalPlan::Subquery(ref alias, ref child) => {
        let ctx = Rc::new(ExpressionContext::new(vec![alias.to_string()]));
        let mut output = child.output()?;
        for i in 0..output.len() {
          output[i].0 = ctx.clone();
        }
        Ok(output)
      },
      LogicalPlan::TableScan(ref schema_info, ref table_info, ref alias) => {
        let ctx = Rc::new(
          ExpressionContext::new(
            vec![
              schema_info.schema_name().to_string(),
              table_info.relation_name().to_string(),
            ]
          )
        );
        let num_fields = table_info.num_fields();
        let mut expressions = Vec::new();
        for idx in 0..num_fields {
          expressions.push(
            (
              ctx.clone(),
              Expression::ColumnRef(schema_info.clone(), table_info.clone(), alias.clone(), idx)
            )
          );
        }
        Ok(expressions)
      },
      LogicalPlan::UnresolvedCreateSchema(_) => {
        Err(Error::SQLAnalysisError("UnresolvedCreateSchema".to_string()))
      },
      LogicalPlan::UnresolvedCreateTable(_, _, _) => {
        Err(Error::SQLAnalysisError("UnresolvedCreateTable".to_string()))
      },
      LogicalPlan::UnresolvedDropSchema(_, _) => {
        Err(Error::SQLAnalysisError("UnresolvedDropSchema".to_string()))
      },
      LogicalPlan::UnresolvedDropTable(_, _) => {
        Err(Error::SQLAnalysisError("UnresolvedDropTable".to_string()))
      },
      LogicalPlan::UnresolvedExplain(_, _, _) => {
        Err(Error::SQLAnalysisError("UnresolvedExplain".to_string()))
      },
      LogicalPlan::UnresolvedFilter(_, _) => {
        Err(Error::SQLAnalysisError("UnresolvedFilter".to_string()))
      },
      LogicalPlan::UnresolvedInsertInto(_, _, _, _) => {
        Err(Error::SQLAnalysisError("UnresolvedInsertInto".to_string()))
      },
      LogicalPlan::UnresolvedLimit(_, _) => {
        Err(Error::SQLAnalysisError("UnresolvedLimit".to_string()))
      },
      LogicalPlan::UnresolvedLocalRelation(_) => {
        Err(Error::SQLAnalysisError("UnresolvedLocalRelation".to_string()))
      },
      LogicalPlan::UnresolvedProject(_, _) => {
        Err(Error::SQLAnalysisError("UnresolvedProject".to_string()))
      },
      LogicalPlan::UnresolvedDescribe(_, _) => {
        Err(Error::SQLAnalysisError("UnresolvedDescribe".to_string()))
      },
      LogicalPlan::UnresolvedShowSchemas => {
        Err(Error::SQLAnalysisError("UnresolvedShowSchemas".to_string()))
      },
      LogicalPlan::UnresolvedShowTables(_) => {
        Err(Error::SQLAnalysisError("UnresolvedShowTables".to_string()))
      },
      LogicalPlan::UnresolvedSubquery(_, _) => {
        Err(Error::SQLAnalysisError("UnresolvedSubquery".to_string()))
      },
      LogicalPlan::UnresolvedTableScan(_, _, _) => {
        Err(Error::SQLAnalysisError("UnresolvedTableScan".to_string()))
      },
    }
  }
}

impl TreeNode<LogicalPlan> for LogicalPlan {
  #[inline]
  fn display(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      LogicalPlan::CreateSchema(ref schema_name) => write!(f, "CreateSchema({})", schema_name),
      LogicalPlan::CreateTable(ref schema_name, ref table_name, ref fields) => {
        write!(f, "CreateTable({}.{}, {})", schema_name, table_name, fields)
      },
      LogicalPlan::DropSchema(ref schema_info, cascade) => {
        write!(f, "DropSchema({}, {})", schema_info.schema_name(), cascade)
      },
      LogicalPlan::DropTable(ref schema_info, ref table_info) => {
        write!(f, "DropTable({}.{})", schema_info.schema_name(), table_info.relation_name())
      },
      LogicalPlan::Explain(extended, _, _) => write!(f, "Explain(extended: {})", extended),
      LogicalPlan::Filter(ref expression, _) => {
        write!(f, "Filter(")?;
        expression.display(f)?;
        write!(f, ")")
      },
      LogicalPlan::InsertInto(ref schema_info, ref table_info, _, _) => {
        write!(f, "InsertInto({}.{})", schema_info.schema_name(), table_info.relation_name())
      },
      LogicalPlan::Limit(ref limit, _) => write!(f, "Limit({})", limit),
      LogicalPlan::LocalRelation(ref expressions) => {
        write!(f, "LocalRelation({} rows)", expressions.len())
      },
      LogicalPlan::Project(ref expressions, _) => {
        write!(f, "Project(")?;
        for i in 0..expressions.len() {
          if i > 0 {
            write!(f, ", ")?;
          }
          expressions[i].display(f)?;
        }
        write!(f, ")")
      },
      LogicalPlan::Subquery(ref alias, _) => write!(f, "Subquery({})", alias),
      LogicalPlan::TableScan(ref schema_info, ref table_info, ref alias) => {
        write!(
          f, "TableScan({}.{}, {:?})",
          schema_info.schema_name(),
          table_info.relation_name(),
          alias
        )
      },
      LogicalPlan::UnresolvedCreateSchema(_) => write!(f, "UnresolvedCreateSchema"),
      LogicalPlan::UnresolvedCreateTable(_, _, _) => write!(f, "UnresolvedCreateTable"),
      LogicalPlan::UnresolvedDropSchema(_, _) => write!(f, "UnresolvedDropSchema"),
      LogicalPlan::UnresolvedDropTable(_, _) => write!(f, "UnresolvedDropTable"),
      LogicalPlan::UnresolvedExplain(_, _, _) => write!(f, "UnresolvedExplain"),
      LogicalPlan::UnresolvedFilter(_, _) => write!(f, "UnresolvedFilter"),
      LogicalPlan::UnresolvedInsertInto(_, _, _, _) => write!(f, "UnresolvedInsertInto"),
      LogicalPlan::UnresolvedLimit(_, _) => write!(f, "UnresolvedLimit"),
      LogicalPlan::UnresolvedLocalRelation(_) => write!(f, "UnresolvedLocalRelation"),
      LogicalPlan::UnresolvedProject(_, _) => write!(f, "UnresolvedProject"),
      LogicalPlan::UnresolvedDescribe(_, _) => write!(f, "UnresolvedDescribe"),
      LogicalPlan::UnresolvedShowSchemas => write!(f, "UnresolvedShowSchemas"),
      LogicalPlan::UnresolvedShowTables(_) => write!(f, "UnresolvedShowTables"),
      LogicalPlan::UnresolvedSubquery(_, _) => write!(f, "UnresolvedSubquery"),
      LogicalPlan::UnresolvedTableScan(_, _, _) => write!(f, "UnresolvedTableScan"),
    }
  }

  #[inline]
  fn as_ref(&self) -> &LogicalPlan {
    self
  }

  #[inline]
  fn children(&self) -> Vec<&LogicalPlan> {
    match self {
      LogicalPlan::CreateSchema(_) => Vec::new(),
      LogicalPlan::CreateTable(_, _, _) => Vec::new(),
      LogicalPlan::DropSchema(_, _) => Vec::new(),
      LogicalPlan::DropTable(_, _) => Vec::new(),
      LogicalPlan::Explain(_, _, ref child) => vec![child],
      LogicalPlan::Filter(_, ref child) => vec![child],
      LogicalPlan::InsertInto(_, _, _, ref query) => vec![query],
      LogicalPlan::Limit(_, ref child) => vec![child],
      LogicalPlan::LocalRelation(_) => Vec::new(),
      LogicalPlan::Project(_, ref child) => vec![child],
      LogicalPlan::Subquery(_, ref child) => vec![child],
      LogicalPlan::TableScan(_, _, _) => Vec::new(),
      LogicalPlan::UnresolvedCreateSchema(_) => Vec::new(),
      LogicalPlan::UnresolvedCreateTable(_, _, _) => Vec::new(),
      LogicalPlan::UnresolvedDropSchema(_, _) => Vec::new(),
      LogicalPlan::UnresolvedDropTable(_, _) => Vec::new(),
      LogicalPlan::UnresolvedExplain(_, _, ref child) => vec![child],
      LogicalPlan::UnresolvedFilter(_, ref child) => vec![child],
      LogicalPlan::UnresolvedInsertInto(_, _, _, ref query) => vec![query],
      LogicalPlan::UnresolvedLimit(_, ref child) => vec![child],
      LogicalPlan::UnresolvedLocalRelation(_) => Vec::new(),
      LogicalPlan::UnresolvedProject(_, ref child) => vec![child],
      LogicalPlan::UnresolvedDescribe(_, _) => Vec::new(),
      LogicalPlan::UnresolvedShowSchemas => Vec::new(),
      LogicalPlan::UnresolvedShowTables(_) => Vec::new(),
      LogicalPlan::UnresolvedSubquery(_, ref child) => vec![child],
      LogicalPlan::UnresolvedTableScan(_, _, _) => Vec::new(),
    }
  }

  #[inline]
  fn copy(&self, mut children: Vec<LogicalPlan>) -> LogicalPlan {
    match self {
      LogicalPlan::CreateSchema(ref schema_name) => {
        LogicalPlan::CreateSchema(schema_name.clone())
      },
      LogicalPlan::CreateTable(ref schema_name, ref table_name, ref schema) => {
        LogicalPlan::CreateTable(schema_name.clone(), table_name.clone(), schema.clone())
      },
      LogicalPlan::DropSchema(ref schema_info, cascade) => {
        LogicalPlan::DropSchema(schema_info.clone(), *cascade)
      },
      LogicalPlan::DropTable(ref schema_info, ref table_info) => {
        LogicalPlan::DropTable(schema_info.clone(), table_info.clone())
      },
      LogicalPlan::Explain(extended, ref unresolved_child, _) => {
        let child = get_unary!("Explain", children);
        LogicalPlan::Explain(*extended, unresolved_child.clone(), Rc::new(child))
      },
      LogicalPlan::Filter(ref expression, _) => {
        let child = get_unary!("Filter", children);
        LogicalPlan::Filter(expression.clone(), Rc::new(child))
      },
      LogicalPlan::InsertInto(ref schema_info, ref table_info, ref cols, _) => {
        let child = get_unary!("InsertInto", children);
        LogicalPlan::InsertInto(
          schema_info.clone(),
          table_info.clone(),
          cols.clone(),
          Rc::new(child)
        )
      },
      LogicalPlan::Limit(limit, _) => {
        let child = get_unary!("Limit", children);
        LogicalPlan::Limit(*limit, Rc::new(child))
      },
      LogicalPlan::LocalRelation(ref expressions) => {
        LogicalPlan::LocalRelation(expressions.clone())
      },
      LogicalPlan::Project(ref expressions, _) => {
        let child = get_unary!("Project", children);
        LogicalPlan::Project(expressions.clone(), Rc::new(child))
      },
      LogicalPlan::Subquery(ref alias, _) => {
        let child = get_unary!("Subquery", children);
        LogicalPlan::Subquery(alias.clone(), Rc::new(child))
      },
      LogicalPlan::TableScan(ref schema_info, ref table_info, ref table_alias) => {
        LogicalPlan::TableScan(schema_info.clone(), table_info.clone(), table_alias.clone())
      },
      LogicalPlan::UnresolvedCreateSchema(ref schema_name) => {
        LogicalPlan::UnresolvedCreateSchema(schema_name.clone())
      },
      LogicalPlan::UnresolvedCreateTable(ref schema_name, ref table_name, ref fields) => {
        LogicalPlan::UnresolvedCreateTable(schema_name.clone(), table_name.clone(), fields.clone())
      },
      LogicalPlan::UnresolvedDropSchema(ref schema_name, cascade) => {
        LogicalPlan::UnresolvedDropSchema(schema_name.clone(), *cascade)
      },
      LogicalPlan::UnresolvedDropTable(ref schema_name, ref table_name) => {
        LogicalPlan::UnresolvedDropTable(schema_name.clone(), table_name.clone())
      },
      LogicalPlan::UnresolvedExplain(extended, ref snapshot, _) => {
        let child = get_unary!("UnresolvedExplain", children);
        LogicalPlan::UnresolvedExplain(*extended, snapshot.clone(), Rc::new(child))
      },
      LogicalPlan::UnresolvedFilter(ref expressions, _) => {
        let child = get_unary!("UnresolvedFilter", children);
        LogicalPlan::UnresolvedFilter(expressions.clone(), Rc::new(child))
      },
      LogicalPlan::UnresolvedInsertInto(ref schema_name, ref table_name, ref columns, _) => {
        let child = get_unary!("UnresolvedInsertInto", children);
        LogicalPlan::UnresolvedInsertInto(
          schema_name.clone(),
          table_name.clone(),
          columns.clone(),
          Rc::new(child)
        )
      },
      LogicalPlan::UnresolvedLimit(limit, _) => {
        let child = get_unary!("UnresolvedLimit", children);
        LogicalPlan::UnresolvedLimit(*limit, Rc::new(child))
      },
      LogicalPlan::UnresolvedLocalRelation(ref expressions) => {
        LogicalPlan::UnresolvedLocalRelation(expressions.clone())
      },
      LogicalPlan::UnresolvedProject(ref expressions, _) => {
        let child = get_unary!("UnresolvedProject", children);
        LogicalPlan::UnresolvedProject(expressions.clone(), Rc::new(child))
      },
      LogicalPlan::UnresolvedDescribe(ref schema, ref table) => {
        LogicalPlan::UnresolvedDescribe(schema.clone(), table.clone())
      },
      LogicalPlan::UnresolvedShowSchemas => LogicalPlan::UnresolvedShowSchemas,
      LogicalPlan::UnresolvedShowTables(ref schema_name) => {
        LogicalPlan::UnresolvedShowTables(schema_name.clone())
      },
      LogicalPlan::UnresolvedSubquery(ref alias, _) => {
        let child = get_unary!("UnresolvedSubquery", children);
        LogicalPlan::UnresolvedSubquery(alias.clone(), Rc::new(child))
      },
      LogicalPlan::UnresolvedTableScan(ref schema_name, ref table_name, ref table_alias) => {
        LogicalPlan::UnresolvedTableScan(
          schema_name.clone(),
          table_name.clone(),
          table_alias.clone()
        )
      },
    }
  }
}

#[derive(Debug, PartialEq)]
pub enum PhysicalPlan {
  CreateSchema(Rc<String> /* schema name */),
  CreateTable(
    Rc<String> /* schema name */,
    Rc<String> /* table name */,
    Rc<Fields> /* table schema */,
  ),
  DropSchema(Rc<SchemaInfo> /* schema info */, bool /* cascade */),
  DropTable(Rc<SchemaInfo> /* schema info */, Rc<RelationInfo> /* table info */),
  Explain(
    bool,
    Rc<LogicalPlan> /* unresolved snapshot */,
    Rc<LogicalPlan> /* resolved snapshot */,
    Rc<PhysicalPlan> /* child */,
  ),
  Filter(Rc<Expression> /* filter expression */, Rc<PhysicalPlan> /* child */),
  InsertInto(
    Rc<SchemaInfo> /* schema info */,
    Rc<RelationInfo> /* table info */,
    Rc<Vec<usize>> /* col_positions */,
    Rc<PhysicalPlan> /* query */,
  ),
  Limit(usize /* limit */, Rc<PhysicalPlan> /* child */),
  LocalRelation(Rc<Vec<Vec<Expression>>> /* expressions */),
  Project(Rc<Vec<Expression>> /* expressions */, Rc<PhysicalPlan> /* child */),
  SeqScan(Rc<SchemaInfo> /* schema info */, Rc<RelationInfo> /* table info */),
}

impl PhysicalPlan {
  // Returns the output schema of rows produced by this plan node.
  pub fn schema(&self) -> Res<Fields> {
    match self {
      PhysicalPlan::CreateSchema(_) |
      PhysicalPlan::CreateTable(_, _, _) |
      PhysicalPlan::DropSchema(_, _) |
      PhysicalPlan::DropTable(_, _) => Ok(Fields::new(Vec::new())),
      PhysicalPlan::InsertInto(_, _, _, _) => Ok(Fields::new(vec![
        Field::new("rows_affected".to_string(), Type::BIGINT, false),
      ])),
      PhysicalPlan::Explain(_, _, _, _) => Ok(Fields::new(vec![
        Field::new("plan".to_string(), Type::TEXT, false),
      ])),
      PhysicalPlan::Filter(_, ref child) => child.schema(),
      PhysicalPlan::Limit(_, ref child) => child.schema(),
      PhysicalPlan::LocalRelation(ref expressions) => {
        if expressions.is_empty() {
          return Ok(Fields::new(Vec::new()));
        }
        // All rows are guaranteed to be homogeneous by analysis (same count and types),
        // so the schema can be derived from the first row's expressions.
        expressions[0].iter().map(|expr| {
          Ok(Field::new(expr.name().to_string(), expr.data_type()?, expr.nullable()?))
        }).collect::<Res<Vec<_>>>().map(Fields::new)
      },
      PhysicalPlan::Project(ref exprs, _) => {
        exprs.iter().map(|expr| {
          Ok(Field::new(expr.name().to_string(), expr.data_type()?, expr.nullable()?))
        }).collect::<Res<Vec<_>>>().map(Fields::new)
      },
      PhysicalPlan::SeqScan(_, ref table_info) => Ok(table_info.relation_fields().clone()),
    }
  }
}

impl TreeNode<PhysicalPlan> for PhysicalPlan {
  #[inline]
  fn display(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      PhysicalPlan::CreateSchema(ref schema_name) => write!(f, "CreateSchema({})", schema_name),
      PhysicalPlan::CreateTable(ref schema_name, ref table_name, ref fields) => {
        write!(f, "CreateTable({}.{}, {})", schema_name, table_name, fields)
      },
      PhysicalPlan::DropSchema(ref schema_info, cascade) => {
        write!(f, "DropSchema({}, {})", schema_info.schema_name(), cascade)
      },
      PhysicalPlan::DropTable(ref schema_info, ref table_info) => {
        write!(f, "DropTable({}.{})", schema_info.schema_name(), table_info.relation_name())
      },
      PhysicalPlan::Explain(extended, _, _, _) => {
        write!(f, "Explain(extended: {})", extended)
      },
      PhysicalPlan::Filter(ref expression, _) => {
        write!(f, "Filter(")?;
        expression.display(f)?;
        write!(f, ")")
      },
      PhysicalPlan::InsertInto(ref schema_info, ref table_info, _, _) => {
        write!(f, "InsertInto({}.{})", schema_info.schema_name(), table_info.relation_name())
      },
      PhysicalPlan::Limit(ref limit, _) => write!(f, "Limit({})", limit),
      PhysicalPlan::LocalRelation(ref expressions) => {
        write!(f, "LocalRelation({} rows)", expressions.len())
      },
      PhysicalPlan::Project(ref expressions, _) => {
        write!(f, "Project(")?;
        for i in 0..expressions.len() {
          if i > 0 {
            write!(f, ", ")?;
          }
          expressions[i].display(f)?;
        }
        write!(f, ")")
      },
      PhysicalPlan::SeqScan(ref schema_info, ref table_info) => {
        write!(f, "SeqScan({}.{})", schema_info.schema_name(), table_info.relation_name())
      },
    }
  }

  #[inline]
  fn as_ref(&self) -> &PhysicalPlan {
    self
  }

  #[inline]
  fn children(&self) -> Vec<&PhysicalPlan> {
    match self {
      PhysicalPlan::CreateSchema(_) => Vec::new(),
      PhysicalPlan::CreateTable(_, _, _) => Vec::new(),
      PhysicalPlan::DropSchema(_, _) => Vec::new(),
      PhysicalPlan::DropTable(_, _) => Vec::new(),
      PhysicalPlan::Explain(_, _, _, ref child) => vec![child],
      PhysicalPlan::Filter(_, ref child) => vec![child],
      PhysicalPlan::InsertInto(_, _, _, ref query) => vec![query],
      PhysicalPlan::Limit(_, ref child) => vec![child],
      PhysicalPlan::LocalRelation(_) => Vec::new(),
      PhysicalPlan::Project(_, ref child) => vec![child],
      PhysicalPlan::SeqScan(_, _) => Vec::new(),
    }
  }

  #[inline]
  fn copy(&self, mut children: Vec<PhysicalPlan>) -> PhysicalPlan {
    match self {
      PhysicalPlan::CreateSchema(ref schema_name) => {
        PhysicalPlan::CreateSchema(schema_name.clone())
      },
      PhysicalPlan::CreateTable(ref schema_name, ref table_name, ref schema) => {
        PhysicalPlan::CreateTable(schema_name.clone(), table_name.clone(), schema.clone())
      },
      PhysicalPlan::DropSchema(ref schema_info, cascade) => {
        PhysicalPlan::DropSchema(schema_info.clone(), *cascade)
      },
      PhysicalPlan::DropTable(ref schema_info, ref table_info) => {
        PhysicalPlan::DropTable(schema_info.clone(), table_info.clone())
      },
      PhysicalPlan::Explain(extended, ref unresolved_snapshot, ref resolved_snapshot, _) => {
        let child = get_unary!("Explain", children);
        PhysicalPlan::Explain(
          *extended,
          unresolved_snapshot.clone(),
          resolved_snapshot.clone(),
          Rc::new(child)
        )
      },
      PhysicalPlan::Filter(ref expression, _) => {
        let child = get_unary!("Filter", children);
        PhysicalPlan::Filter(expression.clone(), Rc::new(child))
      },
      PhysicalPlan::InsertInto(ref schema_info, ref table_info, ref cols, _) => {
        let child = get_unary!("InsertInto", children);
        PhysicalPlan::InsertInto(
          schema_info.clone(),
          table_info.clone(),
          cols.clone(),
          Rc::new(child)
        )
      },
      PhysicalPlan::Limit(limit, _) => {
        let child = get_unary!("Limit", children);
        PhysicalPlan::Limit(*limit, Rc::new(child))
      },
      PhysicalPlan::LocalRelation(ref expressions) => {
        PhysicalPlan::LocalRelation(expressions.clone())
      },
      PhysicalPlan::Project(ref expressions, _) => {
        let child = get_unary!("Project", children);
        PhysicalPlan::Project(expressions.clone(), Rc::new(child))
      },
      PhysicalPlan::SeqScan(ref schema_info, ref table_info) => {
        PhysicalPlan::SeqScan(schema_info.clone(), table_info.clone())
      },
    }
  }
}

//=========================
// Plan and Expression DSL
//=========================

pub mod dsl {
  use std::rc::Rc;
  use super::{Expression, Fields, LogicalPlan, Type};

  // Expressions.

  pub fn qualified_identifier(parts: Vec<&str>, name: &str) -> Expression {
    Expression::Identifier(
      Rc::new(parts.into_iter().map(|x| x.to_string()).collect()),
      Rc::new(name.to_string())
    )
  }

  pub fn identifier(name: &str) -> Expression {
    qualified_identifier(Vec::new(), name)
  }

  pub fn boolean(value: bool) -> Expression {
    Expression::LiteralBool(value)
  }

  pub fn int(value: i32) -> Expression {
    Expression::LiteralInt(value)
  }

  pub fn bigint(value: i64) -> Expression {
    Expression::LiteralBigInt(value)
  }

  pub fn float(value: f32) -> Expression {
    Expression::LiteralFloat(value)
  }

  pub fn double(value: f64) -> Expression {
    Expression::LiteralDouble(value)
  }

  pub fn string(value: &str) -> Expression {
    Expression::LiteralString(Rc::new(format!("{}", value)))
  }

  pub fn null() -> Expression {
    Expression::Null
  }

  pub fn star() -> Expression {
    Expression::Star(Rc::new(Vec::new()))
  }

  pub fn qualified_star(parts: Vec<&str>) -> Expression {
    Expression::Star(Rc::new(parts.into_iter().map(|x| x.to_string()).collect()))
  }

  pub fn alias(child: Expression, name: &str) -> Expression {
    Expression::Alias(Rc::new(child), Rc::new(name.to_string()))
  }

  pub fn add(left: Expression, right: Expression) -> Expression {
    Expression::Add(Rc::new(left), Rc::new(right))
  }

  pub fn cast(expr: Expression, tpe: Type) -> Expression {
    Expression::Cast(Rc::new(expr), Rc::new(tpe))
  }

  pub fn subtract(left: Expression, right: Expression) -> Expression {
    Expression::Subtract(Rc::new(left), Rc::new(right))
  }

  pub fn multiply(left: Expression, right: Expression) -> Expression {
    Expression::Multiply(Rc::new(left), Rc::new(right))
  }

  pub fn divide(left: Expression, right: Expression) -> Expression {
    Expression::Divide(Rc::new(left), Rc::new(right))
  }

  pub fn _plus(child: Expression) -> Expression {
    Expression::UnaryPlus(Rc::new(child))
  }

  pub fn _minus(child: Expression) -> Expression {
    Expression::UnaryMinus(Rc::new(child))
  }

  pub fn equals(left: Expression, right: Expression) -> Expression {
    Expression::Equals(Rc::new(left), Rc::new(right))
  }

  pub fn less_than(left: Expression, right: Expression) -> Expression {
    Expression::LessThan(Rc::new(left), Rc::new(right))
  }

  pub fn greater_than(left: Expression, right: Expression) -> Expression {
    Expression::GreaterThan(Rc::new(left), Rc::new(right))
  }

  pub fn and(left: Expression, right: Expression) -> Expression {
    Expression::And(Rc::new(left), Rc::new(right))
  }

  pub fn or(left: Expression, right: Expression) -> Expression {
    Expression::Or(Rc::new(left), Rc::new(right))
  }

  pub fn concat(left: Expression, right: Expression) -> Expression {
    Expression::Concat(Rc::new(left), Rc::new(right))
  }

  pub fn is_null(child: Expression) -> Expression {
    Expression::IsNull(Rc::new(child))
  }

  pub fn is_not_null(child: Expression) -> Expression {
    Expression::IsNotNull(Rc::new(child))
  }

  pub fn not(child: Expression) -> Expression {
    Expression::Not(Rc::new(child))
  }

  pub fn not_equals(left: Expression, right: Expression) -> Expression {
    Expression::NotEquals(Rc::new(left), Rc::new(right))
  }

  pub fn less_than_equals(left: Expression, right: Expression) -> Expression {
    Expression::LessThanEquals(Rc::new(left), Rc::new(right))
  }

  pub fn greater_than_equals(left: Expression, right: Expression) -> Expression {
    Expression::GreaterThanEquals(Rc::new(left), Rc::new(right))
  }

  // LogicalPlan nodes.

  pub fn create_schema(schema: &str) -> LogicalPlan {
    LogicalPlan::UnresolvedCreateSchema(Rc::new(schema.to_string()))
  }

  pub fn create_table(schema: Option<&str>, table: &str, fields: Fields) -> LogicalPlan {
    LogicalPlan::UnresolvedCreateTable(
      schema.map(|x| Rc::new(x.to_string())),
      Rc::new(table.to_string()),
      Rc::new(fields)
    )
  }

  pub fn drop_schema(schema: &str, is_cascade: bool) -> LogicalPlan {
    LogicalPlan::UnresolvedDropSchema(Rc::new(schema.to_string()), is_cascade)
  }

  pub fn drop_table(schema: Option<&str>, table: &str) -> LogicalPlan {
    LogicalPlan::UnresolvedDropTable(
      schema.map(|x| Rc::new(x.to_string())),
      Rc::new(table.to_string())
    )
  }

  // Returns an empty local relation with no rows.
  pub fn empty() -> LogicalPlan {
    LogicalPlan::UnresolvedLocalRelation(Rc::new(vec![vec![]]))
  }

  pub fn filter(expression: Expression, child: LogicalPlan) -> LogicalPlan {
    LogicalPlan::UnresolvedFilter(Rc::new(expression), Rc::new(child))
  }

  pub fn from(schema: Option<&str>, table: &str, alias: Option<&str>) -> LogicalPlan {
    LogicalPlan::UnresolvedTableScan(
      schema.map(|x| Rc::new(x.to_string())),
      Rc::new(table.to_string()),
      alias.map(|x| Rc::new(x.to_string()))
    )
  }

  pub fn insert_into_values(
    schema: Option<&str>,
    table: &str,
    cols: Vec<String>,
    expr: Vec<Vec<Expression>>
  ) -> LogicalPlan {
    insert_into_select(schema, table, cols, LogicalPlan::UnresolvedLocalRelation(Rc::new(expr)))
  }

  pub fn insert_into_select(
    schema: Option<&str>,
    table: &str,
    cols: Vec<String>,
    query: LogicalPlan
  ) -> LogicalPlan {
    LogicalPlan::UnresolvedInsertInto(
      schema.map(|x| Rc::new(x.to_string())),
      Rc::new(table.to_string()),
      Rc::new(cols),
      Rc::new(query)
    )
  }

  pub fn limit(value: usize, child: LogicalPlan) -> LogicalPlan {
    LogicalPlan::UnresolvedLimit(value, Rc::new(child))
  }

  pub fn local(expressions: Vec<Expression>) -> LogicalPlan {
    LogicalPlan::UnresolvedLocalRelation(Rc::new(vec![expressions]))
  }

  pub fn project(expressions: Vec<Expression>, child: LogicalPlan) -> LogicalPlan {
    LogicalPlan::UnresolvedProject(Rc::new(expressions), Rc::new(child))
  }

  pub fn subquery(child: LogicalPlan, alias: Option<&str>) -> LogicalPlan {
    LogicalPlan::UnresolvedSubquery(alias.map(|x| Rc::new(x.to_string())), Rc::new(child))
  }
}

#[cfg(test)]
pub mod tests {
  use super::*;
  use super::dsl::*;
  use crate::sql::trees;

  #[test]
  fn test_plan_expression_type_promotion() {
    assert_eq!(
      Expression::Alias(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new("foo".to_string())
      ).data_type(),
      Ok(Type::INT)
    );
    assert_eq!(
      Expression::Add(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Expression::LiteralBigInt(2)),
      ).data_type(),
      Ok(Type::BIGINT)
    );
    assert_eq!(
      Expression::And(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Expression::LiteralInt(2)),
      ).data_type(),
      Ok(Type::BOOL)
    );

    // §3.3: Integer division stays integer.
    assert_eq!(
      Expression::Divide(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Expression::LiteralInt(2)),
      ).data_type(),
      Ok(Type::INT)
    );
    assert_eq!(
      Expression::Divide(
        Rc::new(Expression::LiteralBigInt(1)),
        Rc::new(Expression::LiteralInt(2)),
      ).data_type(),
      Ok(Type::BIGINT)
    );
    assert_eq!(
      Expression::Divide(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Expression::LiteralBigInt(2)),
      ).data_type(),
      Ok(Type::BIGINT)
    );
    assert_eq!(
      Expression::Divide(
        Rc::new(Expression::LiteralBigInt(1)),
        Rc::new(Expression::LiteralBigInt(2)),
      ).data_type(),
      Ok(Type::BIGINT)
    );
    assert_eq!(
      Expression::Divide(
        Rc::new(Expression::LiteralFloat(1.0)),
        Rc::new(Expression::LiteralInt(2)),
      ).data_type(),
      Ok(Type::FLOAT)
    );
    assert_eq!(
      Expression::Divide(
        Rc::new(Expression::LiteralDouble(1.0)),
        Rc::new(Expression::LiteralInt(2)),
      ).data_type(),
      Ok(Type::DOUBLE)
    );
    assert_eq!(
      Expression::Cast(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Type::BIGINT),
      ).data_type(),
      Ok(Type::BIGINT)
    );
    assert_eq!(
      Expression::Equals(Rc::new(Expression::Null), Rc::new(Expression::Null)).data_type(),
      Ok(Type::BOOL)
    );
    assert_eq!(
      Expression::GreaterThan(Rc::new(Expression::Null), Rc::new(Expression::Null)).data_type(),
      Ok(Type::BOOL)
    );
    assert_eq!(
      Expression::GreaterThanEquals(
        Rc::new(Expression::Null),
        Rc::new(Expression::Null)
      ).data_type(),
      Ok(Type::BOOL)
    );
    assert_eq!(
      Expression::Identifier(
        Rc::new(vec!["foo".to_string()]),
        Rc::new("bar".to_string())
      ).data_type(),
      Err(
        Error::SQLAnalysisExpressionError(
          "Identifier foo.bar does not have a data type".to_string()
        )
      )
    );
    assert_eq!(
      Expression::Identifier(Rc::new(Vec::new()), Rc::new("bar".to_string())).data_type(),
      Err(
        Error::SQLAnalysisExpressionError(
          "Identifier bar does not have a data type".to_string()
        )
      )
    );
    assert_eq!(
      Expression::LessThan(Rc::new(Expression::Null), Rc::new(Expression::Null)).data_type(),
      Ok(Type::BOOL)
    );
    assert_eq!(
      Expression::LessThanEquals(Rc::new(Expression::Null), Rc::new(Expression::Null)).data_type(),
      Ok(Type::BOOL)
    );
    assert_eq!(Expression::LiteralBool(true).data_type(), Ok(Type::BOOL));
    assert_eq!(Expression::LiteralInt(1i32).data_type(), Ok(Type::INT));
    assert_eq!(Expression::LiteralBigInt(1i64).data_type(), Ok(Type::BIGINT));
    assert_eq!(Expression::LiteralFloat(1f32).data_type(), Ok(Type::FLOAT));
    assert_eq!(Expression::LiteralDouble(1f64).data_type(), Ok(Type::DOUBLE));
    assert_eq!(Expression::LiteralString(Rc::new("foo".to_string())).data_type(), Ok(Type::TEXT));
    assert_eq!(
      Expression::Multiply(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Expression::LiteralFloat(1f32)),
      ).data_type(),
      Ok(Type::FLOAT)
    );
    assert_eq!(Expression::Null.data_type(), Ok(Type::NULL));

    // §3.2: NULL op T infers type T; NULL op NULL infers NULL.
    assert_eq!(
      Expression::Add(Rc::new(Expression::Null), Rc::new(Expression::LiteralInt(1))).data_type(),
      Ok(Type::INT)
    );
    assert_eq!(
      Expression::Add(
        Rc::new(Expression::LiteralDouble(1.0)), Rc::new(Expression::Null)
      ).data_type(),
      Ok(Type::DOUBLE)
    );
    assert_eq!(
      Expression::Add(Rc::new(Expression::Null), Rc::new(Expression::Null)).data_type(),
      Ok(Type::NULL)
    );
    assert_eq!(
      Expression::Divide(
        Rc::new(Expression::Null), Rc::new(Expression::LiteralBigInt(1))
      ).data_type(),
      Ok(Type::BIGINT)
    );

    // §3.4 / §8.2: Non-numeric operands in arithmetic are a type error.
    assert_eq!(
      Expression::Add(
        Rc::new(Expression::LiteralDouble(1.0)),
        Rc::new(Expression::LiteralString(Rc::new("x".to_string()))),
      ).data_type(),
      Err(Error::SQLAnalysisExpressionError(
        "Cannot reconcile data types DOUBLE and TEXT".to_string()
      ))
    );
    assert_eq!(
      Expression::Multiply(
        Rc::new(Expression::LiteralFloat(1.0)),
        Rc::new(Expression::LiteralBool(true)),
      ).data_type(),
      Err(Error::SQLAnalysisExpressionError(
        "Cannot reconcile data types FLOAT and BOOL".to_string()
      ))
    );
    assert_eq!(
      Expression::Or(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Expression::LiteralInt(2)),
      ).data_type(),
      Ok(Type::BOOL)
    );
    assert_eq!(
      Expression::Star(Rc::new(vec!["foo".to_string()])).data_type(),
      Err(
        Error::SQLAnalysisExpressionError(
          "Star expression foo.* does not have a data type".to_string()
        )
      )
    );
    assert_eq!(
      Expression::Star(Rc::new(Vec::new())).data_type(),
      Err(
        Error::SQLAnalysisExpressionError(
          "Star expression * does not have a data type".to_string()
        )
      )
    );
    assert_eq!(
      Expression::Subtract(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Expression::LiteralDouble(2f64)),
      ).data_type(),
      Ok(Type::DOUBLE)
    );
    assert_eq!(
      Expression::UnaryPlus(Rc::new(Expression::LiteralInt(1))).data_type(),
      Ok(Type::INT)
    );
    assert_eq!(
      Expression::UnaryMinus(Rc::new(Expression::LiteralFloat(1.1))).data_type(),
      Ok(Type::FLOAT)
    );
    assert_eq!(
      Expression::Concat(
        Rc::new(Expression::LiteralString(Rc::new("a".to_string()))),
        Rc::new(Expression::LiteralString(Rc::new("b".to_string()))),
      ).data_type(),
      Ok(Type::TEXT)
    );
    assert_eq!(Expression::IsNull(Rc::new(Expression::Null)).data_type(), Ok(Type::BOOL));
    assert_eq!(Expression::IsNotNull(Rc::new(Expression::Null)).data_type(), Ok(Type::BOOL));
    assert_eq!(Expression::Not(Rc::new(Expression::LiteralBool(true))).data_type(), Ok(Type::BOOL));
    assert_eq!(
      Expression::NotEquals(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Expression::LiteralInt(2)),
      ).data_type(),
      Ok(Type::BOOL)
    );
  }

  #[test]
  fn test_plan_expression_nullable() {
    // Literals: never nullable.
    assert_eq!(Expression::LiteralBool(true).nullable(), Ok(false));
    assert_eq!(Expression::LiteralInt(1).nullable(), Ok(false));
    assert_eq!(Expression::LiteralBigInt(1).nullable(), Ok(false));
    assert_eq!(Expression::LiteralFloat(1.0).nullable(), Ok(false));
    assert_eq!(Expression::LiteralDouble(1.0).nullable(), Ok(false));
    assert_eq!(Expression::LiteralString(Rc::new("a".to_string())).nullable(), Ok(false));
    // NULL literal: always nullable.
    assert_eq!(Expression::Null.nullable(), Ok(true));

    // Unary: propagates child.
    assert_eq!(Expression::UnaryMinus(Rc::new(Expression::LiteralInt(1))).nullable(), Ok(false));
    assert_eq!(Expression::UnaryMinus(Rc::new(Expression::Null)).nullable(), Ok(true));
    assert_eq!(Expression::UnaryPlus(Rc::new(Expression::LiteralInt(1))).nullable(), Ok(false));
    assert_eq!(Expression::Not(Rc::new(Expression::LiteralBool(true))).nullable(), Ok(false));
    assert_eq!(Expression::Not(Rc::new(Expression::Null)).nullable(), Ok(true));

    // Arithmetic: nullable if either side is.
    assert_eq!(
      Expression::Add(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Expression::LiteralInt(2)),
      ).nullable(),
      Ok(false)
    );
    assert_eq!(
      Expression::Add(
        Rc::new(Expression::Null),
        Rc::new(Expression::LiteralInt(2)),
      ).nullable(),
      Ok(true)
    );
    assert_eq!(
      Expression::Subtract(Rc::new(Expression::Null), Rc::new(Expression::Null)).nullable(),
      Ok(true)
    );
    assert_eq!(
      Expression::Multiply(
        Rc::new(Expression::LiteralInt(1)), Rc::new(Expression::Null)
      ).nullable(),
      Ok(true)
    );
    assert_eq!(
      Expression::Divide(
        Rc::new(Expression::LiteralInt(1)), Rc::new(Expression::LiteralInt(2))
      ).nullable(),
      Ok(false)
    );

    // Comparisons: nullable if either operand is nullable.
    assert_eq!(
      Expression::Equals(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Expression::LiteralInt(2)),
      ).nullable(),
      Ok(false)
    );
    assert_eq!(
      Expression::Equals(
        Rc::new(Expression::Null),
        Rc::new(Expression::LiteralInt(2)),
      ).nullable(),
      Ok(true)
    );
    assert_eq!(
      Expression::NotEquals(
        Rc::new(Expression::Null),
        Rc::new(Expression::LiteralInt(1)),
      ).nullable(),
      Ok(true)
    );
    assert_eq!(
      Expression::NotEquals(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Expression::LiteralInt(2)),
      ).nullable(),
      Ok(false)
    );
    assert_eq!(
      Expression::LessThan(Rc::new(Expression::Null), Rc::new(Expression::Null)).nullable(),
      Ok(true)
    );
    assert_eq!(
      Expression::GreaterThan(
        Rc::new(Expression::LiteralInt(1)), Rc::new(Expression::LiteralInt(2))
      ).nullable(),
      Ok(false)
    );

    // Logical: nullable if either operand is.
    assert_eq!(
      Expression::And(
        Rc::new(Expression::LiteralBool(true)),
        Rc::new(Expression::LiteralBool(false)),
      ).nullable(),
      Ok(false)
    );
    assert_eq!(
      Expression::And(
        Rc::new(Expression::Null),
        Rc::new(Expression::LiteralBool(false)),
      ).nullable(),
      Ok(true)
    );
    assert_eq!(
      Expression::Or(
        Rc::new(Expression::Null),
        Rc::new(Expression::LiteralBool(true)),
      ).nullable(),
      Ok(true)
    );
    assert_eq!(
      Expression::Or(
        Rc::new(Expression::LiteralBool(false)),
        Rc::new(Expression::LiteralBool(true)),
      ).nullable(),
      Ok(false)
    );

    // IS NULL / IS NOT NULL: always non-nullable regardless of input.
    assert_eq!(Expression::IsNull(Rc::new(Expression::Null)).nullable(), Ok(false));
    assert_eq!(Expression::IsNull(Rc::new(Expression::LiteralInt(1))).nullable(), Ok(false));
    assert_eq!(Expression::IsNotNull(Rc::new(Expression::Null)).nullable(), Ok(false));
    assert_eq!(Expression::IsNotNull(Rc::new(Expression::LiteralInt(1))).nullable(), Ok(false));

    // Concat: propagates nullability.
    assert_eq!(
      Expression::Concat(
        Rc::new(Expression::LiteralString(Rc::new("a".to_string()))),
        Rc::new(Expression::LiteralString(Rc::new("b".to_string()))),
      ).nullable(),
      Ok(false)
    );
    assert_eq!(
      Expression::Concat(
        Rc::new(Expression::Null),
        Rc::new(Expression::LiteralString(Rc::new("b".to_string()))),
      ).nullable(),
      Ok(true)
    );

    // Alias and Cast preserve child nullability.
    assert_eq!(
      Expression::Alias(Rc::new(Expression::Null), Rc::new("x".to_string())).nullable(),
      Ok(true)
    );
    assert_eq!(
      Expression::Alias(Rc::new(Expression::LiteralInt(1)), Rc::new("x".to_string())).nullable(),
      Ok(false)
    );
    assert_eq!(
      Expression::Cast(Rc::new(Expression::Null), Rc::new(Type::INT)).nullable(),
      Ok(true)
    );
    assert_eq!(
      Expression::Cast(Rc::new(Expression::LiteralInt(1)), Rc::new(Type::BIGINT)).nullable(),
      Ok(false)
    );
  }

  #[test]
  fn test_plan_expression_copy() {
    use crate::sql::trees;

    // Verify that copy() correctly rebuilds each new expression type.
    // We use transform_up with a no-op rule which exercises copy() on every node.
    struct NoopRule;
    impl trees::Rule<Expression> for NoopRule {
      fn apply(&self, _: &Expression) -> crate::common::error::Res<Option<Expression>> {
        Ok(None)
      }
    }

    let exprs = vec![
      concat(string("a"), string("b")),
      is_null(int(1)),
      is_not_null(null()),
      not(boolean(true)),
      not_equals(int(1), int(2)),
    ];

    for expr in exprs {
      let result = trees::transform_up(&expr, &NoopRule).unwrap();
      assert_eq!(result, expr);
    }
  }

  #[test]
  fn test_plan_can_cast() {
    // Identity: T → T is always valid.
    assert!(can_cast(&Type::NULL, &Type::NULL));
    assert!(can_cast(&Type::BOOL, &Type::BOOL));
    assert!(can_cast(&Type::INT, &Type::INT));
    assert!(can_cast(&Type::BIGINT, &Type::BIGINT));
    assert!(can_cast(&Type::FLOAT, &Type::FLOAT));
    assert!(can_cast(&Type::DOUBLE, &Type::DOUBLE));
    assert!(can_cast(&Type::TEXT, &Type::TEXT));

    // §4.1 Widening: always succeed at runtime.
    assert!(can_cast(&Type::NULL, &Type::BOOL));
    assert!(can_cast(&Type::NULL, &Type::INT));
    assert!(can_cast(&Type::NULL, &Type::BIGINT));
    assert!(can_cast(&Type::NULL, &Type::FLOAT));
    assert!(can_cast(&Type::NULL, &Type::DOUBLE));
    assert!(can_cast(&Type::NULL, &Type::TEXT));
    assert!(can_cast(&Type::INT, &Type::BIGINT));
    assert!(can_cast(&Type::INT, &Type::FLOAT));
    assert!(can_cast(&Type::INT, &Type::DOUBLE));
    assert!(can_cast(&Type::INT, &Type::TEXT));
    assert!(can_cast(&Type::BIGINT, &Type::FLOAT));
    assert!(can_cast(&Type::BIGINT, &Type::DOUBLE));
    assert!(can_cast(&Type::BIGINT, &Type::TEXT));
    assert!(can_cast(&Type::FLOAT, &Type::DOUBLE));
    assert!(can_cast(&Type::FLOAT, &Type::TEXT));
    assert!(can_cast(&Type::DOUBLE, &Type::TEXT));
    assert!(can_cast(&Type::BOOL, &Type::TEXT));

    // §4.2 Narrowing: validated at analysis, may fail at runtime.
    assert!(can_cast(&Type::BIGINT, &Type::INT));
    assert!(can_cast(&Type::DOUBLE, &Type::FLOAT));
    assert!(can_cast(&Type::DOUBLE, &Type::BIGINT));
    assert!(can_cast(&Type::DOUBLE, &Type::INT));
    assert!(can_cast(&Type::FLOAT, &Type::BIGINT));
    assert!(can_cast(&Type::FLOAT, &Type::INT));
    assert!(can_cast(&Type::TEXT, &Type::INT));
    assert!(can_cast(&Type::TEXT, &Type::BIGINT));
    assert!(can_cast(&Type::TEXT, &Type::FLOAT));
    assert!(can_cast(&Type::TEXT, &Type::DOUBLE));
    assert!(can_cast(&Type::TEXT, &Type::BOOL));

    // §4.3 Invalid: rejected at analysis time.
    assert!(!can_cast(&Type::BOOL, &Type::INT));
    assert!(!can_cast(&Type::BOOL, &Type::BIGINT));
    assert!(!can_cast(&Type::BOOL, &Type::FLOAT));
    assert!(!can_cast(&Type::BOOL, &Type::DOUBLE));
    assert!(!can_cast(&Type::BOOL, &Type::NULL));
    assert!(!can_cast(&Type::INT, &Type::BOOL));
    assert!(!can_cast(&Type::BIGINT, &Type::BOOL));
    assert!(!can_cast(&Type::FLOAT, &Type::BOOL));
    assert!(!can_cast(&Type::DOUBLE, &Type::BOOL));
    assert!(!can_cast(&Type::TEXT, &Type::NULL));
    assert!(!can_cast(&Type::INT, &Type::NULL));
    assert!(!can_cast(&Type::BIGINT, &Type::NULL));
    assert!(!can_cast(&Type::FLOAT, &Type::NULL));
    assert!(!can_cast(&Type::DOUBLE, &Type::NULL));
  }

  #[test]
  fn test_plan_can_numeric_and_null_downcast() {
    // Identity.
    assert!(can_numeric_and_null_downcast(&Type::INT, &Type::INT));
    assert!(can_numeric_and_null_downcast(&Type::BIGINT, &Type::BIGINT));
    assert!(can_numeric_and_null_downcast(&Type::FLOAT, &Type::FLOAT));
    assert!(can_numeric_and_null_downcast(&Type::DOUBLE, &Type::DOUBLE));
    assert!(can_numeric_and_null_downcast(&Type::NULL, &Type::NULL));

    // Numeric narrowing.
    assert!(can_numeric_and_null_downcast(&Type::BIGINT, &Type::INT));
    assert!(can_numeric_and_null_downcast(&Type::DOUBLE, &Type::FLOAT));
    assert!(can_numeric_and_null_downcast(&Type::DOUBLE, &Type::BIGINT));
    assert!(can_numeric_and_null_downcast(&Type::DOUBLE, &Type::INT));
    assert!(can_numeric_and_null_downcast(&Type::FLOAT, &Type::BIGINT));
    assert!(can_numeric_and_null_downcast(&Type::FLOAT, &Type::INT));

    // Widening not allowed.
    assert!(!can_numeric_and_null_downcast(&Type::INT, &Type::BIGINT));
    assert!(!can_numeric_and_null_downcast(&Type::INT, &Type::FLOAT));
    assert!(!can_numeric_and_null_downcast(&Type::INT, &Type::DOUBLE));
    assert!(!can_numeric_and_null_downcast(&Type::FLOAT, &Type::DOUBLE));

    // Non-numeric not allowed.
    assert!(!can_numeric_and_null_downcast(&Type::TEXT, &Type::INT));
    assert!(!can_numeric_and_null_downcast(&Type::BOOL, &Type::INT));
    assert!(!can_numeric_and_null_downcast(&Type::NULL, &Type::INT));
    assert!(!can_numeric_and_null_downcast(&Type::INT, &Type::TEXT));
    assert!(!can_numeric_and_null_downcast(&Type::INT, &Type::BOOL));
  }

  #[test]
  fn test_plan_can_upcast() {
    // Numeric and NULL widening (via can_numeric_and_null_upcast).
    assert!(can_upcast(&Type::INT, &Type::BIGINT));
    assert!(can_upcast(&Type::INT, &Type::FLOAT));
    assert!(can_upcast(&Type::INT, &Type::DOUBLE));
    assert!(can_upcast(&Type::BIGINT, &Type::FLOAT));
    assert!(can_upcast(&Type::BIGINT, &Type::DOUBLE));
    assert!(can_upcast(&Type::FLOAT, &Type::DOUBLE));
    assert!(can_upcast(&Type::NULL, &Type::INT));
    assert!(can_upcast(&Type::NULL, &Type::TEXT));
    assert!(can_upcast(&Type::NULL, &Type::BOOL));

    // Identity.
    assert!(can_upcast(&Type::INT, &Type::INT));
    assert!(can_upcast(&Type::TEXT, &Type::TEXT));
    assert!(can_upcast(&Type::BOOL, &Type::BOOL));

    // → TEXT widening.
    assert!(can_upcast(&Type::INT, &Type::TEXT));
    assert!(can_upcast(&Type::BIGINT, &Type::TEXT));
    assert!(can_upcast(&Type::FLOAT, &Type::TEXT));
    assert!(can_upcast(&Type::DOUBLE, &Type::TEXT));
    assert!(can_upcast(&Type::BOOL, &Type::TEXT));

    // Narrowing not allowed.
    assert!(!can_upcast(&Type::BIGINT, &Type::INT));
    assert!(!can_upcast(&Type::DOUBLE, &Type::FLOAT));
    assert!(!can_upcast(&Type::TEXT, &Type::INT));
    assert!(!can_upcast(&Type::TEXT, &Type::BOOL));
    assert!(!can_upcast(&Type::BOOL, &Type::INT));
    assert!(!can_upcast(&Type::INT, &Type::BOOL));
  }

  #[test]
  fn test_plan_can_downcast() {
    // Numeric narrowing (via can_numeric_and_null_downcast).
    assert!(can_downcast(&Type::BIGINT, &Type::INT));
    assert!(can_downcast(&Type::DOUBLE, &Type::FLOAT));
    assert!(can_downcast(&Type::DOUBLE, &Type::BIGINT));
    assert!(can_downcast(&Type::DOUBLE, &Type::INT));
    assert!(can_downcast(&Type::FLOAT, &Type::BIGINT));
    assert!(can_downcast(&Type::FLOAT, &Type::INT));

    // Identity.
    assert!(can_downcast(&Type::INT, &Type::INT));
    assert!(can_downcast(&Type::TEXT, &Type::TEXT));
    assert!(can_downcast(&Type::BOOL, &Type::BOOL));

    // TEXT → narrowing.
    assert!(can_downcast(&Type::TEXT, &Type::INT));
    assert!(can_downcast(&Type::TEXT, &Type::BIGINT));
    assert!(can_downcast(&Type::TEXT, &Type::FLOAT));
    assert!(can_downcast(&Type::TEXT, &Type::DOUBLE));
    assert!(can_downcast(&Type::TEXT, &Type::BOOL));

    // Widening not allowed.
    assert!(!can_downcast(&Type::INT, &Type::BIGINT));
    assert!(!can_downcast(&Type::INT, &Type::TEXT));
    assert!(!can_downcast(&Type::BOOL, &Type::TEXT));
    assert!(!can_downcast(&Type::INT, &Type::BOOL));
    assert!(!can_downcast(&Type::BOOL, &Type::INT));
  }

  #[test]
  fn test_plan_can_numeric_and_null_upcast() {
    // Identity.
    assert!(can_numeric_and_null_upcast(&Type::INT, &Type::INT));
    assert!(can_numeric_and_null_upcast(&Type::BIGINT, &Type::BIGINT));
    assert!(can_numeric_and_null_upcast(&Type::FLOAT, &Type::FLOAT));
    assert!(can_numeric_and_null_upcast(&Type::DOUBLE, &Type::DOUBLE));
    assert!(can_numeric_and_null_upcast(&Type::NULL, &Type::NULL));

    // Numeric widening.
    assert!(can_numeric_and_null_upcast(&Type::INT, &Type::BIGINT));
    assert!(can_numeric_and_null_upcast(&Type::INT, &Type::FLOAT));
    assert!(can_numeric_and_null_upcast(&Type::INT, &Type::DOUBLE));
    assert!(can_numeric_and_null_upcast(&Type::BIGINT, &Type::FLOAT));
    assert!(can_numeric_and_null_upcast(&Type::BIGINT, &Type::DOUBLE));
    assert!(can_numeric_and_null_upcast(&Type::FLOAT, &Type::DOUBLE));

    // NULL → any.
    assert!(can_numeric_and_null_upcast(&Type::NULL, &Type::INT));
    assert!(can_numeric_and_null_upcast(&Type::NULL, &Type::BIGINT));
    assert!(can_numeric_and_null_upcast(&Type::NULL, &Type::FLOAT));
    assert!(can_numeric_and_null_upcast(&Type::NULL, &Type::DOUBLE));
    assert!(can_numeric_and_null_upcast(&Type::NULL, &Type::TEXT));
    assert!(can_numeric_and_null_upcast(&Type::NULL, &Type::BOOL));

    // Narrowing not allowed.
    assert!(!can_numeric_and_null_upcast(&Type::BIGINT, &Type::INT));
    assert!(!can_numeric_and_null_upcast(&Type::DOUBLE, &Type::FLOAT));
    assert!(!can_numeric_and_null_upcast(&Type::FLOAT, &Type::INT));

    // Non-numeric not allowed (no implicit TEXT/BOOL widening).
    assert!(!can_numeric_and_null_upcast(&Type::TEXT, &Type::INT));
    assert!(!can_numeric_and_null_upcast(&Type::BOOL, &Type::INT));
    assert!(!can_numeric_and_null_upcast(&Type::INT, &Type::TEXT));
    assert!(!can_numeric_and_null_upcast(&Type::INT, &Type::BOOL));
    assert!(!can_numeric_and_null_upcast(&Type::TEXT, &Type::BOOL));
    assert!(!can_numeric_and_null_upcast(&Type::BOOL, &Type::TEXT));
  }

  #[test]
  fn test_plan_expression_context_matches_suffix() {
    let ctx = ExpressionContext::new(Vec::new());
    assert!(ctx.matches_suffix(&[]));

    let ctx = ExpressionContext::new(vec!["a".to_string(), "b".to_string(), "c".to_string()]);
    assert!(ctx.matches_suffix(&[]));
    assert!(ctx.matches_suffix(&["c".to_string()]));
    assert!(ctx.matches_suffix(&["b".to_string(), "c".to_string()]));
    assert!(ctx.matches_suffix(&["a".to_string(), "b".to_string(), "c".to_string()]));

    assert!(!ctx.matches_suffix(&["".to_string()]));
    assert!(!ctx.matches_suffix(&["a".to_string()]));
    assert!(!ctx.matches_suffix(&["b".to_string()]));
    assert!(!ctx.matches_suffix(&["a".to_string(), "b".to_string()]));
    assert!(!ctx.matches_suffix(&["c".to_string(), "b".to_string()]));
    assert!(!ctx.matches_suffix(&["c".to_string(), "b".to_string(), "a".to_string()]));
  }

  #[test]
  fn test_plan_display() {
    let expr = and(equals(int(1), int(2)), less_than(identifier("a"), string("abc")));
    assert_eq!(trees::plan_output(&expr), "((1) = (2)) and (($a) < (abc))");

    let expr = equals(alias(qualified_identifier(vec!["a", "b"], "c"), "col"), string("abc"));
    assert_eq!(trees::plan_output(&expr), "($a.b.c as col) = (abc)");

    let expr = equals(alias(identifier("a"), "A"), _minus(int(2)));
    assert_eq!(trees::plan_output(&expr), "($a as A) = (-2)");
  }
}
