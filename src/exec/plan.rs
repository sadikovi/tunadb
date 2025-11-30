use std::fmt;
use std::rc::Rc;
use crate::common::error::{Error, Res};
use crate::core::trees::TreeNode;
use crate::core::types::{Fields, Type};
use crate::exec::catalog::{SchemaInfo, RelationInfo};

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
  Identifier(Rc<Vec<String>> /* identifier parts */),
  LessThan(Rc<Expression>, Rc<Expression>),
  LessThanEquals(Rc<Expression>, Rc<Expression>),
  LiteralBool(bool),
  LiteralInt(i32),
  LiteralBigInt(i64),
  LiteralFloat(f32),
  LiteralDouble(f64),
  LiteralString(Rc<String> /* string value */),
  Multiply(Rc<Expression>, Rc<Expression>),
  Null,
  Or(Rc<Expression>, Rc<Expression>),
  Star(Rc<Vec<String>> /* identifier parts */),
  Subtract(Rc<Expression>, Rc<Expression>),
  UnaryPlus(Rc<Expression>),
  UnaryMinus(Rc<Expression>),
}

impl Expression {
  pub fn data_type(&self) -> Res<&Type> {
    match self {
      Expression::Add(ref left, ref right) => {
        match (left.data_type()?, right.data_type()?) {
          (&Type::NULL, &Type::NULL) => Ok(&Type::NULL),
          (&Type::DOUBLE, _) => Ok(&Type::DOUBLE),
          (_, &Type::DOUBLE) => Ok(&Type::DOUBLE),
          (&Type::FLOAT, _) => Ok(&Type::FLOAT),
          (_, &Type::FLOAT) => Ok(&Type::FLOAT),
          (&Type::BIGINT, _) => Ok(&Type::BIGINT),
          (_, &Type::BIGINT) => Ok(&Type::BIGINT),
          (&Type::INT, _) => Ok(&Type::INT),
          (_, &Type::INT) => Ok(&Type::INT),
          (left, right) => {
            Err(
              Error::SQLAnalysisExpressionDataType(
                format!("Cannot reconcile data types {} and {}", left, right)
              )
            )
          },
        }
      },
      Expression::Alias(ref child, _) => child.data_type(),
      Expression::And(_, _) => Ok(&Type::BOOL),
      Expression::ColumnRef(_, ref table_info, _, ref idx) => {
        Ok(table_info.relation_fields().get()[*idx].data_type())
      },
      Expression::Divide(ref left, ref right) => {
        match (left.data_type()?, right.data_type()?) {
          (&Type::NULL, &Type::NULL) => Ok(&Type::NULL),
          (&Type::NULL, other) => Ok(other),
          (other, &Type::NULL) => Ok(other),
          (&Type::INT, &Type::INT) => Ok(&Type::DOUBLE),
          (&Type::BIGINT, &Type::INT) => Ok(&Type::DOUBLE),
          (&Type::INT, &Type::BIGINT) => Ok(&Type::DOUBLE),
          (&Type::BIGINT, &Type::BIGINT) => Ok(&Type::DOUBLE),
          (&Type::DOUBLE, _) => Ok(&Type::DOUBLE),
          (_, &Type::DOUBLE) => Ok(&Type::DOUBLE),
          (&Type::FLOAT, _) => Ok(&Type::FLOAT),
          (_, &Type::FLOAT) => Ok(&Type::FLOAT),
          (left, right) => {
            Err(
              Error::SQLAnalysisExpressionDataType(
                format!("Cannot reconcile data types {} and {}", left, right)
              )
            )
          },
        }
      },
      Expression::Equals(_, _) => Ok(&Type::BOOL),
      Expression::GreaterThan(_, _) => Ok(&Type::BOOL),
      Expression::GreaterThanEquals(_, _) => Ok(&Type::BOOL),
      Expression::Identifier(ref parts) => {
        Err(
          Error::SQLAnalysisUnresolvedExpression(
            format!("Identifier {:?} does not have a data type", parts)
          )
        )
      },
      Expression::LessThan(_, _) => Ok(&Type::BOOL),
      Expression::LessThanEquals(_, _) => Ok(&Type::BOOL),
      Expression::LiteralBool(_) => Ok(&Type::BOOL),
      Expression::LiteralInt(_) => Ok(&Type::INT),
      Expression::LiteralBigInt(_) => Ok(&Type::BIGINT),
      Expression::LiteralFloat(_) => Ok(&Type::FLOAT),
      Expression::LiteralDouble(_) => Ok(&Type::DOUBLE),
      Expression::LiteralString(_) => Ok(&Type::TEXT),
      Expression::Multiply(ref left, ref right) => {
        match (left.data_type()?, right.data_type()?) {
          (&Type::NULL, &Type::NULL) => Ok(&Type::NULL),
          (&Type::DOUBLE, _) => Ok(&Type::DOUBLE),
          (_, &Type::DOUBLE) => Ok(&Type::DOUBLE),
          (&Type::FLOAT, _) => Ok(&Type::FLOAT),
          (_, &Type::FLOAT) => Ok(&Type::FLOAT),
          (&Type::BIGINT, _) => Ok(&Type::BIGINT),
          (_, &Type::BIGINT) => Ok(&Type::BIGINT),
          (&Type::INT, _) => Ok(&Type::INT),
          (_, &Type::INT) => Ok(&Type::INT),
          (left, right) => {
            Err(
              Error::SQLAnalysisExpressionDataType(
                format!("Cannot reconcile data types {} and {}", left, right)
              )
            )
          },
        }
      },
      Expression::Null => Ok(&Type::NULL),
      Expression::Or(_, _) => Ok(&Type::BOOL),
      Expression::Star(ref parts) => {
        Err(
          Error::SQLAnalysisUnresolvedExpression(
            format!("Star expression {:?} does not have a data type", parts)
          )
        )
      },
      Expression::Subtract(ref left, ref right) => {
        match (left.data_type()?, right.data_type()?) {
          (&Type::NULL, &Type::NULL) => Ok(&Type::NULL),
          (&Type::DOUBLE, _) => Ok(&Type::DOUBLE),
          (_, &Type::DOUBLE) => Ok(&Type::DOUBLE),
          (&Type::FLOAT, _) => Ok(&Type::FLOAT),
          (_, &Type::FLOAT) => Ok(&Type::FLOAT),
          (&Type::BIGINT, _) => Ok(&Type::BIGINT),
          (_, &Type::BIGINT) => Ok(&Type::BIGINT),
          (&Type::INT, _) => Ok(&Type::INT),
          (_, &Type::INT) => Ok(&Type::INT),
          (left, right) => {
            Err(
              Error::SQLAnalysisExpressionDataType(
                format!("Cannot reconcile data types {} and {}", left, right)
              )
            )
          },
        }
      },
      Expression::UnaryPlus(ref child) => child.data_type(),
      Expression::UnaryMinus(ref child) => child.data_type(),
    }
  }

  pub fn nullable(&self) -> Res<bool> {
    match self {
      Expression::Add(ref left, ref right) => Ok(left.nullable()? || right.nullable()?),
      Expression::Alias(ref child, _) => child.nullable(),
      Expression::And(_, _) => Ok(false),
      Expression::ColumnRef(_, ref table_info, _, ref idx) => {
        Ok(table_info.relation_fields().get()[*idx].nullable())
      },
      Expression::Divide(ref left, ref right) => Ok(left.nullable()? || right.nullable()?),
      Expression::Equals(_, _) => Ok(false),
      Expression::GreaterThan(_, _) => Ok(false),
      Expression::GreaterThanEquals(_, _) => Ok(false),
      Expression::Identifier(ref parts) => {
        Err(
          Error::SQLAnalysisUnresolvedExpression(
            format!("Identifier {:?} does not have nullable status", parts)
          )
        )
      },
      Expression::LessThan(_, _) => Ok(false),
      Expression::LessThanEquals(_, _) => Ok(false),
      Expression::LiteralBool(_) => Ok(false),
      Expression::LiteralInt(_) => Ok(false),
      Expression::LiteralBigInt(_) => Ok(false),
      Expression::LiteralFloat(_) => Ok(false),
      Expression::LiteralDouble(_) => Ok(false),
      Expression::LiteralString(_) => Ok(false),
      Expression::Multiply(ref left, ref right) => Ok(left.nullable()? || right.nullable()?),
      Expression::Null => Ok(true),
      Expression::Or(ref left, ref right) => Ok(left.nullable()? || right.nullable()?),
      Expression::Star(ref parts) => {
        Err(
          Error::SQLAnalysisUnresolvedExpression(
            format!("Star expression {:?} does not have nullable status", parts)
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
      Expression::ColumnRef(_, ref table_info, _, ref index) => {
        let name = table_info.relation_fields().get()[*index].name();
        let tpe = table_info.relation_fields().get()[*index].data_type();
        write!(f, "{}#{}#{}", name, index, tpe)
      },
      Expression::Divide(ref left, ref right) => display_binary!(f, left, "/", right),
      Expression::Equals(ref left, ref right) => display_binary!(f, left, "=", right),
      Expression::GreaterThan(ref left, ref right) => display_binary!(f, left, ">", right),
      Expression::GreaterThanEquals(ref left, ref right) => display_binary!(f, left, ">=", right),
      Expression::Identifier(ref parts) => write!(f, "${}", parts.join(".")),
      Expression::LessThan(ref left, ref right) => display_binary!(f, left, "<", right),
      Expression::LessThanEquals(ref left, ref right) => display_binary!(f, left, "<=", right),
      Expression::LiteralBool(value) => write!(f, "{}", value),
      Expression::LiteralInt(value) => write!(f, "{}", value),
      Expression::LiteralBigInt(value) => write!(f, "{}", value),
      Expression::LiteralFloat(value) => write!(f, "{}", value),
      Expression::LiteralDouble(value) => write!(f, "{}", value),
      Expression::LiteralString(value) => write!(f, "{}", value),
      Expression::Multiply(ref left, ref right) => display_binary!(f, left, "x", right),
      Expression::Null => write!(f, "null"),
      Expression::Or(ref left, ref right) => display_binary!(f, left, "or", right),
      Expression::Star(ref parts) => write!(f, "{}.*", parts.join(".")),
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
      Expression::ColumnRef(_, _, _, _) => Vec::new(),
      Expression::Divide(ref left, ref right) => vec![left, right],
      Expression::Equals(ref left, ref right) => vec![left, right],
      Expression::GreaterThan(ref left, ref right) => vec![left, right],
      Expression::GreaterThanEquals(ref left, ref right) => vec![left, right],
      Expression::Identifier(_) => Vec::new(),
      Expression::LessThan(ref left, ref right) => vec![left, right],
      Expression::LessThanEquals(ref left, ref right) => vec![left, right],
      Expression::LiteralBool(_) => Vec::new(),
      Expression::LiteralInt(_) => Vec::new(),
      Expression::LiteralBigInt(_) => Vec::new(),
      Expression::LiteralFloat(_) => Vec::new(),
      Expression::LiteralDouble(_) => Vec::new(),
      Expression::LiteralString(_) => Vec::new(),
      Expression::Multiply(ref left, ref right) => vec![left, right],
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
      Expression::Identifier(parts) => Expression::Identifier(parts.clone()),
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
  Filter(Rc<Expression> /* filter expression */, Rc<LogicalPlan> /* child */),
  InsertInto(
    Rc<RelationInfo> /* table info */,
    Rc<Fields> /* columns to insert */,
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
  UnresolvedSubquery(Option<Rc<String>> /* alias */, Rc<LogicalPlan> /* child */),
  UnresolvedTableScan(
    Option<Rc<String>> /* optional schema name */,
    Rc<String> /* table name */,
    Option<Rc<String>> /* alias */,
  ),
}

impl LogicalPlan {
  // Returns the list of expressions that produce the output fields/schema for the plan node.
  pub fn output(&self) -> Res<Vec<(Rc<ExpressionContext>, Expression)>> {
    match self {
      LogicalPlan::CreateSchema(_) => Ok(Vec::new()),
      LogicalPlan::CreateTable(_, _, _) => Ok(Vec::new()),
      LogicalPlan::DropSchema(_, _) => Ok(Vec::new()),
      LogicalPlan::DropTable(_, _) => Ok(Vec::new()),
      LogicalPlan::Filter(_, ref child) => child.output(),
      LogicalPlan::InsertInto(_, _, _) => Ok(Vec::new()),
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
        let fields = table_info.relation_fields().get();
        let mut expressions = Vec::new();
        for idx in 0..fields.len() {
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
        Err(Error::SQLAnalysisUnresolvedPlan("UnresolvedCreateSchema".to_string()))
      },
      LogicalPlan::UnresolvedCreateTable(_, _, _) => {
        Err(Error::SQLAnalysisUnresolvedPlan("UnresolvedCreateTable".to_string()))
      },
      LogicalPlan::UnresolvedDropSchema(_, _) => {
        Err(Error::SQLAnalysisUnresolvedPlan("UnresolvedDropSchema".to_string()))
      },
      LogicalPlan::UnresolvedDropTable(_, _) => {
        Err(Error::SQLAnalysisUnresolvedPlan("UnresolvedDropTable".to_string()))
      },
      LogicalPlan::UnresolvedFilter(_, _) => {
        Err(Error::SQLAnalysisUnresolvedPlan("UnresolvedFilter".to_string()))
      },
      LogicalPlan::UnresolvedInsertInto(_, _, _, _) => {
        Err(Error::SQLAnalysisUnresolvedPlan("UnresolvedInsertInto".to_string()))
      },
      LogicalPlan::UnresolvedLimit(_, _) => {
        Err(Error::SQLAnalysisUnresolvedPlan("UnresolvedLimit".to_string()))
      },
      LogicalPlan::UnresolvedLocalRelation(_) => {
        Err(Error::SQLAnalysisUnresolvedPlan("UnresolvedLocalRelation".to_string()))
      },
      LogicalPlan::UnresolvedProject(_, _) => {
        Err(Error::SQLAnalysisUnresolvedPlan("UnresolvedProject".to_string()))
      },
      LogicalPlan::UnresolvedSubquery(_, _) => {
        Err(Error::SQLAnalysisUnresolvedPlan("UnresolvedSubquery".to_string()))
      },
      LogicalPlan::UnresolvedTableScan(_, _, _) => {
        Err(Error::SQLAnalysisUnresolvedPlan("UnresolvedTableScan".to_string()))
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
        write!(
          f,
          "DropTable({}.{})",
          schema_info.schema_name(),
          table_info.relation_name()
        )
      },
      LogicalPlan::Filter(_, _) => write!(f, "Filter"),
      LogicalPlan::InsertInto(_, _, _) => write!(f, "InsertInto"),
      LogicalPlan::Limit(_, _) => write!(f, "Limit"),
      LogicalPlan::LocalRelation(_) => write!(f, "LocalRelation"),
      LogicalPlan::Project(ref expressions, _) => write!(f, "Project({:?})", expressions),
      LogicalPlan::Subquery(ref alias, _) => write!(f, "Subquery({})", alias),
      LogicalPlan::TableScan(ref schema_info, ref table_info, ref alias) => {
        write!(
          f,
          "TableScan({}.{}, {:?})",
          schema_info.schema_name(),
          table_info.relation_name(),
          alias
        )
      },
      LogicalPlan::UnresolvedCreateSchema(_) => write!(f, "UnresolvedCreateSchema"),
      LogicalPlan::UnresolvedCreateTable(_, _, _) => write!(f, "UnresolvedCreateTable"),
      LogicalPlan::UnresolvedDropSchema(_, _) => write!(f, "UnresolvedDropSchema"),
      LogicalPlan::UnresolvedDropTable(_, _) => write!(f, "UnresolvedDropTable"),
      LogicalPlan::UnresolvedFilter(_, _) => write!(f, "UnresolvedFilter"),
      LogicalPlan::UnresolvedInsertInto(_, _, _, _) => write!(f, "UnresolvedInsertInto"),
      LogicalPlan::UnresolvedLimit(_, _) => write!(f, "UnresolvedLimit"),
      LogicalPlan::UnresolvedLocalRelation(_) => write!(f, "UnresolvedLocalRelation"),
      LogicalPlan::UnresolvedProject(_, _) => write!(f, "UnresolvedProject"),
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
      LogicalPlan::Filter(_, ref child) => vec![child],
      LogicalPlan::InsertInto(_, _, ref query) => vec![query],
      LogicalPlan::Limit(_, ref child) => vec![child],
      LogicalPlan::LocalRelation(_) => Vec::new(),
      LogicalPlan::Project(_, ref child) => vec![child],
      LogicalPlan::Subquery(_, ref child) => vec![child],
      LogicalPlan::TableScan(_, _, _) => Vec::new(),
      LogicalPlan::UnresolvedCreateSchema(_) => Vec::new(),
      LogicalPlan::UnresolvedCreateTable(_, _, _) => Vec::new(),
      LogicalPlan::UnresolvedDropSchema(_, _) => Vec::new(),
      LogicalPlan::UnresolvedDropTable(_, _) => Vec::new(),
      LogicalPlan::UnresolvedFilter(_, ref child) => vec![child],
      LogicalPlan::UnresolvedInsertInto(_, _, _, ref query) => vec![query],
      LogicalPlan::UnresolvedLimit(_, ref child) => vec![child],
      LogicalPlan::UnresolvedLocalRelation(_) => Vec::new(),
      LogicalPlan::UnresolvedProject(_, ref child) => vec![child],
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
      LogicalPlan::Filter(ref expression, _) => {
        let child = get_unary!("Filter", children);
        LogicalPlan::Filter(expression.clone(), Rc::new(child))
      },
      LogicalPlan::InsertInto(ref table_info, ref cols, _) => {
        let child = get_unary!("InsertInto", children);
        LogicalPlan::InsertInto(table_info.clone(), cols.clone(), Rc::new(child))
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

//=========================
// Plan and Expression DSL
//=========================

pub mod dsl {
  use std::rc::Rc;
  use super::{Expression, Fields, LogicalPlan};

  // Expressions.

  pub fn qualified_identifier(parts: Vec<&str>) -> Expression {
    Expression::Identifier(Rc::new(parts.into_iter().map(|x| x.to_string()).collect()))
  }

  pub fn identifier(name: &str) -> Expression {
    qualified_identifier(vec![name])
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
  use crate::core::trees;

  #[test]
  fn test_plan_expression_type_promotion() {
    assert_eq!(
      Expression::Alias(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new("foo".to_string())
      ).data_type(),
      Ok(&Type::INT)
    );
    assert_eq!(
      Expression::Add(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Expression::LiteralBigInt(2)),
      ).data_type(),
      Ok(&Type::BIGINT)
    );
    assert_eq!(
      Expression::And(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Expression::LiteralInt(2)),
      ).data_type(),
      Ok(&Type::BOOL)
    );
    assert_eq!(
      Expression::Divide(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Expression::LiteralInt(2)),
      ).data_type(),
      Ok(&Type::DOUBLE)
    );
    assert_eq!(
      Expression::Equals(Rc::new(Expression::Null), Rc::new(Expression::Null)).data_type(),
      Ok(&Type::BOOL)
    );
    assert_eq!(
      Expression::GreaterThan(Rc::new(Expression::Null), Rc::new(Expression::Null)).data_type(),
      Ok(&Type::BOOL)
    );
    assert_eq!(
      Expression::GreaterThanEquals(
        Rc::new(Expression::Null),
        Rc::new(Expression::Null)
      ).data_type(),
      Ok(&Type::BOOL)
    );
    assert_eq!(
      Expression::Identifier(Rc::new(vec!["foo".to_string()])).data_type(),
      Err(
        Error::SQLAnalysisUnresolvedExpression(
          "Identifier [\"foo\"] does not have a data type".to_string()
        )
      )
    );
    assert_eq!(
      Expression::LessThan(Rc::new(Expression::Null), Rc::new(Expression::Null)).data_type(),
      Ok(&Type::BOOL)
    );
    assert_eq!(
      Expression::LessThanEquals(Rc::new(Expression::Null), Rc::new(Expression::Null)).data_type(),
      Ok(&Type::BOOL)
    );
    assert_eq!(Expression::LiteralBool(true).data_type(), Ok(&Type::BOOL));
    assert_eq!(Expression::LiteralInt(1i32).data_type(), Ok(&Type::INT));
    assert_eq!(Expression::LiteralBigInt(1i64).data_type(), Ok(&Type::BIGINT));
    assert_eq!(Expression::LiteralFloat(1f32).data_type(), Ok(&Type::FLOAT));
    assert_eq!(Expression::LiteralDouble(1f64).data_type(), Ok(&Type::DOUBLE));
    assert_eq!(Expression::LiteralString(Rc::new("foo".to_string())).data_type(), Ok(&Type::TEXT));
    assert_eq!(
      Expression::Multiply(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Expression::LiteralFloat(1f32)),
      ).data_type(),
      Ok(&Type::FLOAT)
    );
    assert_eq!(Expression::Null.data_type(), Ok(&Type::NULL));
    assert_eq!(
      Expression::Or(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Expression::LiteralInt(2)),
      ).data_type(),
      Ok(&Type::BOOL)
    );
    assert_eq!(
      Expression::Star(Rc::new(vec!["foo".to_string()])).data_type(),
      Err(
        Error::SQLAnalysisUnresolvedExpression(
          "Star expression [\"foo\"] does not have a data type".to_string()
        )
      )
    );
    assert_eq!(
      Expression::Subtract(
        Rc::new(Expression::LiteralInt(1)),
        Rc::new(Expression::LiteralDouble(2f64)),
      ).data_type(),
      Ok(&Type::DOUBLE)
    );
    assert_eq!(
      Expression::UnaryPlus(Rc::new(Expression::LiteralInt(1))).data_type(),
      Ok(&Type::INT)
    );
    assert_eq!(
      Expression::UnaryMinus(Rc::new(Expression::LiteralFloat(1.1))).data_type(),
      Ok(&Type::FLOAT)
    );
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
    assert_eq!(trees::plan_output(&expr), "((1) = (2)) and (($a) < (abc))\n");

    let expr = equals(alias(qualified_identifier(vec!["a", "b"]), "col"), string("abc"));
    assert_eq!(trees::plan_output(&expr), "($a.b as col) = (abc)\n");

    let expr = equals(alias(identifier("a"), "A"), _minus(int(2)));
    assert_eq!(trees::plan_output(&expr), "($a as A) = (-2)\n");
  }
}
