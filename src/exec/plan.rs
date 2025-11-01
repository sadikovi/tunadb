use std::fmt;
use std::rc::Rc;
use crate::core::trees::TreeNode;
use crate::core::types::Fields;
use crate::exec::catalog::TableInfo;

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

#[derive(Debug, PartialEq)]
pub struct TableIdentifier {
  schema: Option<String>,
  table: String,
}

impl TableIdentifier {
  #[inline]
  pub fn new(schema: Option<String>, table: String) -> TableIdentifier {
    Self { schema, table }
  }

  #[inline]
  pub fn schema(&self) -> Option<&str> {
    self.schema.as_ref().map(|schema| schema.as_str())
  }

  #[inline]
  pub fn table(&self) -> &str {
    &self.table
  }
}

#[derive(Debug, PartialEq)]
pub enum Plan {
  CreateSchema(Rc<String> /* schema name */),
  CreateTable(Rc<TableIdentifier>, Rc<Fields> /* schema */),
  DropSchema(Rc<String> /* schema name */, bool /* cascade */),
  DropTable(Rc<TableIdentifier>),
  // Indicates an empty relation, e.g. "select 1;".
  Empty,
  Filter(Rc<Expression> /* filter expression */, Rc<Plan> /* child */),
  InsertInto(Rc<TableIdentifier>, Rc<Vec<String>> /* columns */, Rc<Plan> /* query */),
  Limit(usize /* limit */, Rc<Plan> /* child */),
  LocalRelation(Rc<Vec<Vec<Expression>>> /* expressions */),
  Project(Rc<Vec<Expression>> /* expressions */, Rc<Plan> /* child */),
  TableScan(Rc<TableInfo> /* resolved table info */, Option<Rc<String>> /* alias */),
  UnresolvedTableScan(Rc<TableIdentifier> /* table identifier */, Option<Rc<String>> /* alias */),
}

impl TreeNode<Plan> for Plan {
  #[inline]
  fn display(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Plan::CreateSchema(_) => write!(f, "CreateSchema"),
      Plan::CreateTable(_, _) => write!(f, "CreateTable"),
      Plan::DropSchema(_, _) => write!(f, "DropSchema"),
      Plan::DropTable(_) => write!(f, "DropTable"),
      Plan::Empty => write!(f, "Empty"),
      Plan::Filter(_, _) => write!(f, "Filter"),
      Plan::InsertInto(_, _, _) => write!(f, "InsertInto"),
      Plan::Limit(_, _) => write!(f, "Limit"),
      Plan::LocalRelation(_) => write!(f, "LocalRelation"),
      Plan::Project(_, _) => write!(f, "Project"),
      Plan::TableScan(_, _) => write!(f, "TableScan"),
      Plan::UnresolvedTableScan(_, _) => write!(f, "UnresolvedTableScan"),
    }
  }

  #[inline]
  fn as_ref(&self) -> &Plan {
    self
  }

  #[inline]
  fn children(&self) -> Vec<&Plan> {
    match self {
      Plan::CreateSchema(_) => Vec::new(),
      Plan::CreateTable(_, _) => Vec::new(),
      Plan::DropSchema(_, _) => Vec::new(),
      Plan::DropTable(_) => Vec::new(),
      Plan::Empty => Vec::new(),
      Plan::Filter(_, ref child) => vec![child],
      Plan::InsertInto(_, _, ref query) => vec![query],
      Plan::Limit(_, ref child) => vec![child],
      Plan::LocalRelation(_) => Vec::new(),
      Plan::Project(_, ref child) => vec![child],
      Plan::TableScan(_, _) => Vec::new(),
      Plan::UnresolvedTableScan(_, _) => Vec::new(),
    }
  }

  #[inline]
  fn copy(&self, mut children: Vec<Plan>) -> Plan {
    match self {
      Plan::CreateSchema(ref schema_name) => {
        Plan::CreateSchema(schema_name.clone())
      },
      Plan::CreateTable(ref ident, ref schema) => {
        Plan::CreateTable(ident.clone(), schema.clone())
      },
      Plan::DropSchema(ref schema_name, cascade) => {
        Plan::DropSchema(schema_name.clone(), *cascade)
      },
      Plan::DropTable(ref ident) => {
        Plan::DropTable(ident.clone())
      },
      Plan::Empty => {
        Plan::Empty
      },
      Plan::Filter(ref expression, _) => {
        let child = get_unary!("Filter", children);
        Plan::Filter(expression.clone(), Rc::new(child))
      },
      Plan::InsertInto(ref table_ident, ref cols, ref query) => {
        Plan::InsertInto(table_ident.clone(), cols.clone(), query.clone())
      },
      Plan::Limit(limit, _) => {
        let child = get_unary!("Limit", children);
        Plan::Limit(*limit, Rc::new(child))
      },
      Plan::LocalRelation(ref expressions) => {
        Plan::LocalRelation(expressions.clone())
      },
      Plan::Project(expressions, _) => {
        let child = get_unary!("Project", children);
        Plan::Project(expressions.clone(), Rc::new(child))
      },
      Plan::TableScan(ref info, ref table_alias) => {
        Plan::TableScan(info.clone(), table_alias.clone())
      },
      Plan::UnresolvedTableScan(ref table_ident, ref table_alias) => {
        Plan::UnresolvedTableScan(table_ident.clone(), table_alias.clone())
      },
    }
  }
}

#[derive(Debug, PartialEq)]
pub enum Expression {
  Add(Rc<Expression>, Rc<Expression>),
  Alias(Rc<Expression>, Rc<String> /* alias name */),
  And(Rc<Expression>, Rc<Expression>),
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

//========================
// Plan and Expression DSL
//========================

pub mod dsl {
  use std::rc::Rc;
  use super::{Expression, Fields, Plan, TableIdentifier};

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

  // Plan nodes.

  pub fn create_schema(schema: &str) -> Plan {
    Plan::CreateSchema(Rc::new(schema.to_string()))
  }

  pub fn create_table(schema: Option<&str>, table: &str, fields: Fields) -> Plan {
    let table_ident = TableIdentifier::new(
      schema.map(|x| x.to_string()),
      table.to_string()
    );
    Plan::CreateTable(Rc::new(table_ident), Rc::new(fields))
  }

  pub fn drop_schema(schema: &str, is_cascade: bool) -> Plan {
    Plan::DropSchema(Rc::new(schema.to_string()), is_cascade)
  }

  pub fn drop_table(schema: Option<&str>, table: &str) -> Plan {
    let table_ident = TableIdentifier::new(
      schema.map(|x| x.to_string()),
      table.to_string()
    );
    Plan::DropTable(Rc::new(table_ident))
  }

  pub fn empty() -> Plan {
    Plan::Empty
  }

  pub fn filter(expression: Expression, child: Plan) -> Plan {
    Plan::Filter(Rc::new(expression), Rc::new(child))
  }

  pub fn from(schema: Option<&str>, table: &str, alias: Option<&str>) -> Plan {
    let table_ident = TableIdentifier::new(
      schema.map(|x| x.to_string()),
      table.to_string()
    );
    let table_alias = alias.map(|x| Rc::new(x.to_string()));
    Plan::UnresolvedTableScan(Rc::new(table_ident), table_alias)
  }

  pub fn insert_into_values(
    schema: Option<&str>,
    table: &str,
    cols: Vec<String>,
    expr: Vec<Vec<Expression>>
  ) -> Plan {
    insert_into_select(schema, table, cols, Plan::LocalRelation(Rc::new(expr)))
  }

  pub fn insert_into_select(
    schema: Option<&str>,
    table: &str,
    cols: Vec<String>,
    query: Plan
  ) -> Plan {
    let table_ident = TableIdentifier::new(
      schema.map(|x| x.to_string()),
      table.to_string()
    );
    Plan::InsertInto(
      Rc::new(table_ident),
      Rc::new(cols),
      Rc::new(query)
    )
  }

  pub fn limit(value: usize, child: Plan) -> Plan {
    Plan::Limit(value, Rc::new(child))
  }

  pub fn project(expressions: Vec<Expression>, child: Plan) -> Plan {
    Plan::Project(Rc::new(expressions), Rc::new(child))
  }
}

#[cfg(test)]
pub mod tests {
  use super::dsl::*;
  use crate::core::trees;

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
