use std::fmt;
use std::rc::Rc;
use crate::common::trees::TreeNode;

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
pub enum Plan {
  Filter(Rc<Expression> /* filter expression */, Rc<Plan> /* child */),
  Limit(usize /* limit */, Rc<Plan> /* child */),
  Project(Rc<Vec<Expression>> /* expressions */, Rc<Plan> /* child */),
  TableScan(Option<Rc<String>> /* schema */, Rc<String> /* table name */),
  Empty, // indicates an empty relation, e.g. "select 1;"
}

impl TreeNode<Plan> for Plan {
  #[inline]
  fn display(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Plan::Filter(_, _) => write!(f, "Filter"),
      Plan::Limit(_, _) => write!(f, "Limit"),
      Plan::Project(_, _) => write!(f, "Project"),
      Plan::TableScan(_, _) => write!(f, "TableScan"),
      Plan::Empty => write!(f, "Empty"),
    }
  }

  #[inline]
  fn as_ref(&self) -> &Plan {
    self
  }

  #[inline]
  fn children(&self) -> Vec<&Plan> {
    match self {
      Plan::Filter(_, ref child) => vec![child],
      Plan::Limit(_, ref child) => vec![child],
      Plan::Project(_, ref child) => vec![child],
      Plan::TableScan(_, _) => Vec::new(),
      Plan::Empty => Vec::new(),
    }
  }

  #[inline]
  fn copy(&self, mut children: Vec<Plan>) -> Plan {
    match self {
      Plan::Filter(ref expression, _) => {
        let child = get_unary!("Filter", children);
        Plan::Filter(expression.clone(), Rc::new(child))
      },
      Plan::Limit(limit, _) => {
        let child = get_unary!("Limit", children);
        Plan::Limit(*limit, Rc::new(child))
      },
      Plan::Project(expressions, _) => {
        let child = get_unary!("Project", children);
        Plan::Project(expressions.clone(), Rc::new(child))
      },
      Plan::TableScan(ref schema, ref name) => {
        Plan::TableScan(schema.clone(), name.clone())
      },
      Plan::Empty => Plan::Empty,
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
  Identifier(Rc<String> /* identifier value */),
  LessThan(Rc<Expression>, Rc<Expression>),
  LessThanEquals(Rc<Expression>, Rc<Expression>),
  LiteralNumber(Rc<String> /* numeric value */),
  LiteralString(Rc<String> /* string value */),
  Multiply(Rc<Expression>, Rc<Expression>),
  Null,
  Or(Rc<Expression>, Rc<Expression>),
  Star,
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
      Expression::Identifier(value) => write!(f, "${}", value),
      Expression::LessThan(ref left, ref right) => display_binary!(f, left, "<", right),
      Expression::LessThanEquals(ref left, ref right) => display_binary!(f, left, "<=", right),
      Expression::LiteralNumber(value) => write!(f, "{}", value),
      Expression::LiteralString(value) => write!(f, "{}", value),
      Expression::Multiply(ref left, ref right) => display_binary!(f, left, "x", right),
      Expression::Null => write!(f, "null"),
      Expression::Or(ref left, ref right) => display_binary!(f, left, "or", right),
      Expression::Star => write!(f, "*"),
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
      Expression::LiteralNumber(_) => Vec::new(),
      Expression::LiteralString(_) => Vec::new(),
      Expression::Multiply(ref left, ref right) => vec![left, right],
      Expression::Null => Vec::new(),
      Expression::Or(ref left, ref right) => vec![left, right],
      Expression::Star => Vec::new(),
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
      Expression::Identifier(value) => Expression::Identifier(value.clone()),
      Expression::LessThan(_, _) => {
        let (left, right) = get_binary!("LessThan", children);
        Expression::LessThan(Rc::new(left), Rc::new(right))
      },
      Expression::LessThanEquals(_, _) => {
        let (left, right) = get_binary!("LessThanEquals", children);
        Expression::LessThanEquals(Rc::new(left), Rc::new(right))
      },
      Expression::LiteralNumber(value) => Expression::LiteralNumber(value.clone()),
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
      Expression::Star => Expression::Star,
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
  use super::{Expression, Plan};

  pub fn identifier(name: &str) -> Expression {
    Expression::Identifier(Rc::new(name.to_string()))
  }

  pub fn number(value: &str) -> Expression {
    Expression::LiteralNumber(Rc::new(value.to_string()))
  }

  pub fn string(value: &str) -> Expression {
    Expression::LiteralString(Rc::new(format!("'{}'", value)))
  }

  pub fn null() -> Expression {
    Expression::Null
  }

  pub fn star() -> Expression {
    Expression::Star
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

  pub fn filter(expression: Expression, child: Plan) -> Plan {
    Plan::Filter(Rc::new(expression), Rc::new(child))
  }

  pub fn project(expressions: Vec<Expression>, child: Plan) -> Plan {
    Plan::Project(Rc::new(expressions), Rc::new(child))
  }

  pub fn empty() -> Plan {
    Plan::Empty
  }

  pub fn from(schema: Option<&str>, table: &str) -> Plan {
    Plan::TableScan(schema.map(|x| Rc::new(x.to_string())), Rc::new(table.to_string()))
  }

  pub fn limit(value: usize, child: Plan) -> Plan {
    Plan::Limit(value, Rc::new(child))
  }
}

#[cfg(test)]
pub mod tests {
  use super::dsl::*;
  use crate::common::trees;

  #[test]
  fn test_plan_display() {
    let expr = and(equals(number("1"), number("2")), less_than(identifier("a"), string("abc")));
    assert_eq!(trees::plan_output(&expr), "((1) = (2)) and (($a) < ('abc'))\n");

    let expr = equals(alias(identifier("a"), "A"), _minus(number("2")));
    assert_eq!(trees::plan_output(&expr), "($a as A) = (-2)\n");
  }
}
