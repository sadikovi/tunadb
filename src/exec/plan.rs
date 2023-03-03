use std::fmt;
use std::rc::Rc;
use crate::common::trees::TreeNode;

#[derive(Debug, PartialEq)]
pub enum Plan {
  Filter(Rc<Expression> /* filter expression */, Rc<Plan> /* child */),
  Limit(usize /* limit */, Rc<Plan> /* child */),
  Project(Vec<Expression> /* expressions */, Rc<Plan>),
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
  fn copy(&self, children: Vec<Plan>) -> Plan {
    match self {
      Plan::Filter(ref expression, ref child) => unimplemented!(),
      Plan::Limit(limit, ref child) => unimplemented!(),
      Plan::Project(expressions, ref child) => unimplemented!(),
      Plan::TableScan(ref schema, ref name) => unimplemented!(),
      Plan::Empty => unimplemented!(),
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

macro_rules! copy_binary {
  ($tpe:expr, $name:expr, $children:expr) => {{
    assert_eq!(
      $children.len(),
      2,
      "Expected 2 child nodes for {} binary expression but found {}",
      $name,
      $children.len()
    );
    let right = $children.pop().unwrap();
    let left = $children.pop().unwrap();
    $tpe(Rc::new(left), Rc::new(right))
  }}
}

macro_rules! copy_unary {
  ($tpe:expr, $name:expr, $children:expr) => {{
    assert_eq!(
      $children.len(),
      1,
      "Expected 1 child node for {} unary expression but found {}",
      $name,
      $children.len()
    );
    let child = $children.pop().unwrap();
    $tpe(Rc::new(child))
  }}
}

macro_rules! display_binary {
  ($f:expr, $left:expr, $op:expr, $right:expr) => {{
    $left.display($f)?;
    write!($f, " {} ", $op)?;
    $right.display($f)
  }}
}

macro_rules! display_unary {
  ($f:expr, $op:expr, $child:expr) => {{
    write!($f, "{}", $op)?;
    $child.display($f)
  }}
}

impl TreeNode<Expression> for Expression {
  #[inline]
  fn display(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Expression::Add(ref left, ref right) => display_binary!(f, left, "+", right),
      Expression::Alias(ref child, ref name) => {
        child.display(f)?;
        write!(f, "as {}", name)
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
      Expression::Add(_, _) => copy_binary!(Expression::Add, "Add", children),
      Expression::Alias(_, ref name) => {
        assert_eq!(
          children.len(),
          1,
          "Expected 1 child for Alias expression but found {}",
          children.len()
        );
        let child = children.pop().unwrap();
        Expression::Alias(Rc::new(child), name.clone())
      },
      Expression::And(_, _) => copy_binary!(Expression::And, "And", children),
      Expression::Divide(_, _) => copy_binary!(Expression::Divide, "Divide", children),
      Expression::Equals(_, _) => copy_binary!(Expression::Equals, "Equals", children),
      Expression::GreaterThan(_, _) => copy_binary!(Expression::GreaterThan, "GreaterThan", children),
      Expression::GreaterThanEquals(_, _) => copy_binary!(Expression::GreaterThanEquals, "GreaterThanEquals", children),
      Expression::Identifier(value) => Expression::Identifier(value.clone()),
      Expression::LessThan(_, _) => copy_binary!(Expression::LessThan, "LessThan", children),
      Expression::LessThanEquals(_, _) => copy_binary!(Expression::LessThanEquals, "LessThanEquals", children),
      Expression::LiteralNumber(value) => Expression::LiteralNumber(value.clone()),
      Expression::LiteralString(value) => Expression::LiteralString(value.clone()),
      Expression::Multiply(_, _) => copy_binary!(Expression::Multiply, "Multiply", children),
      Expression::Null => Expression::Null,
      Expression::Or(_, _) => copy_binary!(Expression::Or, "Or", children),
      Expression::Star => Expression::Star,
      Expression::Subtract(_, _) => copy_binary!(Expression::Subtract, "Subtract", children),
      Expression::UnaryPlus(_) => copy_unary!(Expression::UnaryPlus, "UnaryPlus", children),
      Expression::UnaryMinus(_) => copy_unary!(Expression::UnaryMinus, "UnaryMinus", children),
    }
  }
}
