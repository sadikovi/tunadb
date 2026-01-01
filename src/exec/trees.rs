use std::fmt;
use crate::common::error::Res;

// Generic `TreeNode` to provide traversal and transform.
pub trait TreeNode<A> {
  // Defines how the node is displayed in the tree.
  // The following constraints apply:
  // - use `write!` instead of `writeln!`, each node must occupy only one line, no `\n`.
  // - the name should preferrably be short but descriptive.
  fn display(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;

  // Returns a reference to itself.
  // This is needed to downcast to the A reference.
  fn as_ref(&self) -> &A;

  // Returns a list of children for the node.
  // Can return an empty list if there are no children.
  fn children(&self) -> Vec<&A>;

  // Copies the node with the new set of children.
  // This method must be implemented in a way so it is cheap to make a copy, e.g.
  // by using Rc or some other ways of shared ownership.
  fn copy(&self, children: Vec<A>) -> A;
}

// Rule to transform a tree.
pub trait Rule<A> {
  // Applies the rule on the `node`.
  // The function can return:
  // - Ok(Some(new_node)), where the new_node is a new subtree that replaces node.
  // - Ok(None), means the rule did not apply, the node should remain unchanged.
  // - Err(_), error during the rule resolution.
  fn apply(&self, node: &A) -> Res<Option<A>>;
}

// Returns a copy of this node where the `rule` has been recursively applied to it and
// all of its children (pre-order). When the `rule` does not apply to a given node it
// is left unchanged.
pub fn transform_down<A>(node: &A, rule: &dyn Rule<A>) -> Res<A> where A: TreeNode<A> {
  let binding = rule.apply(node)?;
  let node = binding.as_ref().unwrap_or(node);

  let mut children = Vec::new();
  for child in node.children() {
    let updated = transform_down(child.as_ref(), rule)?;
    children.push(updated);
  }

  Ok(node.copy(children))
}

// Returns a copy of this node where the `rule` has been recursively applied first to all
// of its children and then itself (post-order). When the `rule` does not apply to a given
// node, it is left unchanged.
pub fn transform_up<A>(node: &A, rule: &dyn Rule<A>) -> Res<A> where A: TreeNode<A> {
  let mut children = Vec::new();
  for child in node.children() {
    let updated = transform_up(child.as_ref(), rule)?;
    children.push(updated);
  }

  let node = node.copy(children);
  Ok(rule.apply(&node)?.unwrap_or(node))
}

// Expanded plan tree display.
struct PlanTreeDisplay<'a, A: TreeNode<A>> {
  plan: &'a A
}

impl<'a, A: TreeNode<A>> fmt::Display for PlanTreeDisplay<'a, A> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    recur_gen_tree(self.plan, &mut Vec::new(), f)
  }
}

// Simple single-line display of the plan node.
struct PlanSimpleDisplay<'a, A: TreeNode<A>> {
  plan: &'a A
}

impl<'a, A: TreeNode<A>> fmt::Display for PlanSimpleDisplay<'a, A> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.plan.display(f)?;
    writeln!(f)
  }
}

// Internal method to generate tree string.
#[inline]
fn recur_gen_tree<A>(
  plan: &A,
  buf: &mut Vec<bool>,
  f: &mut fmt::Formatter<'_>
) -> fmt::Result where A: TreeNode<A> {
  plan.display(f)?;
  writeln!(f)?;

  // Add child levels.
  let children = plan.children();
  let len = children.len();

  let pos = buf.len();
  buf.push(true);
  for i in 0..len {
    buf[pos] = i < len - 1;
    for j in 0..buf.len() {
      if buf[j] && j != pos {
        write!(f, ":  ")?;
      } else if buf[j] && j == pos {
        write!(f, ":- ")?;
      } else if !buf[j] && j == pos {
        write!(f, "+- ")?;
      } else {
        write!(f, "   ")?;
      }
    }
    recur_gen_tree(children[i], buf, f)?;
  }
  buf.pop();

  Ok(())
}

// Returns a string of the tree output.
pub fn tree_output<A>(plan: &A) -> String where A: TreeNode<A> {
  let output = PlanTreeDisplay { plan };
  output.to_string()
}

// Returns a string of the tree output.
pub fn plan_output<A>(plan: &A) -> String where A: TreeNode<A> {
  let output = PlanSimpleDisplay { plan };
  output.to_string()
}

#[cfg(test)]
mod tests {
  use super::*;

  #[derive(Debug, PartialEq)]
  struct TestNode {
    name: String,
    children: Vec<TestNode>,
  }

  impl TestNode {
    fn new(name: &str, children: Vec<TestNode>) -> Self {
      Self { name: name.to_owned(), children }
    }
  }

  impl TreeNode<TestNode> for TestNode {
    fn display(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      write!(f, "{}", self.name)
    }

    fn as_ref(&self) -> &TestNode {
      self
    }

    fn children(&self) -> Vec<&TestNode> {
      self.children.iter().map(|node| node).collect()
    }

    fn copy(&self, children: Vec<TestNode>) -> TestNode {
      Self::new(&self.name, children)
    }
  }

  // Helper method that returns a simple test tree.
  fn get_test_tree() -> TestNode {
    TestNode::new(
      "A",
      vec![
        TestNode::new(
          "B",
          vec![
            TestNode::new("C", vec![]),
            TestNode::new("D", vec![]),
          ]
        ),
        TestNode::new("E", vec![]),
      ]
    )
  }

  struct NoopRule {
  }

  impl Rule<TestNode> for NoopRule {
    fn apply(&self, _node: &TestNode) -> Res<Option<TestNode>> {
      Ok(None)
    }
  }

  #[test]
  fn test_trees_transform_up_not_modified() {
    let rule = NoopRule {};

    let node = TestNode::new("A", vec![]);
    let res = transform_up(&node, &rule).unwrap();
    assert_eq!(res, node);

    let node = get_test_tree();
    let res = transform_up(&node, &rule).unwrap();
    assert_eq!(res, node);
  }

  struct RenameRule {
  }

  impl Rule<TestNode> for RenameRule {
    fn apply(&self, node: &TestNode) -> Res<Option<TestNode>> {
      if &node.name == "A" {
        Ok(Some(TestNode::new("Ap", vec![TestNode::new("B", vec![])])))
      } else if &node.name == "B" {
        Ok(Some(TestNode::new("Bp", vec![TestNode::new("C", vec![])])))
      } else {
        Ok(None)
      }
    }
  }

  #[test]
  fn test_trees_transform_up_modified() {
    let rule = RenameRule {};

    let node = TestNode::new("A", vec![]);
    let res = transform_up(&node, &rule).unwrap();
    assert_eq!(res, TestNode::new("Ap", vec![TestNode::new("B", vec![])]));

    let node = get_test_tree();
    let res = transform_up(&node, &rule).unwrap();
    assert_eq!(res, TestNode::new("Ap", vec![TestNode::new("B", vec![])]));
  }

  #[test]
  fn test_trees_transform_down_not_modified() {
    let rule = NoopRule {};

    let node = TestNode::new("A", vec![]);
    let res = transform_down(&node, &rule).unwrap();
    assert_eq!(res, node);

    let node = get_test_tree();
    let res = transform_down(&node, &rule).unwrap();
    assert_eq!(res, node);
  }

  struct Rename2Rule {
  }

  impl Rule<TestNode> for Rename2Rule {
    fn apply(&self, node: &TestNode) -> Res<Option<TestNode>> {
      if &node.name == "A" {
        Ok(Some(TestNode::new("Ap", vec![TestNode::new("B", vec![])])))
      } else if &node.name == "B" {
        Ok(Some(TestNode::new("Bp", vec![TestNode::new("Cp", vec![])])))
      } else {
        Ok(None)
      }
    }
  }

  #[test]
  fn test_trees_transform_down_modified() {
    let rule = Rename2Rule {};

    let exp = TestNode::new(
      "Ap",
      vec![
        TestNode::new(
          "Bp",
          vec![
            TestNode::new("Cp", vec![])
          ]
        )
      ]
    );

    let node = TestNode::new("A", vec![]);
    let res = transform_down(&node, &rule).unwrap();
    assert_eq!(res, exp);

    let node = get_test_tree();
    let res = transform_down(&node, &rule).unwrap();
    assert_eq!(res, exp);
  }

  #[test]
  fn test_trees_output() {
    let node = TestNode::new("A", vec![]);
    assert_eq!(tree_output(&node).trim(), "A");

    let node = TestNode::new(
      "A",
      vec![
        TestNode::new("B", vec![]),
        TestNode::new("C", vec![]),
      ]
    );
    assert_eq!(
      tree_output(&node).trim(),
      vec![
        "A",
        ":- B",
        "+- C"
      ].join("\n")
    );

    let node = TestNode::new(
      "A",
      vec![
        TestNode::new(
          "B",
          vec![
            TestNode::new("C", vec![]),
          ]
        ),
      ]
    );
    assert_eq!(
      tree_output(&node).trim(),
      vec![
        "A",
        "+- B",
        "   +- C"
      ].join("\n")
    );

    let node = TestNode::new(
      "A",
      vec![
        TestNode::new(
          "B",
          vec![
            TestNode::new("C", vec![]),
            TestNode::new("D", vec![]),
          ]
        ),
        TestNode::new(
          "E",
          vec![
            TestNode::new("F", vec![]),
          ]
        ),
      ]
    );

    assert_eq!(
      tree_output(&node).trim(),
      vec![
        "A",
        ":- B",
        ":  :- C",
        ":  +- D",
        "+- E",
        "   +- F"
      ].join("\n")
    );
  }
}
