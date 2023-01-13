use std::fmt;

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
  fn children(&self) -> &[A];

  // Copies the node with the new set of children.
  fn copy(&self, children: Vec<A>) -> A;
}

// Returns a copy of this node where the `rule` has been recursively applied to it and
// all of its children (pre-order). When the `rule` does not apply to a given node it
// is left unchanged.
pub fn transform_down<A, R>(node: &A, rule: &R) -> A where A: TreeNode<A>, R: Fn(&A) -> Option<A> {
  let binding = rule(node);
  let node = binding.as_ref().unwrap_or(node);

  let mut children = Vec::new();
  for child in node.children() {
    let updated = transform_down(child.as_ref(), rule);
    children.push(updated);
  }

  node.copy(children)
}

// Returns a copy of this node where the `rule` has been recursively applied first to all
// of its children and then itself (post-order). When the `rule` does not apply to a given
// node, it is left unchanged.
pub fn transform_up<A, R>(node: &A, rule: &R) -> A where A: TreeNode<A>, R: Fn(&A) -> Option<A> {
  let mut children = Vec::new();
  for child in node.children() {
    let updated = transform_up(child.as_ref(), rule);
    children.push(updated);
  }

  let node = node.copy(children);
  rule(&node).unwrap_or(node)
}

struct TreeDisplay<'a, A: TreeNode<A>> {
  plan: &'a A
}

impl<'a, A: TreeNode<A>> fmt::Display for TreeDisplay<'a, A> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    recur_gen_tree(self.plan, &mut Vec::new(), f)
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
    recur_gen_tree(&children[i], buf, f)?;
  }
  buf.pop();

  Ok(())
}

// Returns a string of the tree output.
pub fn tree_string<A>(plan: &A) -> String where A: TreeNode<A> {
  let tree = TreeDisplay { plan };
  tree.to_string()
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
      Self { name: name.to_string(), children }
    }
  }

  impl TreeNode<TestNode> for TestNode {
    fn display(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      write!(f, "{}", self.name)
    }

    fn as_ref(&self) -> &TestNode {
      self
    }

    fn children(&self) -> &[TestNode] {
      &self.children
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

  #[test]
  fn test_trees_transform_up_not_modified() {
    let node = TestNode::new("A", vec![]);
    let res = transform_up(&node, &|_| None);
    assert_eq!(res, node);

    let node = get_test_tree();
    let res = transform_up(&node, &|_| None);
    assert_eq!(res, node);
  }

  #[test]
  fn test_trees_transform_up_modified() {
    let rule = |n: &TestNode| {
      if n.name == "A" {
        Some(TestNode::new("Ap", vec![TestNode::new("B", vec![])]))
      } else if n.name == "B" {
        Some(TestNode::new("Bp", vec![TestNode::new("C", vec![])]))
      } else {
        None
      }
    };

    let node = TestNode::new("A", vec![]);
    let res = transform_up(&node, &rule);
    assert_eq!(res, TestNode::new("Ap", vec![TestNode::new("B", vec![])]));

    let node = get_test_tree();
    let res = transform_up(&node, &rule);
    assert_eq!(res, TestNode::new("Ap", vec![TestNode::new("B", vec![])]));
  }

  #[test]
  fn test_trees_transform_down_not_modified() {
    let node = TestNode::new("A", vec![]);
    let res = transform_down(&node, &|_| None);
    assert_eq!(res, node);

    let node = get_test_tree();
    let res = transform_down(&node, &|_| None);
    assert_eq!(res, node);
  }

  #[test]
  fn test_trees_transform_down_modified() {
    let rule = |n: &TestNode| {
      if n.name == "A" {
        Some(TestNode::new("Ap", vec![TestNode::new("B", vec![])]))
      } else if n.name == "B" {
        Some(TestNode::new("Bp", vec![TestNode::new("Cp", vec![])]))
      } else {
        None
      }
    };

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
    let res = transform_down(&node, &rule);
    assert_eq!(res, exp);

    let node = get_test_tree();
    let res = transform_down(&node, &rule);
    assert_eq!(res, exp);
  }

  #[test]
  fn test_trees_output() {
    let node = TestNode::new("A", vec![]);
    assert_eq!(&tree_string(&node), "A\n");

    let node = TestNode::new(
      "A",
      vec![
        TestNode::new("B", vec![]),
        TestNode::new("C", vec![]),
      ]
    );
    assert_eq!(
      tree_string(&node),
      vec![
        "A",
        ":- B",
        "+- C",
        ""
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
      tree_string(&node),
      vec![
        "A",
        "+- B",
        "   +- C",
        ""
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
      tree_string(&node),
      vec![
        "A",
        ":- B",
        ":  :- C",
        ":  +- D",
        "+- E",
        "   +- F",
        ""
      ].join("\n")
    );

    let node = TestNode::new(
      "A",
      vec![
        TestNode::new(
          "B",
          vec![
            TestNode::new("C", vec![
              TestNode::new("N1", vec![
                TestNode::new("N11", vec![]),
                TestNode::new("N12", vec![]),
              ]),
              TestNode::new("N2", vec![]),
            ]),
            TestNode::new("D", vec![
              TestNode::new("N1", vec![]),
              TestNode::new("N2", vec![]),
              TestNode::new("N3", vec![]),
              TestNode::new("N4", vec![]),
              TestNode::new("N5", vec![]),
            ]),
          ]
        ),
        TestNode::new(
          "E",
          vec![
            TestNode::new("F", vec![
              TestNode::new("G", vec![
                TestNode::new("H", vec![]),
              ]),
            ]),
            TestNode::new("Z", vec![]),
          ]
        ),
      ]
    );

    assert_eq!(
      tree_string(&node),
      vec![
        "A",
        ":- B",
        ":  :- C",
        ":  :  :- N1",
        ":  :  :  :- N11",
        ":  :  :  +- N12",
        ":  :  +- N2",
        ":  +- D",
        ":     :- N1",
        ":     :- N2",
        ":     :- N3",
        ":     :- N4",
        ":     +- N5",
        "+- E",
        "   :- F",
        "   :  +- G",
        "   :     +- H",
        "   +- Z",
        ""
      ].join("\n")
    );
  }
}
