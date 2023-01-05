// Generic `TreeNode` to provide traversal and transform.
pub trait TreeNode<A> {
  // Returns a short and descriptive name of the tree node.
  // This is only used when printing the tree for debugging or visualising the plan.
  fn debug_name(&self) -> String;

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

// Return a copy of this node where the `rule` has been recursively applied first to all
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

/// Internal method to generate tree string.
fn recur_gen_tree<A>(
  plan: &A,
  depth: usize,
  prefix: &str,
  is_last_child: bool,
  buf: &mut Vec<String>
) where A: TreeNode<A> {
  let parent_prefix = if depth == 0 { "" } else if is_last_child { "+- " } else { "- " };
  // Generate prefix for current node.
  let curr = format!("{}{}{}", prefix, parent_prefix, plan.debug_name());
  buf.push(curr);

  // Add child levels.
  let children = plan.children();
  let len = children.len();

  for i in 0..len {
    let is_last_child = i == len - 1;
    let prefix = format!(
      "{}{}{}",
      prefix,
      " ".repeat(parent_prefix.len()),
      if is_last_child { "" } else { ":" }
    );
    recur_gen_tree(&children[i], depth + 1, &prefix, is_last_child, buf);
  }
}

// Collects tree output into the provided buffer.
// Each line represents a node in the tree.
pub fn tree_output<A>(plan: &A, buffer: &mut Vec<String>) where A: TreeNode<A> {
  recur_gen_tree(plan, 0, "", false, buffer);
}

// Returns a string of the tree output.
pub fn tree_string<A>(plan: &A) -> String where A: TreeNode<A> {
  let mut buffer = Vec::new();
  tree_output(plan, &mut buffer);
  buffer.join("\n")
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
    fn debug_name(&self) -> String {
      self.name.clone()
    }

    fn as_ref(&self) -> &TestNode {
      self
    }

    fn children(&self) -> &[TestNode] {
      &self.children
    }

    fn copy(&self, children: Vec<TestNode>) -> TestNode {
      Self::new(&self.debug_name(), children)
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
      if n.debug_name() == "A" {
        Some(TestNode::new("Ap", vec![TestNode::new("B", vec![])]))
      } else if n.debug_name() == "B" {
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
      if n.debug_name() == "A" {
        Some(TestNode::new("Ap", vec![TestNode::new("B", vec![])]))
      } else if n.debug_name() == "B" {
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
    assert_eq!(&tree_string(&node), "A");

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
      tree_string(&node),
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
      tree_string(&node),
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
