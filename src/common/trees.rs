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
  fn children(&self) -> Vec<&A>;

  // Copies the node with the new set of children.
  // This method must be implemented in a way so it is cheap to make a copy, e.g.
  // by using Rc or some other ways of shared ownership.
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
    recur_gen_tree(children[i], buf, f)?;
  }
  buf.pop();

  Ok(())
}

// Returns a string of the tree output.
pub fn tree_string<A>(plan: &A) -> String where A: TreeNode<A> {
  let tree = TreeDisplay { plan };
  tree.to_string()
}
