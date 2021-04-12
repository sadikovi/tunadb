use std::fmt;

const MAX_VALUES: usize = 5;

#[derive(Clone, Debug)]
struct Node {
  id: usize,
  is_leaf: bool,
  keys: [i32; MAX_VALUES],
  values: [i32; MAX_VALUES],
  pointers: [usize; MAX_VALUES + 1],
  len: usize, // number of keys in the node
}

impl Node {
  // Creates a new node.
  pub fn new(id: usize, is_leaf: bool) -> Self {
    Self {
      id: id,
      is_leaf: is_leaf,
      keys: [0; MAX_VALUES],
      values: [0; MAX_VALUES],
      pointers: [0; MAX_VALUES + 1],
      len: 0,
    }
  }
}

impl fmt::Display for Node {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if self.is_leaf {
      write!(f, "L ({}) {:?} {:?}", self.id, &self.keys[0..self.len], &self.values[0..self.len])
    } else {
      write!(f, "I ({}) {:?} {:?}", self.id, &self.keys[0..self.len], &self.pointers[0..self.len + 1])
    }
  }
}

// Returns true if key exists and position to insert
fn search(keys: &[i32], key: i32) -> (bool, usize) {
  let mut start = 0;
  let mut end = keys.len();
  // "start" would point to the insertion point where keys[start] >= key
  while start < end {
    let pivot = (start + end - 1) >> 1;
    if key < keys[pivot] {
      end = pivot;
    } else if key > keys[pivot] {
      start = pivot + 1;
    } else {
      return (true, pivot);
    }
  }
  (false, start)
}

// Inserts into a leaf node at position i
fn insert_leaf(node: &mut Node, exists: bool, i: usize, key: i32, value: i32) {
  if !exists {
    for k in (i..node.len).rev() {
      node.keys[k + 1] = node.keys[k];
      node.values[k + 1] = node.values[k];
    }
    node.len += 1;
  }
  node.keys[i] = key;
  node.values[i] = value;
}

// Both nodes left_id and right_id are children of the provided node
fn insert_internal(node: &mut Node, sp: usize, key: i32, left_id: usize, right_id: usize) {
  // Update the current pointer to the new right node
  node.pointers[sp] = right_id;
  // Shift elements (keys and pointers) after sep to the right, skip the sp
  for i in (sp..node.len).rev() {
    node.keys[i + 1] = node.keys[i];
  }
  for i in (sp..node.len + 1).rev() {
    node.pointers[i + 1] = node.pointers[i];
  }
  node.keys[sp] = key;
  node.pointers[sp] = left_id;
  node.len += 1; // inserted a new key
}

// Split the node (and update it) and return a new node + split key
fn split_leaf(from: &mut Node, to: &mut Node) -> i32 {
  let sp = (from.len >> 1) + 1; // split point
  let key = from.keys[sp]; // split key to propagate to the parent
  for i in sp..from.len {
    to.keys[i - sp] = from.keys[i];
    to.values[i - sp] = from.values[i];
  }
  // Update lengths
  to.len = from.len - sp;
  from.len = sp;
  key
}

// Splits the node (and update it) and return a new node + split key
fn split_internal(from: &mut Node, to: &mut Node) -> i32 {
  let sp = (from.len >> 1) + 1; // split point
  let key = from.keys[sp];
  // Interval nodes do not include the separator key
  for i in sp + 1..from.len {
    to.keys[i - sp - 1] = from.keys[i];
  }
  // Pointers have +1 length
  for i in sp + 1..from.len + 1 {
    to.pointers[i - sp - 1] = from.pointers[i];
  }
  // Update lengths
  to.len = from.len - sp - 1;
  from.len = sp;
  key
}

#[derive(Clone, Debug)]
struct BTree {
  nodes: Vec<Node>,
  root: usize,
}

impl BTree {
  pub fn new() -> Self {
    // Create a new btree root as leaf
    let nodes = vec![Node::new(0, true)];
    Self { nodes: nodes, root: 0 }
  }

  fn next_id(&self) -> usize {
    self.nodes.len()
  }

  pub fn insert(&mut self, key: i32, value: i32) {
    let mut curr = self.root;
    let mut stack = Vec::new();
    loop {
      // Check if the page is a leaf, if so, terminate the search
      let node = &self.nodes[curr];
      if node.is_leaf {
        break;
      }
      // Search for the pointer to the next page, i < node.len + 1
      let (_, i) = search(&node.keys[0..node.len], key);
      let next = node.pointers[i];
      // Push onto stack
      stack.push((curr, i));
      curr = next;
    }

    // Current node is a leaf node, insert the key
    let node = &mut self.nodes[curr];
    let (exists, i) = search(&node.keys[0..node.len], key);
    insert_leaf(node, exists, i, key, value);

    // Split the leaf node
    if node.len == MAX_VALUES {
      let next_id = self.next_id();
      let mut new_node = Node::new(next_id, true);
      let sp_key = split_leaf(&mut self.nodes[curr], &mut new_node);
      self.nodes.push(new_node);

      self.split(stack, sp_key, curr, next_id);
    }
  }

  fn split(&mut self, mut stack: Vec<(usize, usize)>, mut key: i32, mut left_id: usize, mut right_id: usize) {
    while let Some((id, sp)) = stack.pop() {
      insert_internal(&mut self.nodes[id], sp, key, left_id, right_id);
      // Internal node is full, split it
      if self.nodes[id].len == MAX_VALUES {
        let next_id = self.next_id();
        let mut new_node = Node::new(next_id, false);
        let sp_key = split_internal(&mut self.nodes[id], &mut new_node);
        self.nodes.push(new_node);
        key = sp_key;
        left_id = id;
        right_id = next_id;
      } else {
        // Node can fit all of the values, we do not need to check the subsequent parents
        return;
      }
    }

    // This means the root node is full and needs to be split
    let mut new_root = Node::new(self.next_id(), false);
    new_root.keys[0] = key;
    new_root.pointers[0] = left_id;
    new_root.pointers[1] = right_id;
    new_root.len = 1;

    self.root = new_root.id;
    self.nodes.push(new_root);
  }
}

impl fmt::Display for BTree {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    writeln!(f, "B-tree")?;

    let mut stack = Vec::new();
    stack.push((self.root, 0));
    while let Some((id, ind)) = stack.pop() {
      let node = &self.nodes[id];
      writeln!(f, "{}{}", " ".repeat(ind), node)?;
      if !node.is_leaf {
        for i in 0..node.len + 1 {
          stack.push((node.pointers[i], ind + 2));
        }
      }
    }
    Ok(())
  }
}

fn main() {
  let mut btree = BTree::new();
  for i in vec![13, 32, 50, 16, 39, 95, 34, 55, 41, 84, 35, 18, 53, 67, 38, 54, 71, 40, 4, 79, 64, 33, 94, 17, 59, 98, 68, 31, 22, 25, 23, 85, 48, 75, 36, 83, 26, 46, 56, 14, 80, 20, 60, 58, 78, 82, 37, 47, 88, 28, 81, 5, 8, 77, 45, 87, 42, 61, 15, 74, 51, 69, 76, 86, 93, 10, 57, 19, 99, 49, 2, 70, 43, 90, 91, 7, 72, 9, 73, 89, 30, 12, 27, 66, 44, 92, 1, 62, 52, 65, 96, 29, 6, 11, 24, 3, 21, 97, 63] {
  // for i in 1..100 {
    println!("Inserting key = {}, value = {}", i, i);
    btree.insert(i, i);
    // println!();
    // println!("{}", btree);
  }
  println!();
  println!("{}", btree);
}
