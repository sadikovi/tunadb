use std::fmt;

const MIN_KEYS: usize = 2;
const MAX_KEYS: usize = 5;

#[derive(Clone, Debug)]
struct Node {
  id: usize,
  is_leaf: bool,
  keys: [i32; MAX_KEYS],
  values: [i32; MAX_KEYS],
  pointers: [usize; MAX_KEYS + 1],
  len: usize, // number of keys in the node
}

impl Node {
  // Creates a new node.
  pub fn new(id: usize, is_leaf: bool) -> Self {
    Self {
      id: id,
      is_leaf: is_leaf,
      keys: [0; MAX_KEYS],
      values: [0; MAX_KEYS],
      pointers: [0; MAX_KEYS + 1],
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
    Self { nodes: vec![Node::new(0, true)], root: 0 }
  }

  fn next_id(&self) -> usize {
    self.nodes.len()
  }

  // Deletes the key and returns the value for that key
  pub fn find(&self, key: i32) -> Option<i32> {
    let mut curr = self.root;
    loop {
      // Check if the page is a leaf, if so, terminate the search
      let node = &self.nodes[curr];
      if node.is_leaf {
        break;
      }
      // Search for the pointer to the next page, i < node.len + 1
      let (exists, i) = search(&node.keys[0..node.len], key);
      let next = if exists { node.pointers[i + 1] } else { node.pointers[i] };
      curr = next;
    }

    // Current node is a leaf node, delete the key
    let node = &self.nodes[curr];
    let (exists, i) = search(&node.keys[0..node.len], key);
    if exists {
      Some(node.values[i])
    } else {
      None
    }
  }

  pub fn insert(&mut self, key: i32, value: i32) {
    // TODO: split the node before inserting otherwise there could be no room to insert
    let mut curr = self.root;
    let mut stack = Vec::new();
    loop {
      // Check if the page is a leaf, if so, terminate the search
      let node = &self.nodes[curr];
      if node.is_leaf {
        break;
      }
      // Search for the pointer to the next page, i < node.len + 1
      let (exists, i) = search(&node.keys[0..node.len], key);
      let next = if exists { node.pointers[i + 1] } else { node.pointers[i] };
      // Push onto stack
      stack.push((curr, i));
      curr = next;
    }

    // Current node is a leaf node, insert the key
    let node = &mut self.nodes[curr];
    let (exists, i) = search(&node.keys[0..node.len], key);
    insert_leaf(node, exists, i, key, value);

    // Split the leaf node
    if node.len == MAX_KEYS {
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
      if self.nodes[id].len == MAX_KEYS {
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

  // Deletes the key and returns the value for that key
  pub fn delete(&mut self, key: i32) {
    let mut curr = self.root;
    let mut stack = Vec::new();
    loop {
      // Check if the page is a leaf, if so, terminate the search
      let node = &self.nodes[curr];
      if node.is_leaf {
        break;
      }
      // Search for the pointer to the next page, i < node.len + 1
      let (exists, i) = search(&node.keys[0..node.len], key);
      let ptr = if exists { i + 1 } else { i };
      let next = node.pointers[ptr];
      // Push onto stack
      stack.push((curr, ptr));
      curr = next;
    }

    // Current node is a leaf node, delete the key
    let node = &self.nodes[curr];
    let (exists, i) = search(&node.keys[0..node.len], key);
    if exists {
      let mut node = &mut self.nodes[curr];
      for k in i..node.len - 1 {
        node.keys[k] = node.keys[k + 1];
        node.values[k] = node.values[k + 1];
      }
      node.len -= 1; // deleted a key
      println!("  deleted key: {} in leaf: {}", key, node);
    }

    let node = &self.nodes[curr];
    if exists {
      if i == 0 {
        if node.len == 0 {
          // Node is empty, remove the key from the parent
          println!("  node is empty, cannot fix parent links");
        } else {
          // Fix parent links because we are deleting the smallest key
          let next_smallest_key = node.keys[0];
          println!("  fix parent links with the next key: {}", next_smallest_key);
          for k in (0..stack.len()).rev() {
            let (parent, pos) = stack[k];
            let mut parent = &mut self.nodes[parent];
            if parent.keys[pos] == key {
              parent.keys[pos] = next_smallest_key;
            }
          }
        }
      }

      self.repair_after_delete(curr, stack);
    }
  }

  fn repair_after_delete(&mut self, mut curr: usize, mut stack: Vec<(usize, usize)>) {
    println!("  repair after delete, stack: {:?}", stack);
    while let Some((parent_index, ptr)) = stack.pop() {
      let parent = &self.nodes[parent_index];
      let node = &self.nodes[parent.pointers[ptr]];
      curr = node.id;

      println!("    reparing node: {}, parent: {}, ptr: {}", node, parent, ptr);

      if node.len >= MIN_KEYS {
        return;
      }

      println!("    parent: {}, ptr: {}, node.len: {}", parent, ptr, node.len);
      if ptr > 0 && self.nodes[parent.pointers[ptr - 1]].len > MIN_KEYS {
        println!("    steal from the left sibling");
        self.steal_from_left(curr, parent_index, ptr);
        return;
      } else if ptr < parent.len && self.nodes[parent.pointers[ptr + 1]].len > MIN_KEYS {
        println!("    steal from the right sibling");
        self.steal_from_right(curr, parent_index, ptr);
        return;
      } else if ptr == 0 {
        println!("    merge with the right sibling");
        self.merge_right(parent_index, ptr);
      } else {
        println!("    merge with the left sibling");
        self.merge_right(parent_index, ptr - 1);
      }
    }

    // At this point we have reached the parent node

    println!("    reached parent: {} with curr: {}", self.root, curr);
    let root = &mut self.nodes[self.root];
    if root.len == 0 {
      self.root = root.pointers[0];
    }
  }

  fn steal_from_left(&mut self, curr: usize, parent_index: usize, ptr: usize) {
    let mut node = self.nodes[curr].clone();
    let mut parent = self.nodes[parent_index].clone();
    let left_id = parent.pointers[ptr - 1];
    let mut left = self.nodes[left_id].clone();

    assert!(node.is_leaf == left.is_leaf);

    println!("      before; left: {}, node: {}, parent: {}", left, node, parent);

    node.len += 1;

    if node.is_leaf {
      // Update keys and values
      for i in (0..node.len - 1).rev() {
        node.keys[i + 1] = node.keys[i];
        node.values[i + 1] = node.values[i];
      }
      node.keys[0] = left.keys[left.len - 1];
      node.values[0] = left.values[left.len - 1];
      parent.keys[ptr - 1] = left.keys[left.len - 1];
    } else {
      // Update keys
      for i in (0..node.len - 1).rev() {
        node.keys[i + 1] = node.keys[i];
      }
      node.keys[0] = parent.keys[ptr - 1];
      parent.keys[ptr - 1] = left.keys[left.len - 1];

      // Update pointers
      for i in (0..node.len).rev() {
        node.pointers[i + 1] = node.pointers[i];
      }
      node.pointers[0] = left.pointers[left.len];
    }

    left.len -= 1;

    println!("      after; left: {}, node: {}, parent: {}", left, node, parent);

    self.nodes[curr] = node;
    self.nodes[parent_index] = parent;
    self.nodes[left_id] = left;
  }

  fn steal_from_right(&mut self, curr: usize, parent_index: usize, ptr: usize) {
    let mut node = self.nodes[curr].clone();
    let mut parent = self.nodes[parent_index].clone();
    let right_id = parent.pointers[ptr + 1];
    let mut right = self.nodes[right_id].clone();

    assert!(node.is_leaf == right.is_leaf);

    println!("      before; node: {}, right: {}, parent: {}", node, right, parent);

    node.len += 1;

    if node.is_leaf {
      node.keys[node.len - 1] = right.keys[0];
      node.values[node.len - 1] = right.values[0];
      parent.keys[ptr] = right.keys[1];

      for i in 0..right.len - 1 {
        right.keys[i] = right.keys[i + 1];
        right.values[i] = right.values[i + 1];
      }
    } else {
      node.keys[node.len - 1] = parent.keys[ptr];
      parent.keys[ptr] = right.keys[0];
      node.pointers[node.len] = right.pointers[0];

      for i in 0..right.len - 1 {
        right.keys[i] = right.keys[i + 1];
      }
      for i in 0..right.len {
        right.pointers[i] = right.pointers[i + 1];
      }
    }

    right.len -= 1;

    println!("      after; node: {}, right: {}, parent: {}", node, right, parent);

    self.nodes[curr] = node;
    self.nodes[parent_index] = parent;
    self.nodes[right_id] = right;
  }

  fn merge_right(&mut self, parent_index: usize, ptr: usize) {
    let mut parent = self.nodes[parent_index].clone();
    let curr = parent.pointers[ptr];
    let mut node = self.nodes[curr].clone();
    let right_id = parent.pointers[ptr + 1];
    let right = &self.nodes[right_id];

    println!("      want to merge node: {}, right: {}, parent: {}", node, right, parent);
    assert!(node.is_leaf == right.is_leaf);

    let is_leaf = node.is_leaf;

    if node.is_leaf {
      for i in 0..right.len {
        node.keys[node.len + i] = right.keys[i];
        node.values[node.len + i] = right.values[i];
      }
      node.len += right.len;
    } else {
      node.keys[node.len] = parent.keys[ptr];
      for i in 0..right.len {
        node.keys[node.len + 1 + i] = right.keys[i];
      }
      for i in 0..right.len + 1 {
        node.pointers[node.len + 1 + i] = right.pointers[i];
      }
      node.len += right.len + 1;
    }

    for i in ptr + 1..parent.len {
      parent.keys[i - 1] = parent.keys[i];
      parent.pointers[i] = parent.pointers[i + 1];
    }
    parent.len -= 1;

    println!("      merged node: {}, right: {}, parent: {}", node, right, parent);

    self.nodes[curr] = node;
    self.nodes[parent_index] = parent;
    self.nodes[right_id] = Node::new(99999999, is_leaf);
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

// Testing functions

fn test_find(btree: &BTree, keys: &[i32], assert_match: bool) {
  for &key in keys {
    if assert_match {
      assert_eq!(btree.find(key), Some(key), "Failed to find {}", key);
    } else {
      assert_eq!(btree.find(key), None, "Failed, the key {} existed", key);
    }
  }
  println!("Search: OK");
}

fn test_insert(btree: &mut BTree, keys: &[i32]) {
  for i in 0..keys.len() {
    let key = keys[i];
    println!("Inserting key = {}, value = {}", key, key);
    btree.insert(key, key);
    // Perform search on a subset
    test_find(btree, &keys[0..i + 1], true);
    test_find(btree, &keys[i + 1..], false);
  }
}

fn test_delete(btree: &mut BTree, keys: &[i32]) {
  for i in 0..keys.len() {
    let key = keys[i];
    println!("Deleting key = {}", key);
    btree.delete(key);
    // Perform search on a subset
    test_find(btree, &keys[0..i + 1], false);
    test_find(btree, &keys[i + 1..], true);

    println!("{}", btree);
  }
}

fn main() {
  let arr = vec![13, 32, 50, 16, 39, 95, 34, 55, 41, 84, 35, 18, 53, 67, 38, 54, 71, 40, 4, 79, 64, 33, 94, 17, 59, 98, 68, 31, 22, 25, 23, 85, 48, 75, 36, 83, 26, 46, 56, 14, 80, 20, 60, 58, 78, 82, 37, 47, 88, 28, 81, 5, 8, 77, 45, 87, 42, 61, 15, 74, 51, 69, 76, 86, 93, 10, 57, 19, 99, 49, 2, 70, 43, 90, 91, 7, 72, 9, 73, 89, 30, 12, 27, 66, 44, 92, 1, 62, 52, 65, 96, 29, 6, 11, 24, 3, 21, 97, 63];
  // let arr = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99];
  // let arr = vec![99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0];
  // let arr = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
  // let arr = vec![1, 100, 2, 10, 3, 4, 5, 6, 7, 8];
  // let arr = vec![1, 2, 3, 4, 5];

  let mut btree = BTree::new();

  // Check insert
  test_insert(&mut btree, &arr);
  println!();
  println!("{}", btree);

  // Check positive search
  test_find(&btree, &arr, true);

  // Check delete
  test_delete(&mut btree, &arr);
  println!();
  println!("{}", btree);

  // Check negative search
  test_find(&btree, &arr, false);

  assert_eq!(format!("{}", btree), format!("{}", BTree::new()))
}
