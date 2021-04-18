use std::fmt;
use rand::prelude::*;

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
  next: Option<usize>, // pointer to the next leaf node, only set in a leaf
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
      next: None,
    }
  }
}

impl fmt::Display for Node {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if self.is_leaf {
      write!(f, "L ({}) {:?} {:?} *{:?}", self.id, &self.keys[0..self.len], &self.values[0..self.len], self.next)
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

  // Returns an iterator with all of the leaves
  // Used for testing only
  pub fn range(&self) -> BTreeIter {
    // Find the leftmost leaf node to start range query
    let mut curr = self.root;
    let mut node = &self.nodes[curr];
    while !node.is_leaf {
      curr = node.pointers[0];
      node = &self.nodes[curr];
    }
    BTreeIter::new(&self, Some(curr))
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
      // Update next pointers
      new_node.next = self.nodes[curr].next;
      self.nodes[curr].next = Some(next_id);
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
      // println!("  deleted key: {} in leaf: {}", key, node);
    }

    let node = &self.nodes[curr];
    if exists {
      if i == 0 {
        if node.len == 0 {
          // Node is empty, remove the key from the parent
          // println!("  node is empty, cannot fix parent links");
        } else {
          // Fix parent links because we are deleting the smallest key
          let next_smallest_key = node.keys[0];
          // println!("  fix parent links with the next key: {}", next_smallest_key);
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
    // println!("  repair after delete, stack: {:?}", stack);
    while let Some((parent_index, ptr)) = stack.pop() {
      let parent = &self.nodes[parent_index];
      let node = &self.nodes[parent.pointers[ptr]];
      curr = node.id;

      // println!("    reparing node: {}, parent: {}, ptr: {}", node, parent, ptr);

      if node.len >= MIN_KEYS {
        return;
      }

      // println!("    parent: {}, ptr: {}, node.len: {}", parent, ptr, node.len);
      if ptr > 0 && self.nodes[parent.pointers[ptr - 1]].len > MIN_KEYS {
        // println!("    steal from the left sibling");
        self.steal_from_left(curr, parent_index, ptr);
        return;
      } else if ptr < parent.len && self.nodes[parent.pointers[ptr + 1]].len > MIN_KEYS {
        // println!("    steal from the right sibling");
        self.steal_from_right(curr, parent_index, ptr);
        return;
      } else if ptr == 0 {
        // println!("    merge with the right sibling");
        self.merge_right(parent_index, ptr);
      } else {
        // println!("    merge with the left sibling");
        self.merge_right(parent_index, ptr - 1);
      }
    }

    // At this point we have reached the parent node

    // println!("    reached parent: {} with curr: {}", self.root, curr);
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

    // println!("      before; left: {}, node: {}, parent: {}", left, node, parent);

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

    // println!("      after; left: {}, node: {}, parent: {}", left, node, parent);

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

    // println!("      before; node: {}, right: {}, parent: {}", node, right, parent);

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

    // println!("      after; node: {}, right: {}, parent: {}", node, right, parent);

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

    // println!("      want to merge node: {}, right: {}, parent: {}", node, right, parent);
    assert!(node.is_leaf == right.is_leaf);

    let is_leaf = node.is_leaf;

    if node.is_leaf {
      for i in 0..right.len {
        node.keys[node.len + i] = right.keys[i];
        node.values[node.len + i] = right.values[i];
      }
      node.len += right.len;

      // Update next pointers
      node.next = right.next;
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

    // println!("      merged node: {}, right: {}, parent: {}", node, right, parent);

    self.nodes[curr] = node;
    self.nodes[parent_index] = parent;
    self.nodes[right_id] = Node::new(99999999, is_leaf); // a test value to detect errors
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

// Simple iterator for leaf nodes.
// Used for testing to ensure all operations are performed correctly.
struct BTreeIter<'a> {
  start: Option<usize>,
  pos: usize,
  btree: &'a BTree,
}

impl<'a> BTreeIter<'a> {
  pub fn new(btree: &'a BTree, start: Option<usize>) -> Self {
    Self { start: start, pos: 0, btree: btree }
  }
}

impl<'a> Iterator for BTreeIter<'a> {
  type Item = i32;
  fn next(&mut self) -> Option<Self::Item> {
    let mut cnt = 0;
    loop {
      if cnt > 1 {
        println!("WARN: It took {} iterations to find a value", cnt);
      }
      cnt += 1;

      if let Some(id) = self.start {
        let node = &self.btree.nodes[id];
        if self.pos >= node.len {
          self.pos = 0;
          self.start = node.next;
        } else {
          let key = node.keys[self.pos];
          self.pos += 1;
          return Some(key);
        }
      } else {
        return None;
      }
    }
  }
}

// Testing functions

fn test_find(btree: &BTree, keys: &[i32], assert_match: bool) -> Result<(), String> {
  for &key in keys {
    if assert_match {
      if btree.find(key) != Some(key) {
        return Err(format!("Failed to find {}", key));
      }
    } else {
      if btree.find(key) != None {
        return Err(format!("Failed, the key {} existed", key));
      }
    }
  }
  Ok(())
}

fn test_range(btree: &BTree, keys: &[i32]) -> Result<(), String> {
  let mut expected = keys.to_vec();
  expected.sort();
  let leaf_values: Vec<i32> = btree.range().collect();
  if expected != leaf_values {
    println!("{:?} != {:?}", expected, leaf_values);
    Err(format!("Range query did not match the sorted input"))
  } else {
    Ok(())
  }
}

fn test_insert(btree: &mut BTree, keys: &[i32]) -> Result<(), String> {
  for i in 0..keys.len() {
    let key = keys[i];
    // println!("Inserting key = {}, value = {}", key, key);
    btree.insert(key, key);
    // Perform search on a subset
    test_find(btree, &keys[0..i + 1], true)?;
    test_find(btree, &keys[i + 1..], false)?;
    // Check range
    test_range(btree, &keys[0..i + 1])?;
  }
  Ok(())
}

fn test_delete(btree: &mut BTree, keys: &[i32]) -> Result<(), String> {
  for i in 0..keys.len() {
    let key = keys[i];
    // println!("Deleting key = {}", key);
    btree.delete(key);
    // Perform search on a subset
    test_find(btree, &keys[0..i + 1], false)?;
    test_find(btree, &keys[i + 1..], true)?;
    // Check range
    test_range(btree, &keys[i + 1..])?;
  }
  Ok(())
}

fn test_insert_find_delete(keys: &mut [i32]) -> Result<(), String> {
  let mut rng = thread_rng();

  let mut btree = BTree::new();

  // Check insert
  keys.shuffle(&mut rng);

  test_insert(&mut btree, &keys)?;
  // println!();
  // println!("{}", btree);

  // Check positive search
  test_find(&btree, &keys, true)?;
  // Check range
  test_range(&btree, &keys)?;

  // Check delete
  keys.shuffle(&mut rng);

  test_delete(&mut btree, &keys)?;
  // println!();
  // println!("{}", btree);

  // Check negative search
  test_find(&btree, &keys, false)?;
  // Check empty range
  test_range(&btree, &[])?;

  if format!("{}", btree) != format!("{}", BTree::new()) {
    Err(format!("BTree was not empty after delete: {}", btree))
  } else {
    Ok(())
  }
}

fn main() {
  let mut arr = vec![0i32; 1000];
  for i in 0..arr.len() {
    arr[i] = i as i32;
  }

  for i in 0..10 {
    println!("Iteration {}", i);
    let res = test_insert_find_delete(&mut arr);
    if res.is_err() {
      println!("ERROR!!!");
      println!("Keys: {:?}", arr);
    }
    res.unwrap();
  }
}
