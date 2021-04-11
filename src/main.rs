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
      write!(f, "L {} {:?} {:?}", self.id, &self.keys[0..self.len], &self.values[0..self.len])
    } else {
      write!(f, "I {} {:?} {:?}", self.id, &self.keys[0..self.len], &self.pointers[0..self.len + 1])
    }
  }
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
      // println!(" Searching: {:?}", node);
      if node.is_leaf {
        break;
      }

      // Search for the pointer to the next page
      let mut i = 0;
      while i < node.len {
        if key < node.keys[i] {
          break;
        }
        i += 1;
      }

      let next = node.pointers[i];
      // println!("Found next page: {}, i = {}", next, i);

      stack.push((curr, i));
      curr = next;
    }

    // Current node is a leaf node, insert the key
    let node = &mut self.nodes[curr];

    if node.len == 0 {
      // insert the value directly
      // println!("Updating key = {}", key);
      node.keys[0] = key;
      node.values[0] = value;
      node.len += 1;
    } else {
      let mut start = 0 as i64;
      let mut end = (node.len - 1) as i64;
      // println!("Binary search, start = {}, end = {}", start, end);

      let mut is_insert = true;
      while start <= end {
        let mid = (start + end) / 2;
        // println!("Binary search, start = {}, end = {}, mid = {}", start, end, mid);
        if key == node.keys[mid as usize] {
          // update
          is_insert = false;
          start = mid;
          break;
        } else if key < node.keys[mid as usize] {
          end = mid - 1;
        } else {
          start = mid + 1;
        }
      }

      // println!("start = {}, end = {}", start, end);
      if is_insert {
        // Clear the slot to insert
        for i in (start as usize + 1..node.len + 1).rev() {
          // println!("  Shifting element {}", i);
          node.keys[i] = node.keys[i - 1];
          node.values[i] = node.values[i - 1];
        }
        // We are going to insert a new key
        node.len += 1;
      }
      node.keys[start as usize] = key;
      node.values[start as usize] = value;
    }

    // Split the node
    let new_id = self.next_id();
    let node = &mut self.nodes[curr];
    let new_node_key = if node.len == MAX_VALUES {
      let mut new_node = Node::new(new_id, true);

      // We need to split the node
      let si = node.len / 2 + 1;
      // println!("Split: si = {}", si);

      // Copy half of the elements into the new node
      for i in si..node.len {
        new_node.keys[i - si] = node.keys[i];
        new_node.values[i - si] = node.values[i];
      }
      new_node.len = node.len - si;
      node.len = si;

      Some((new_node, node.keys[si]))
    } else {
      None
    };

    if let Some((node, sep_key)) = new_node_key {
      self.nodes.push(node);
      self.split(stack, sep_key, curr, new_id);
    }
  }

  fn split(&mut self, mut stack: Vec<(usize, usize)>, mut key: i32, mut left_id: usize, mut right_id: usize) {
    while let Some((pid, sep)) = stack.pop() {
      let parent = &mut self.nodes[pid];
      println!("  parent = {}, sep = {}, key = {}", parent, sep, key);

      // Update the current pointer to the new right node
      parent.pointers[sep] = right_id;

      // Shift elements to the right
      for i in (sep + 1..parent.len + 1).rev() {
        parent.keys[i] = parent.keys[i - 1];
      }
      for i in (sep + 1..parent.len + 2).rev() {
        parent.pointers[i] = parent.pointers[i - 1];
      }

      parent.keys[sep] = key;
      parent.pointers[sep] = left_id;

      parent.len += 1;

      println!("  parent (upd) = {}", parent);

      // TODO: move into a separate function
      let new_id = self.next_id();
      let node = &mut self.nodes[pid];
      let new_node_key: Option<(Node, i32)> = if node.len == MAX_VALUES {
        let mut new_node = Node::new(new_id, false);
        let si = node.len / 2 + 1;

        for i in si + 1..node.len {
          new_node.keys[i - si - 1] = node.keys[i];
          new_node.len += 1;
        }
        for i in si + 1..node.len + 1 {
          new_node.pointers[i - si - 1] = node.pointers[i];
        }

        node.len = si;

        println!("  new node (upd) = {}", new_node);

        Some((new_node, node.keys[si]))
      } else {
        None
      };

      if let Some((node, sep_key)) = new_node_key {
        key = sep_key;
        left_id = pid;
        right_id = node.id;
        self.nodes.push(node);
      } else {
        return;
      }
    }

    println!("Split root node");

    // New parent
    let mut parent = Node::new(self.next_id(), false);
    println!("Promote key = {}", key);

    parent.keys[0] = key;
    parent.pointers[0] = left_id;
    parent.pointers[1] = right_id;
    parent.len = 1;

    self.root = parent.id;
    self.nodes.push(parent);
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
  // for i in vec![13, 32, 50, 16, 39, 95, 34, 55, 41, 84, 35, 18, 53, 67, 38, 54, 71, 40, 4, 79, 64, 33, 94, 17, 59, 98, 68, 31, 22, 25, 23, 85, 48, 75, 36, 83, 26, 46, 56, 14, 80, 20, 60, 58, 78, 82, 37, 47, 88, 28, 81, 5, 8, 77, 45, 87, 42, 61, 15, 74, 51, 69, 76, 86, 93, 10, 57, 19, 99, 49, 2, 70, 43, 90, 91, 7, 72, 9, 73, 89, 30, 12, 27, 66, 44, 92, 1, 62, 52, 65, 96, 29, 6, 11, 24, 3, 21, 97, 63] {
  for i in 0..100 {
    println!("Inserting key = {}, value = {}", i, i);
    btree.insert(i, i);
    // println!();
    // println!("{}", btree);
  }

  println!();
  println!("{}", btree);
}
