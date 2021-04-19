////////////////////////////////////////////////////////////
// B+ tree find
////////////////////////////////////////////////////////////

BPlusTree.prototype.findInTree = function (tree, val) {
  if (tree == null) {
    return Result("Element " + val + " is not in the tree");
  }

  var i;
  // Find i where keys[i] >= val or i == numKeys
  for (i = 0; i < tree.numKeys && tree.keys[i] < val; i++);

  if (i == tree.numKeys) {
    if (!tree.isLeaf) {
      this.findInTree(tree.children[tree.numKeys], val);
    } else {
      return Result("Element " + val + " is not in the tree");
    }
  } else if (tree.keys[i] > val) {
    if (!tree.isLeaf) {
      this.findInTree(tree.children[i], val);
    } else {
      return Result("Element " + val + " is not in the tree");
    }
  } else { // tree.keys[i] == val
    if (!tree.isLeaf) {
      this.findInTree(tree.children[i + 1], val);
    } else {
      // Found the key
      return Result("Element " + val + " found");
    }
  }
};

////////////////////////////////////////////////////////////
// B+ tree insert
////////////////////////////////////////////////////////////

BPlusTree.prototype.insert = function (tree, insertValue) {
  if (tree.isLeaf) {
    tree.numKeys++;
    // Copy all keys larger than "insertValue" to the right to free space
    var insertIndex = tree.numKeys - 1;
    while (insertIndex > 0 && tree.keys[insertIndex - 1] > insertValue) {
      tree.keys[insertIndex] = tree.keys[insertIndex - 1];
      insertIndex--;
    }
    // Insert the value
    tree.keys[insertIndex] = insertValue;
    this.insertRepair(tree);
  } else {
    var findIndex = 0;
    while (findIndex < tree.numKeys && tree.keys[findIndex] < insertValue) {
      findIndex++;
    }
    // FIXME:
    // I think if the tree.keys[findIndex] == insertValue, you need to go to children[findIndex + 1]
    // based on the condition that p[i + 1] has all of the keys including k[i]
    this.insert(tree.children[findIndex], insertValue);
  }
};

BPlusTree.prototype.insertRepair = function (tree) {
  // enough free space, max_keys = degree - 1
  if (tree.numKeys <= this.max_keys) return;

  if (tree.parent == null) { // "tree" is the root node
    this.treeRoot = this.split(tree);
  } else {
    var newNode = this.split(tree);
    this.insertRepair(newNode);
  }
};

BPlusTree.prototype.split = function (tree) {
  var rightNode = new BTreeNode(this.nextIndex++); // create a new node
  var risingNode = tree.keys[this.split_index]; // TODO: what is split_index? I think it is "key to promote"

  var i;
  var parentIndex;
  if (tree.parent != null) {
    // Find pointer index of the "tree" node in the parent
    var currentParent = tree.parent;
    for (parentIndex = 0; parentIndex < currentParent.numKeys + 1 && currentParent.children[parentIndex] != tree; parentIndex++);
    if (parentIndex == currentParent.numKeys + 1) {
      throw new Error("Couldn't find which child we were!");
    }

    // Free space for the key to promote
    for (i = currentParent.numKeys; i > parentIndex; i--) {
      currentParent.children[i + 1] = currentParent.children[i];
      currentParent.keys[i] = currentParent.keys[i - 1];
    }
    currentParent.numKeys++;
    // Insert the separate key that we promoted
    currentParent.keys[parentIndex] = risingNode;
    currentParent.children[parentIndex + 1] = rightNode;
    rightNode.parent = currentParent;
  }

  var rightSplit;
  if (tree.isLeaf) { // Updating prev/next pointers for a leaf node
    rightSplit = this.split_index;
    rightNode.next = tree.next;
    tree.next = rightNode;
  } else {
    rightSplit = this.split_index + 1; // it seems to be a pointer index, not key
  }

  // Set numKeys for the rightNode
  rightNode.numKeys = tree.numKeys - rightSplit;

  // Copy half of the child pointers into rightNode
  // Because we maintain parent pointers, update those as we go
  for (var i = rightSplit; i < tree.numKeys + 1; i++) {
    rightNode.children[i - rightSplit] = tree.children[i];
    if (tree.children[i] != null) { // updating parent pointers
      rightNode.isLeaf = false; // weird, rightNode.isLeaf could have been when creating it
      if (tree.children[i] != null) {
        tree.children[i].parent = rightNode;
      }
      tree.children[i] = null;
    }
  }
  // Copy the keys into rightNode
  for (i = rightSplit; i < tree.numKeys; i++) {
    rightNode.keys[i - rightSplit] = tree.keys[i];
  }
  // ... and update numKeys for the current node
  var leftNode = tree;
  leftNode.numKeys = this.split_index;

  if (tree.parent != null) {
    return tree.parent;
  } else { // tree.parent == null, we are splitting the root node
    this.treeRoot = new BTreeNode(this.nextIndex++);
    this.treeRoot.isLeaf = false;
    this.treeRoot.keys[0] = risingNode; // key to promote
    this.treeRoot.children[0] = leftNode; // previous root node with half of the elements in it
    this.treeRoot.children[1] = rightNode;
    leftNode.parent = this.treeRoot;
    rightNode.parent = this.treeRoot;
    return this.treeRoot;
  }
};

////////////////////////////////////////////////////////////
// B+ tree delete
////////////////////////////////////////////////////////////

BPlusTree.prototype.doDelete = function (tree, val) {
  if (tree == null) return;

  // Find a leaf that contains "val"
  var i;
  for (i = 0; i < tree.numKeys && tree.keys[i] < val; i++);
  if (!tree.isLeaf && i == tree.numKeys) {
    // Move to the rightmost pointer and delete "val" there
    this.doDelete(tree.children[tree.numKeys], val);
  } else if (!tree.isLeaf && tree.keys[i] == val) {
    // Move to the pointer i + 1 because all keys are >= val in p[i + 1]
    this.doDelete(tree.children[i + 1], val);
  } else if (!tree.isLeaf) { // tree.keys[i] > val
    this.doDelete(tree.children[i], val);
  } else if (tree.isLeaf && tree.keys[i] == val) {
    // Delete the key by copying elements from right to left
    for (var j = i; j < tree.numKeys - 1; j++) {
      tree.keys[j] = tree.keys[j + 1];
    }
    tree.numKeys--;

    // Bit of a hack -- if we remove the smallest element in a leaf, then find the *next* smallest element
    //  (somewhat tricky if the leaf is now empty!), go up our parent stack, and fix index keys
    if (i == 0 && tree.parent != null) {
      var nextSmallest = "";
      var parentNode = tree.parent;
      var parentIndex;
      for (parentIndex = 0; parentNode.children[parentIndex] != tree; parentIndex++);
      if (tree.numKeys == 0) {
        if (parentIndex == parentNode.numKeys) {
          nextSmallest == "";
        } else {
          nextSmallest = parentNode.children[parentIndex + 1].keys[0];
        }
      } else {
        nextSmallest = tree.keys[0];
      }
      while (parentNode != null) {
        if (parentIndex > 0 && parentNode.keys[parentIndex - 1] == val) {
          parentNode.keys[parentIndex - 1] = nextSmallest;
        }
        var grandParent = parentNode.parent;
        for (parentIndex = 0; grandParent != null && grandParent.children[parentIndex] != parentNode; parentIndex++);
        parentNode = grandParent;
      }
    }
    this.repairAfterDelete(tree);
  } else {
    // Key is not in the tree, do nothing
  }
};

BPlusTree.prototype.repairAfterDelete = function (tree) {
  if (tree.numKeys >= this.min_keys) return; // we have enough keys in the node

  if (tree.parent == null) {
    // I don't qute understand this part but it seems the root can have 0 keys with one child
    // pointer left that points to a valid non-empty node.
    if (tree.numKeys == 0) {
      this.treeRoot = tree.children[0];
      if (this.treeRoot != null) this.treeRoot.parent = null;
    }
  } else {
    var parentNode = tree.parent;
    for (var parentIndex = 0; parentNode.children[parentIndex] != tree; parentIndex++);

    if (parentIndex > 0 && parentNode.children[parentIndex - 1].numKeys > this.min_keys) {
      this.stealFromLeft(tree, parentIndex);
    } else if (parentIndex < parentNode.numKeys && parentNode.children[parentIndex + 1].numKeys > this.min_keys) {
      this.stealFromRight(tree, parentIndex);
    } else if (parentIndex == 0) {
      // Merge with right sibling
      var nextNode = this.mergeRight(tree);
      this.repairAfterDelete(nextNode.parent);
    } else {
      // Merge with left sibling
      nextNode = this.mergeRight(parentNode.children[parentIndex - 1]);
      this.repairAfterDelete(nextNode.parent);
    }
  }
};

// Steal from left sibling
BPlusTree.prototype.stealFromLeft = function (tree, parentIndex) { // parentIndex is a pointer index in the parent for the tree
  var parentNode = tree.parent;
  var leftSib = parentNode.children[parentIndex - 1];

  // Make space for one key from the left sibling by moving keys to the right
  tree.numKeys++;
  for (i = tree.numKeys - 1; i > 0; i--) {
    tree.keys[i] = tree.keys[i - 1];
  }

  if (tree.isLeaf) {
    tree.keys[0] = leftSib.keys[leftSib.numKeys - 1];
    parentNode.keys[parentIndex - 1] = leftSib.keys[leftSib.numKeys - 1]; // key[parentIndex - 1] == pointer[parentIndex]
  } else {
    tree.keys[0] = parentNode.keys[parentIndex - 1];
    parentNode.keys[parentIndex - 1] = leftSib.keys[leftSib.numKeys - 1];
  }

  if (!tree.isLeaf) {
    for (var i = tree.numKeys; i > 0; i--) {
      tree.children[i] = tree.children[i - 1];
    }
    tree.children[0] = leftSib.children[leftSib.numKeys];
    leftSib.children[leftSib.numKeys] = null;
    tree.children[0].parent = tree;
  }

  leftSib.numKeys--;

  return tree;
};

// Steal from right sibling
BPlusTree.prototype.stealFromRight = function (tree, parentIndex) {
  var parentNode = tree.parent;
  var rightSib = parentNode.children[parentIndex + 1];

  tree.numKeys++; // the new key will be added to the end

  if (tree.isLeaf) {
    tree.keys[tree.numKeys - 1] = rightSib.keys[0];
    parentNode.keys[parentIndex] = rightSib.keys[1];
  } else {
    tree.keys[tree.numKeys - 1] = parentNode.keys[parentIndex];
    parentNode.keys[parentIndex] = rightSib.keys[0];
  }

  if (!tree.isLeaf) {
    tree.children[tree.numKeys] = rightSib.children[0];
    tree.children[tree.numKeys].parent = tree;
    // TODO::CHECKME! Shift the pointers to the left in the right sibling
    for (var i = 1; i < rightSib.numKeys + 1; i++) {
      rightSib.children[i - 1] = rightSib.children[i];
    }
  }
  // Shift keys to the left in the right sibling
  for (i = 1; i < rightSib.numKeys; i++) {
    rightSib.keys[i - 1] = rightSib.keys[i];
  }
  rightSib.numKeys--;

  return tree;
};

// Merge "tree" with its right sibling: keys/pointers from the right sibling are copied into "tree"
BPlusTree.prototype.mergeRight = function (tree) {
  var parentNode = tree.parent;
  var parentIndex = 0; // pointer index that points to the "tree", key would be parentIndex - 1
  for (parentIndex = 0; parentNode.children[parentIndex] != tree; parentIndex++);

  var rightSib = parentNode.children[parentIndex + 1];

  // This is done to accommodate a pointer to the rightmost node in "tree"
  // It is a key for the rightmost pointer in "tree", i.e. if val < k[i] => p[i]
  if (!tree.isLeaf) {
    // at this point there are numKeys + 1 keys and numKeys + 1 pointers
    tree.keys[tree.numKeys] = parentNode.keys[parentIndex];
  }

  // Copy keys from the right sibling into "tree"
  for (var i = 0; i < rightSib.numKeys; i++) {
    var insertIndex = tree.numKeys + 1 + i;
    if (tree.isLeaf) {
      insertIndex -= 1; // in leaf nodes there are no pointers, keys can be copied back to back
    }
    tree.keys[insertIndex] = rightSib.keys[i];
  }

  if (!tree.isLeaf) {
    for (i = 0; i <= rightSib.numKeys; i++) {
      tree.children[tree.numKeys + 1 + i] = rightSib.children[i];
      tree.children[tree.numKeys + 1 + i].parent = tree;
    }
    tree.numKeys = tree.numKeys + rightSib.numKeys + 1;
  } else {
    tree.numKeys = tree.numKeys + rightSib.numKeys; // simply combine the keys
    tree.next = rightSib.next;
  }

  // parentIndex + 1 is invalid and points the right sibling
  for (i = parentIndex + 1; i < parentNode.numKeys; i++) {
    parentNode.children[i] = parentNode.children[i + 1];
    parentNode.keys[i - 1] = parentNode.keys[i];
  }

  parentNode.numKeys--;

  return tree;
};

function BTreeNode(id) {
  this.id = id;
  this.isLeaf = true;
  this.parent = null;
  this.numKeys = 1;
  this.keys = [];
  this.children = [];
  this.next = null;
}
