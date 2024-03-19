/*
 * TreeBarrier.java
 *
 * Created on August 3, 2005, 11:07 PM
 *
 * From "Multiprocessor Synchronization and Concurrent Data Structures",
 * by Maurice Herlihy and Nir Shavit.
 * Copyright 2006 Elsevier Inc. All rights reserved.
 */

package unam.ciencias.computoconcurrente;

import java.util.concurrent.atomic.AtomicInteger;

/**
 * Combining tree barrier.
 *
 * @author Maurice Herlihy
 */
public class TreeBarrier implements Barrier {
  int radix; // tree fan-in
  Node[] leaf; // array of leaf nodes
  int leaves; // used to build tree
  ThreadLocal<Boolean> threadSense; // thread-local sense

  public TreeBarrier(int size, int radix) {
    this.radix = radix;
    leaves = 0;
    this.leaf = new Node[size / radix];

    threadSense = ThreadLocal.withInitial(() -> true);

    int depth = 0;
    // compute tree depth
    while (size > 1) {
      depth++;
      size = size / radix;
    }
    // depth es el logaritmo base radix de size
    Node root = new Node();
    build(root, depth - 1);
  }
  // recursive tree constructor
  void build(Node parent, int depth) {
    // are we at a leaf node?
    if (depth == 0) {
      leaf[leaves++] = parent;
    } else {
      for (int i = 0; i < radix; i++) {
        Node child = new Node(parent);
        build(child, depth - 1);
      }
    }
  }
  /** Block until all threads have reached barrier. */
  public void await() {
    int me = ThreadID.get();
    Node myLeaf = leaf[me / radix];
    myLeaf.await();
  }

  private class Node {
    AtomicInteger count;
    Node parent;
    volatile boolean sense;
    // construct root node
    public Node() {
      sense = false;
      parent = null;
      count = new AtomicInteger(radix);
    }

    public Node(Node parent) {
      this();
      this.parent = parent;
    }

    public void await() {
      boolean mySense = threadSense.get();
      int position = count.getAndDecrement();
      if (position == 1) { // I'm last
        if (parent != null) { // root?
          parent.await();
        }
        count.set(radix); // reset counter
        sense = mySense;
      } else {
        while (sense != mySense) {}
      }
      threadSense.set(!mySense);
    }
  }
}
