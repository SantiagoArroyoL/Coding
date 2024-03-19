package unam.ciencias.computoconcurrente;

import java.util.concurrent.atomic.AtomicReference;

public class MCSLock extends Lock {
  public static class QNode {
    volatile boolean locked;
    volatile QNode next;

    QNode() {
      locked = false;
      next = null;
    }
  }

  private final AtomicReference<QNode> tail;
  private final ThreadLocal<QNode> myNode;

  public MCSLock() {
    tail = new AtomicReference<>(null);
    myNode = ThreadLocal.withInitial(QNode::new);
  }

  @Override
  public void lock() {
    QNode qnode = myNode.get();
    QNode pred = tail.getAndSet(qnode);
    if (pred != null) {
      qnode.locked = true;
      pred.next = qnode;
      while (qnode.locked) {}
    }
  }

  @Override
  public void unlock() {
    QNode qnode = myNode.get();
    if (qnode.next == null) {
      if (tail.compareAndSet(qnode, null)) return;
      while (qnode.next == null) {}
    }
    qnode.next.locked = false;
    qnode.next = null;
  }
}
