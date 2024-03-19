package unam.ciencias.computoconcurrente;

import java.util.concurrent.atomic.AtomicReference;

public class MCSLock extends Lock {
  public static class QNode {
    volatile boolean locked;
    volatile QNode next;

    QNode() {
      locked = false; // free
      next = null;
    }
  }

  private final AtomicReference<QNode> tail;
  private final ThreadLocal<QNode> myNode;

  public MCSLock() {
    tail = new AtomicReference<>(null); // vacía
    myNode = ThreadLocal.withInitial(QNode::new); // por omisión marcado como free
  }

  @Override
  public void lock() {
    QNode qnode = myNode.get();
    QNode pred = tail.getAndSet(qnode);
    if (pred != null) { //  hay un predecesor?
      qnode.locked = true; // busy
      pred.next = qnode;
      while (qnode.locked) {}
    }
  }

  @Override
  public void unlock() {
    QNode qnode = myNode.get();
    if (qnode.next == null) { // no tengo sucesor?
      if (tail.compareAndSet(qnode, null)) {
        return; // si yo era el último de la lista, me aseguro de que al terminar la vuelvo a dejar vacía.
      }
      while (qnode.next == null) {} // esperar a que la nueva tail apunte yo hacia él.
    }
    qnode.next.locked = false; // marco que el siguiente ya es free
    qnode.next = null; // reutilizo mi nodo
  }
}
