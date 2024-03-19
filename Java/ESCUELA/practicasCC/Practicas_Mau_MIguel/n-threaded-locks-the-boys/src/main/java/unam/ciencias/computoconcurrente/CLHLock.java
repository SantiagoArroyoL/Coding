package unam.ciencias.computoconcurrente;

import java.util.concurrent.atomic.AtomicReference;

public class CLHLock extends Lock {
  public static class QNode {
    volatile boolean locked;

    QNode() {
      locked = false;
    } // free
  }

  private final AtomicReference<QNode> tail;
  private final ThreadLocal<QNode> myPred;
  private final ThreadLocal<QNode> myNode;

  public CLHLock() {
    tail = new AtomicReference<>(new QNode());
    myNode = ThreadLocal.withInitial(QNode::new);
    myPred = ThreadLocal.withInitial(() -> null);
  }

  @Override
  public void lock() {
    QNode qnode = myNode.get();
    qnode.locked = true; // busy
    QNode pred = tail.getAndSet(qnode); // me formo en la cola y obtengo el predecesor
    myPred.set(pred); // me acuerdo quien es mi predecesor
    while (pred.locked) {}
  }

  @Override
  public void unlock() {
    QNode qnode = myNode.get();
    qnode.locked = false; // mi nodo lo marco como free
    myNode.set(myPred.get()); // reutilizas el nodo predecesor
  }
}
