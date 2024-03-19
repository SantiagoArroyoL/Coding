package unam.ciencias.computoconcurrente;

import java.util.concurrent.atomic.AtomicInteger;

public class ALock extends Lock {
  private final ThreadLocal<Integer> myIndex;
  private final AtomicInteger tail;
  private final VolatileInteger[] flag;

  public ALock(int capacity) {
    myIndex = ThreadLocal.withInitial(() -> 0);
    tail = new AtomicInteger(0);
    flag = new VolatileInteger[capacity];
    for (int i = 0; i < capacity; i++) {
      flag[i] = new VolatileInteger(0);
    }
    flag[0].value = 1;
  }

  @Override
  public void lock() {
    int index = tail.getAndIncrement() % this.flag.length;
    myIndex.set(index);
    while (flag[index].value == 0) {}
  }

  @Override
  public void unlock() {
    int index = myIndex.get();
    flag[index].value = 0;
    flag[(index + 1) % this.flag.length].value = 1;
  }
}
