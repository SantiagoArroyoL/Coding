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
      flag[i] = new VolatileInteger(0); // busy
    }
    flag[0].value = 1; // free
  }

  @Override
  public void lock() {
    int index = tail.getAndIncrement() % this.flag.length;
    myIndex.set(index);
    while (flag[index].value == 0) {} // giro mientras esté busy
  }

  @Override
  public void unlock() {
    int index = myIndex.get();
    flag[index].value = 0; // marco mi ubicación como busy
    flag[(index + 1) % this.flag.length].value = 1; // le aviso al que sigue que está free
  }
}
