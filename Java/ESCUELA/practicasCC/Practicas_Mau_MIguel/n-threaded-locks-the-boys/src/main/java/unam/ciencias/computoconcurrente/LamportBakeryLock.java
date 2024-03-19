package unam.ciencias.computoconcurrente;

import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;

public class LamportBakeryLock extends Lock {
  private final int threads;
  AtomicBoolean[] flag;
  AtomicInteger[] label;

  public LamportBakeryLock(int threads) {
    this.threads = threads;
    flag = new AtomicBoolean[threads];
    label = new AtomicInteger[threads];
    for (int i = 0; i < threads; i++) {
      flag[i] = new AtomicBoolean(false);
      label[i] = new AtomicInteger(0);
    }
  }

  @Override
  public void lock() {
    int threadId = this.getThreadID().get();
    flag[threadId].set(true);
    label[threadId].set(getMaxLabel() + 1);

    for (int i = 0; i < threads; i++) {
      if (i != threadId) {
        while (flag[i].get()
                && (label[threadId].get() > label[i].get()
                || (label[threadId].get() == label[i].get() && threadId > i))) {}
      }
    }
  }

  @Override
  public void unlock() {
    int threadId = this.getThreadID().get();
    flag[threadId].set(false);
  }

  private int getMaxLabel() {
    int maxLabel = Integer.MIN_VALUE;
    for (int i = 0; i < threads; i++) {
      int currentNumber = this.label[i].get();
      if (currentNumber > maxLabel) {
        maxLabel = currentNumber;
      }
    }
    return maxLabel;
  }
}
