package unam.ciencias.computoconcurrente;

import java.util.concurrent.ThreadLocalRandom;
import java.util.concurrent.atomic.AtomicBoolean;

public class BackoffLock extends Lock {
  private final AtomicBoolean lock;

  public BackoffLock() {
    lock = new AtomicBoolean(false);
  }

  @Override
  public void lock() {
    Backoff backoff = new Backoff(10, 1000);
    while (true) {
      while (lock.get()) {}
      if (!lock.getAndSet(true)) {
        return;
      } else {
        backoff.backoff();
      }
    }
  }

  @Override
  public void unlock() {
    lock.set(false);
  }
}

class Backoff {
  private final int minDelay, maxDelay;
  private int limit;

  public Backoff(int min, int max) {
    minDelay = min;
    maxDelay = max;
    limit = minDelay;
  }

  public void backoff() {
    int delay = ThreadLocalRandom.current().nextInt(limit);
    limit = Math.min(maxDelay, 2 * limit);
    sleepCurrentThread(delay);
  }

  void sleepCurrentThread(long timeInMs) {
    try {
      Thread.sleep(timeInMs);
    } catch (InterruptedException ie) {
      System.out.printf("%s  - Interrupt exception happened", Thread.currentThread().getName());
      throw new RuntimeException("Unexpected interrupt exception.");
    }
  }
}
