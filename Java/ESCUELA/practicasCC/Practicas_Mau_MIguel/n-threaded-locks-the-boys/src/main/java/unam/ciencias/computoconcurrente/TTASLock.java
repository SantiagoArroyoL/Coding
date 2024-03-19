package unam.ciencias.computoconcurrente;

import java.util.concurrent.atomic.AtomicBoolean;

public class TTASLock extends Lock {
  private final AtomicBoolean lock;

  public TTASLock() {
    lock = new AtomicBoolean(false);
  }

  @Override
  public void lock() {
    while (true) {
      while (lock.get()) {}
      if (!lock.getAndSet(true)) return;
    }
  }

  @Override
  public void unlock() {
    lock.set(false);
  }
}
