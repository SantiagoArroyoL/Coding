package unam.ciencias.computoconcurrente;

import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;

public class TTASLock implements Lock {

  AtomicBoolean flag = new AtomicBoolean(false);

  @Override
  public void lock() {
    while (true) {
      while (!flag.get()) {}
      if (!flag.getAndSet(true)) {
        return;
      }
    }
  }

  @Override
  public void unlock() {
    flag.set(false);
  }

  @Override
  public void lockInterruptibly() throws InterruptedException {}

  @Override
  public boolean tryLock() {
    return false;
  }

  @Override
  public boolean tryLock(long time, TimeUnit unit) throws InterruptedException {
    return false;
  }

  @Override
  public Condition newCondition() {
    return null;
  }
}
