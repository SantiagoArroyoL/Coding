package unam.ciencias.computoconcurrente;

import java.util.Date;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;

public class ReentrantLock implements Lock {

  ThreadID threadID;

  Lock lock;
  Condition condition;
  int owner;
  int holdCount;

  public ReentrantLock() {
    this.threadID = new ThreadID();
    this.lock = new TTASLock();
  }

  @Override
  public void lock() {
    lock.lock();
    try {
      int myId = this.threadID.get();
      if (myId == owner) {
        holdCount++;
        return;
      }
      while (holdCount > 0) {
        try {
          condition.await();
        } catch (InterruptedException e) {
          e.printStackTrace();
        }
      }

      owner = myId;
      holdCount = 1;
    } finally {
      lock.unlock();
    }
  }

  @Override
  public void unlock() {
    lock.lock();
    try {
      int myId = this.threadID.get();
      if (owner != myId || holdCount > 0) {
        throw new IllegalMonitorStateException();
      }
      holdCount--;
      if (holdCount == 0) {
        condition.signalAll();
      }
    } finally {
      lock.unlock();
    }
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
    return new Condition() {
      @Override
      public void await() throws InterruptedException {}

      @Override
      public void awaitUninterruptibly() {}

      @Override
      public long awaitNanos(long nanosTimeout) throws InterruptedException {
        return 0;
      }

      @Override
      public boolean await(long time, TimeUnit unit) throws InterruptedException {
        return false;
      }

      @Override
      public boolean awaitUntil(Date deadline) throws InterruptedException {
        return false;
      }

      @Override
      public void signal() {}

      @Override
      public void signalAll() {}
    };
  }
}
