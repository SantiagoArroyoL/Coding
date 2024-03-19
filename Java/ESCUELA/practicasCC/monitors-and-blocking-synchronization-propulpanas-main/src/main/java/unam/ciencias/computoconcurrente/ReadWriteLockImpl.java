package unam.ciencias.computoconcurrente;

import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class ReadWriteLockImpl implements ReadWriteLock {

  private Lock readLock;
  private Lock writeLock;

  private boolean writer;
  private int readers;
  private Lock lock;
  private Condition condition;

  public ReadWriteLockImpl() {
    this.writer = false;
    this.readers = 0;
    this.lock = new ReentrantLock();
    this.condition = this.lock.newCondition();
    this.readLock = new ReadLock();
    this.writeLock = new WriteLock();
  }

  @Override
  public Lock readLock() {
    return readLock;
  }

  @Override
  public Lock writeLock() {
    return writeLock;
  }

  class ReadLock implements Lock {
    @Override
    public void lock() {
      lock.lock();
      try {
        while (writer) {
          condition.wait();
        }
        readers++;
      } catch (InterruptedException e) {
        e.printStackTrace();
      } finally {
        lock.unlock();
      }
    }

    @Override
    public void unlock() {
      lock.lock();
      try {
        readers--;
        condition.signalAll();
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
      return null;
    }
  }

  class WriteLock implements Lock {
    @Override
    public void lock() {
      lock.lock();
      try {
        while (writer || readers > 0) {
          condition.wait();
        }
        writer = true;
      } catch (InterruptedException e) {
        e.printStackTrace();
      } finally {
        lock.unlock();
      }
    }

    @Override
    public void unlock() {
      lock.lock();
      try {
        writer = false;
        condition.signalAll();
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
      return null;
    }
  }
}
