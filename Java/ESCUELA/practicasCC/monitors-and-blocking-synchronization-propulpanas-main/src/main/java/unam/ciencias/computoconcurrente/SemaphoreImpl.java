package unam.ciencias.computoconcurrente;

import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class SemaphoreImpl implements Semaphore {

  private final int capacity;
  private final Lock lock;
  private final Condition condition;
  private int availableSlots;

  private ThreadID threadID;

  public SemaphoreImpl(int capacity) {
    this.capacity = capacity;
    this.lock = new ReentrantLock();
    this.condition = this.lock.newCondition();
    this.availableSlots = this.capacity;
    this.threadID = new ThreadID();
  }

  @Override
  public void down() {
    this.lock.lock();
    try {
      while (availableSlots == 0) {
        try {
          this.condition.await(200, TimeUnit.MILLISECONDS);
        } catch (InterruptedException e) {
          e.printStackTrace();
        }
      }
      this.availableSlots--;
    } finally {
      this.lock.unlock();
    }
  }

  @Override
  public void up() {
    this.lock.lock();
    try {
      this.availableSlots++;
      this.condition.signalAll();
      // this.condition.signal(); // ¿Por que no?
    } finally {
      this.lock.unlock();
    }
  }

  @Override
  public int permits() {
    return this.capacity;
  }

  @Override
  public ThreadID getThreadId() {
    return this.threadID;
  }
}
