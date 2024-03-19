package unam.ciencias.computoconcurrente;

import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;

public class ConditionsBoundedBuffer<T> implements Buffer<T> {

  public static final int DEFAULT_SIZE = 20;

  final Lock lock;
  final Condition notFull;
  final Condition notEmpty;

  final T[] items;

  int putIndex, takeIndex, elements;

  public ConditionsBoundedBuffer(int size) {
    this.items = (T[]) new Object[size];
    this.lock = new ReentrantLock();
    this.notFull = lock.newCondition();
    this.notEmpty = lock.newCondition();
    putIndex = takeIndex = elements = 0;
  }

  @Override
  public void put(T x) throws InterruptedException {
    lock.lock();
    try {
      while (elements == items.length) {
        notFull.await();
      }
      items[putIndex] = x;
      if (++putIndex == items.length) {
        putIndex = 0;
      }
      ++elements;
      notEmpty.signal();
    } finally {
      lock.unlock();
    }
  }

  @Override
  public T take() throws InterruptedException {
    lock.lock();
    try {
      while (elements == 0) {
        notEmpty.await();
      }

      T x = items[takeIndex];
      if (++takeIndex == items.length) takeIndex = 0;
      --elements;
      notFull.signal();
      return x;
    } finally {
      lock.unlock();
    }
  }

  @Override
  public int size() {
    return this.items.length;
  }

  @Override
  public int elements() {
    return this.elements;
  }
}
