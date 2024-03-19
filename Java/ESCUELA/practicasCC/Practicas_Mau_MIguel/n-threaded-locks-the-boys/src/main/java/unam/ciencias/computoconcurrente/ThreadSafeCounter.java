package unam.ciencias.computoconcurrente;

public class ThreadSafeCounter implements Counter {
  private final Lock lock;
  private int value;

  public ThreadSafeCounter(Lock lock) {
    this.value = 0;
    this.lock = lock;
  }

  @Override
  public int getAndIncrement() {
    int result;
    this.lock.lock();
    try {
      result = this.value;
      this.value = this.value + 1;
    } finally {
      this.lock.unlock();
    }
    return result;
  }

  @Override
  public int getAndDecrement() {
    int result;
    this.lock.lock();
    try {
      result = this.value;
      this.value = this.value - 1;
    } finally {
      this.lock.unlock();
    }
    return result;
  }

  @Override
  public int getValue() {
    return this.value;
  }
}
