package unam.ciencias.computoconcurrente;

import java.util.concurrent.atomic.AtomicIntegerArray;

public class FilterLock implements Lock {

  private int threads;
  private AtomicIntegerArray threadLevel;
  private AtomicIntegerArray lastToEnterLevel;

  public FilterLock(int threads) {
    this.threads = threads;
    this.threadLevel = new AtomicIntegerArray(this.threads);
    this.lastToEnterLevel = new AtomicIntegerArray(this.threads);
    for (int i = 0; i < threadLevel.length(); i++) {
      threadLevel.set(i, 0);
      lastToEnterLevel.set(i, 0);
    }
  }

  @Override
  public void lock() {
    int threadId = ThreadID.get();

    for (int currentLevel = 0; currentLevel < this.lastToEnterLevel.length(); currentLevel++) {
      this.threadLevel.set(threadId, currentLevel);
      this.lastToEnterLevel.set(currentLevel, threadId);

      while (isThisThreadTheVictim(currentLevel) && isThereAThreadInAHigherLevel(currentLevel)) {}
    }
  }

  private boolean isThereAThreadInAHigherLevel(int currentLevel) {
    for (int level = currentLevel + 1; level < lastToEnterLevel.length(); level++) {
      if (lastToEnterLevel.get(level) == -1) return true;
    }
    return false;
  }

  boolean isThisThreadTheVictim(int level) {
    return ThreadID.get() == this.lastToEnterLevel.get(level);
  }

  @Override
  public void unlock() {
    this.threadLevel.set(ThreadID.get(), -1);
  }
}

/*
class VolatileInteger {
  public int getValue() {
    return value;
  }

  public void setValue(int value) {
    this.value = value;
  }

  volatile int value;

  public VolatileInteger(int value) {
    this.value = value;
  }
}
*/
