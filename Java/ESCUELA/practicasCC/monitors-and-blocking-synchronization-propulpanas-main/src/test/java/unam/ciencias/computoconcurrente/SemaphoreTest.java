package unam.ciencias.computoconcurrente;

import static org.junit.jupiter.api.Assertions.*;

import java.util.concurrent.atomic.AtomicInteger;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class SemaphoreTest {

  static int ROUNDS = 100000;
  static int THREADS = Math.min(4, Runtime.getRuntime().availableProcessors());
  static int MAX_CONCURRENT_THREADS = 2;

  Semaphore semaphore;
  Thread[] threads;
  boolean isSemaphoreCorrect;
  AtomicInteger atomicInteger;

  volatile boolean isMaxConcurrencyAchieved;

  @BeforeEach
  public void setup() {
    isMaxConcurrencyAchieved = false;
    isSemaphoreCorrect = true;
    atomicInteger = new AtomicInteger(0);
    semaphore = new SemaphoreImpl(MAX_CONCURRENT_THREADS);
    initThreads();
  }

  @Test
  void semaphoreTest() throws InterruptedException {
    for (Thread t : threads) {
      t.start();
    }
    for (Thread t : threads) {
      t.join();
    }
    assertTrue(isSemaphoreCorrect);
    assertTrue(isMaxConcurrencyAchieved);
  }

  void initThreads() {
    semaphore.getThreadId().resetInitialThreadIDTo(0);
    threads = new Thread[THREADS];
    for (int i = 0; i < THREADS; i++) {
      threads[i] = new Thread(this::acquireRounds, String.format("%d", i));
    }
    Thread verifier = new Thread(this::verifySemaphoreIsCorrect);
    verifier.setDaemon(true);
    verifier.start();
  }

  void acquireRounds() {
    long myValue = 0;
    for (int i = 0; i < ROUNDS; i++) {
      semaphore.down();
      this.atomicInteger.incrementAndGet();
      myValue += this.simulateCriticalSection(Math.random() * 100);
      if ((i % 1000) == 0) this.sleepCurrentThreads(Math.random() * 10);
      this.atomicInteger.decrementAndGet();
      semaphore.up();
    }
    System.out.printf("%s reached value %d\n", Thread.currentThread().getName(), myValue);
  }

  Integer simulateCriticalSection(Double iterations) {
    int val = 0;
    for (int j = 0; j < iterations; j++) {
      val += j & 1;
    }
    return val;
  }

  void verifySemaphoreIsCorrect() {
    long i = 0L;
    while (true) {
      for (int j = 0; j < Math.random() * 100; j++) {
        isSemaphoreCorrect = isSemaphoreCorrect && (atomicInteger.get() <= MAX_CONCURRENT_THREADS);
        isMaxConcurrencyAchieved =
            isMaxConcurrencyAchieved || (atomicInteger.get() == MAX_CONCURRENT_THREADS);
      }
      if ((i % 6000) == 0) {
        sleepCurrentThreads(Math.random() * 50);
      }
      i++;
    }
  }

  void sleepCurrentThreads(Double aproxMilliseconds) {
    try {
      Thread.sleep(aproxMilliseconds.longValue());
    } catch (InterruptedException ie) {
      System.out.printf("%s  - Interrupt exception happened", Thread.currentThread().getName());
      throw new RuntimeException("Unexpected interrupt exception.");
    }
  }
}
