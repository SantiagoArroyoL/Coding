package unam.ciencias.computoconcurrente;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.ArrayList;
import java.util.List;

public class LockTestExecutor {
  static final int EXECUTIONS = 5;
  static final int MAX_VALUE = 1000000;

  public static void performTest(Lock lock, int threadsToUse) throws InterruptedException {
    System.out.println("Using " + threadsToUse + " threads.");
    int workSizePerThread = MAX_VALUE / threadsToUse;
    int remainingWorkToBeDistributed = MAX_VALUE % threadsToUse;

    for (int i = 0; i < EXECUTIONS; i++) {
      Counter counter = new ThreadSafeCounter(lock);
      List<Thread> threads = new ArrayList<>(threadsToUse);
      lock.getThreadID().resetInitialThreadIDTo(0);

      for (int j = 0, remainingWork = remainingWorkToBeDistributed;
          j < threadsToUse;
          j++, remainingWork--) {
        final int size = workSizePerThread + (remainingWork > 0 ? 1 : 0);
        threads.add(new Thread(() -> incrementCounter(counter, size)));
      }

      for (Thread t : threads) {
        t.start();
      }

      for (Thread t : threads) {
        t.join();
      }

      assertEquals(MAX_VALUE, counter.getValue());
    }
  }

  static void incrementCounter(Counter counter, int iterations) {
    for (int i = 0; i < iterations; i++) {
      counter.getAndIncrement();
    }
  }
}
