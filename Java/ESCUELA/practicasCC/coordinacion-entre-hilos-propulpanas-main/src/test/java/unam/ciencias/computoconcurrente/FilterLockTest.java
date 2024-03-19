package unam.ciencias.computoconcurrente;

import static org.hamcrest.CoreMatchers.equalTo;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.MatcherAssert.assertThat;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

@EnabledIf("testSuiteEnabled")
public class FilterLockTest {

  static boolean testSuiteEnabled() {
    return PropertiesLoader.getBooleanProperty("filter-lock.enabled");
  }

  static final int ITERATIONS = 20;
  static final int MAX_VALUE = 10000;

  Lock lock;
  Counter counter;

  @Test
  public void test() throws InterruptedException {
    int threadNum = Runtime.getRuntime().availableProcessors();
    for (int iter = 0; iter < ITERATIONS; iter++) {
      lock = new FilterLock(threadNum);
      counter = new ThreadSafeCounter(lock);
      Thread[] threads = new Thread[threadNum];
      ThreadID.resetInitialThreadIDTo(0);
      for (int i = 0; i < threadNum; i++) {
        threads[i] = new Thread(this::incrementCounter, Integer.toString(i));
      }
      for (Thread t : threads) {
        t.start();
      }
      for (Thread t : threads) {
        t.join();
      }
      assertThat(counter.getValue(), is(equalTo(MAX_VALUE * threadNum)));
    }
  }

  void incrementCounter() {
    for (int i = 0; i < MAX_VALUE; i++) {
      counter.getAndIncrement();
    }
  }
}
