package unam.ciencias.computoconcurrente;

import static org.hamcrest.CoreMatchers.equalTo;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.MatcherAssert.assertThat;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

public class PetersonLockTest {
  static final int ITERATIONS = 20;
  static final int MAX_VALUE = 10000;
  Lock lock;
  Counter counter;

  @BeforeEach
  void setUp() {
    lock = new PetersonLock();
  }

  @Test
  void lock() throws InterruptedException {

    for (int i = 0; i < ITERATIONS; i++) {
      ThreadID.resetInitialThreadIDTo(0);
      counter = new ThreadSafeCounter(lock);
      Thread[] threads = new Thread[2];
      threads[0] = new Thread(this::incrementCounter, "0");
      threads[1] = new Thread(this::incrementCounter, "1");
      threads[0].start();
      threads[1].start();
      threads[0].join();
      threads[1].join();
      assertThat(2 * MAX_VALUE, is(equalTo(counter.getValue())));
    }
  }

  void incrementCounter() {
    for (int i = 0; i < MAX_VALUE; i++) {
      counter.getAndIncrement();
    }
  }
}
