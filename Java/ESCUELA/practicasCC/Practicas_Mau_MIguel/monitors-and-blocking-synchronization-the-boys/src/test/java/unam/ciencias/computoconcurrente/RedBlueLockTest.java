package unam.ciencias.computoconcurrente;



import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.ThreadLocalRandom;
import java.util.concurrent.locks.Lock;

import static org.hamcrest.MatcherAssert.*;
import static org.hamcrest.CoreMatchers.*;

public class RedBlueLockTest {
  final int ITERATIONS = 500;
  final int SIMULATION_DURATION_MS = 10000;
  Thread verifier;
  List<Thread> blueThreadList = new ArrayList<>();
  List<Thread> redThreadList = new ArrayList<>();
  List<Thread> allThreadList = new ArrayList<>();

  int invalidStates = 0;
  int totalStates = 0;

  RedBlueLock redBlueLock;

  Boolean[] threadFinished;

  ThreadID threadID;

  @BeforeEach
  void setUp() {
    threadID = new ThreadID();
    redBlueLock = new FairRedBlueLock();
    blueThreadList = new ArrayList<>();
    redThreadList = new ArrayList<>();
    allThreadList = new ArrayList<>();
    setUpVerificationThread();
  }

  void setUpVerificationThread() {
    verifier = new Thread(this::performVerifications, "Verifier");
    verifier.setDaemon(true);
    verifier.start();
  }

  @Test
  void testOneRedOneBlue() throws InterruptedException {
    initRedAndBlueThreads(1, 1);
    runThreads();
    waitForThreadsToComplete();
    stopThreads();
    assertThat(invalidStates, is(0));
    assertThat(allThreadsFinished(), is(true));
  }

  @Test
  void testOneRedMultipleBlue() throws InterruptedException {
    initRedAndBlueThreads(1, 2);
    runThreads();
    waitForThreadsToComplete();
    stopThreads();
    assertThat(invalidStates, is(0));
    assertThat(allThreadsFinished(), is(true));
  }

  @Test
  void testMultipleRedOneBlue() throws InterruptedException {
    initRedAndBlueThreads(2, 1);
    runThreads();
    waitForThreadsToComplete();
    stopThreads();
    assertThat(invalidStates, is(0));
    assertThat(allThreadsFinished(), is(true));
  }

  @Test
  void testMultipleRedMultipleBlue() throws InterruptedException {
    initRedAndBlueThreads(3, 2);
    runThreads();
    waitForThreadsToComplete();
    stopThreads();
    assertThat(invalidStates, is(0));
    assertThat(allThreadsFinished(), is(true));
  }

  void initRedAndBlueThreads(int redThreads, int blueThreads) {
    initRedThreads(redThreads);
    initBlueThreads(blueThreads);
    threadFinished = new Boolean[redThreads + blueThreads];
  }

  void initRedThreads(int redThreads) {
    for (int t = 0; t < redThreads; t++) {
      Thread thread = new Thread(
        () -> performWork(redBlueLock.getRedLock()),
        "RedThread" + (t+1)
      );
      redThreadList.add(thread);
      allThreadList.add(thread);
    }
  }

  void initBlueThreads(int blueThreads) {
    for (int t = 0; t < blueThreads; t++) {
      Thread thread = new Thread(
        () -> performWork(redBlueLock.getBlueLock()),
        "BlueThread" + (t+1)
      );
      blueThreadList.add(thread);
      allThreadList.add(thread);
    }
  }

  void runThreads() {
    for (var t : allThreadList) {
      t.start();
    }
  }

  void waitForThreadsToComplete() throws InterruptedException {
    int waits = 0;
    while(allThreadList.stream().anyMatch(Thread::isAlive) && waits * 1000 < SIMULATION_DURATION_MS) {
      Thread.sleep(1000);
      waits++;
    }
  }

  void stopThreads() throws InterruptedException {
    for (var thread : allThreadList) {
      if (thread.isAlive()) {
        thread.interrupt();
      }
    }
    verifier.join();
  }

  void performWork(Lock lock) {
    threadFinished[threadID.get()] = false;
    for (int it = 0; it < ITERATIONS; it++) {
      if (Thread.interrupted()) {
        System.out.printf("Thread %s was interrupted after %d rounds\n",
          Thread.currentThread().getName(),
          it
        );
        return;
      }
      lock.lock();
      try {
        // do something and then sleep
        sleepRandomTime(10);
      } finally {
        lock.unlock();
      }
    }
    threadFinished[threadID.get()] = true;
  }

  void performVerifications() {
    while (allThreadList.stream().anyMatch(Thread::isAlive)) {
      int[] redAndBlueThreads = redBlueLock.redAndBlueThreadCount();
      if (redAndBlueThreads[0] != 0
        && redAndBlueThreads[1] != 0) {
        invalidStates++;
      }
      totalStates++;
      sleepRandomTime(5);
    }
  }

  boolean allThreadsFinished() {
    return Arrays.stream(threadFinished).allMatch(finished -> finished);
  }

  static boolean sleepRandomTime(int limit) {
    try {
      if (!Thread.currentThread().getName().equals("main")) {
        Thread.sleep(Math.abs(ThreadLocalRandom.current().nextInt() % limit));
      }
      return true;
    } catch (InterruptedException e) {
      return false;
    }
  }
}
