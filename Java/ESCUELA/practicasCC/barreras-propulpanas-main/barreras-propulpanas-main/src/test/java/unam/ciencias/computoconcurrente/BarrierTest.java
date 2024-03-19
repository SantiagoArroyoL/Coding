package unam.ciencias.computoconcurrente;

import static org.junit.jupiter.api.Assertions.*;

import java.util.concurrent.atomic.AtomicInteger;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class BarrierTest {

  static int THREADS_COUNT = 7;
  static int FRAMES_LEN = 100;
  static int RADIX = 2;

  Thread[] threads;
  Thread verificationThread;
  Barrier barrier;

  AtomicInteger[] frames;
  boolean isFramesArrayValid;

  @Test
  void test() throws InterruptedException {
    for (Thread t : threads) {
      t.start();
    }
    this.verifyFramesArray();
    for (Thread t : threads) {
      t.join();
    }
    assertTrue(this.isFramesArrayValid);
  }

  @BeforeEach
  public void setUp() {
    barrier = new StaticTreeBarrier(THREADS_COUNT, RADIX);
    isFramesArrayValid = true;
    setUpFrames();
    setUpThreads();
    setUpVerificationThread();
  }

  public void setUpFrames() {
    frames = new AtomicInteger[FRAMES_LEN];
    for (int i = 0; i < frames.length; i++) {
      frames[i] = new AtomicInteger(0);
    }
  }

  void setUpThreads() {
    threads = new Thread[THREADS_COUNT];
    for (int i = 0; i < threads.length; i++) {
      threads[i] = new Thread(this::fillFrames, String.format("%d", i));
    }
  }

  void fillFrames() {
    for (int i = 0; i < FRAMES_LEN; i++) {
      frames[i].getAndIncrement();
      barrier.await();
      Utils.sleepCurrentThread((int) (Math.random() * 100));
    }
  }

  void setUpVerificationThread() {
    verificationThread = new Thread(this::verifyFramesArray, "Verification Thread");
  }

  void verifyFramesArray() {
    boolean isFramesArrayFilled = false;
    while (!isFramesArrayFilled) {
      this.isFramesArrayValid = this.isFramesArrayValid && isFramesArrayValid();
      isFramesArrayFilled = isFramesArrayFilled();
      Utils.sleepCurrentThread((int) (Math.random() * 20));
    }
  }

  boolean isFramesArrayValid() {
    boolean isValid = true;
    for (int i = 0; i < frames.length - 1; i++) {
      int cur = frames[i].get(), next = frames[i + 1].get();
      boolean cond1 = cur > 0 && cur < THREADS_COUNT && next == 0,
          cond2 = cur == THREADS_COUNT,
          cond3 = cur == 0 && next == 0,
          cond = cond1 || cond2 || cond3;
      isValid = isValid && cond;
    }
    return isValid;
  }

  boolean isFramesArrayFilled() {
    boolean isFilled = true;
    for (AtomicInteger i : frames) {
      isFilled = isFilled && i.get() == THREADS_COUNT;
    }
    return isFilled;
  }
}
