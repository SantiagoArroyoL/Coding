package unam.ciencias.computoconcurrente;

import org.junit.jupiter.api.Test;

class LamportBakeryLockTest extends BaseTestSuite {
  @Test
  void twoThreaded() throws InterruptedException {
    LockTestExecutor.performTest(new LamportBakeryLock(2), 2);
  }

  @Test
  @DisableIfHasFewerThanFourCores
  void fourThreaded() throws InterruptedException {
    LockTestExecutor.performTest(new LamportBakeryLock(4), 4);
  }

  @Test
  @DisableIfHasFewerThanEightCores
  void eightThreaded() throws InterruptedException {
    LockTestExecutor.performTest(new LamportBakeryLock(8), 8);
  }

  @Test
  @EnableIfHasNotDefaultCores
  void maximumNumberOfThreads() throws InterruptedException {
    LockTestExecutor.performTest(
        new LamportBakeryLock(Runtime.getRuntime().availableProcessors()),
        Runtime.getRuntime().availableProcessors());
  }
}
