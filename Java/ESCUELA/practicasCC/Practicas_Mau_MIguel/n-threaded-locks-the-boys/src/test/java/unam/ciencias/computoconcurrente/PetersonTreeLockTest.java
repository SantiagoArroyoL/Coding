package unam.ciencias.computoconcurrente;

import org.junit.jupiter.api.Test;

class PetersonTreeLockTest extends BaseTestSuite {
  @Test
  void twoThreaded() throws InterruptedException {
    LockTestExecutor.performTest(new PetersonTreeLock(2), 2);
  }

  @Test
  void threeThreaded() throws InterruptedException {
    LockTestExecutor.performTest(new PetersonTreeLock(3), 3);
  }

  @Test
  void fourThreaded() throws InterruptedException {
    LockTestExecutor.performTest(new PetersonTreeLock(4), 4);
  }

  @Test
  @DisableIfHasFewerThanEightCores
  void eightThreaded() throws InterruptedException {
    LockTestExecutor.performTest(new PetersonTreeLock(8), 8);
  }
}