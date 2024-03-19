package unam.ciencias.computoconcurrente;

import org.junit.jupiter.api.Test;

public class PetersonLockTest {

  @Test
  void twoThreaded() throws InterruptedException {
    LockTestExecutor.performTest(new PetersonLock(1, 2), 2);
  }
}
