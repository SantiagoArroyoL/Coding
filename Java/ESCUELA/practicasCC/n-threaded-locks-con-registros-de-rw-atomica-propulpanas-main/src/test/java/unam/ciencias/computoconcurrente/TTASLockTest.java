package unam.ciencias.computoconcurrente;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.DisabledIfEnvironmentVariable;

@DisabledIfEnvironmentVariable(named = "ENV", matches = "github")
public class TTASLockTest extends BaseTestSuite {
  @Test
  void twoThreaded() throws InterruptedException {
    LockTestExecutor.performTest(new TTASLock(), 2);
  }

  @Test
  void fourThreaded() throws InterruptedException {
    LockTestExecutor.performTest(new TTASLock(), 4);
  }

  @Test
  void eightThreaded() throws InterruptedException {
    LockTestExecutor.performTest(new TTASLock(), 8);
  }
}
