package unam.ciencias.computoconcurrente;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.DisabledIfEnvironmentVariable;

@DisabledIfEnvironmentVariable(named = "ENV", matches = "github")
public class BackoffLockTest extends BaseTestSuite {
  @Test
  void twoThreaded() throws InterruptedException {
    LockTestExecutor.performTest(new BackoffLock(), 2);
  }

  @Test
  @EnableIfHasNotDefaultCores
  void maximumNumberOfThreads() throws InterruptedException {
    LockTestExecutor.performTest(new BackoffLock(), Runtime.getRuntime().availableProcessors());
  }

  @Test
  @DisableIfHasFewerThanFourCores
  void fourThreaded() throws InterruptedException {
    LockTestExecutor.performTest(new BackoffLock(), 4);
  }

  @Test
  @DisableIfHasFewerThanEightCores
  void eightThreaded() throws InterruptedException {
    LockTestExecutor.performTest(new BackoffLock(), 8);
  }
}
