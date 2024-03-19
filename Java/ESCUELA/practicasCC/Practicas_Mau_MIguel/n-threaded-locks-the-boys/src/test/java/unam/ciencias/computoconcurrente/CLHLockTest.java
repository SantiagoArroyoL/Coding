package unam.ciencias.computoconcurrente;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.DisabledIfEnvironmentVariable;

@DisabledIfEnvironmentVariable(named = "ENV", matches = "github")
public class CLHLockTest extends BaseTestSuite {
  @Test
  void twoThreaded() throws InterruptedException {
    LockTestExecutor.performTest(new CLHLock(), 2);
  }

  @Test
  @DisableIfHasFewerThanFourCores
  void fourThreaded() throws InterruptedException {
    LockTestExecutor.performTest(new CLHLock(), 4);
  }

  @Test
  @DisableIfHasFewerThanEightCores
  void eightThreaded() throws InterruptedException {
    LockTestExecutor.performTest(new CLHLock(), 8);
  }

  @Test
  @EnableIfHasNotDefaultCores
  void maximumNumberOfThreads() throws InterruptedException {
    LockTestExecutor.performTest(new CLHLock(), Runtime.getRuntime().availableProcessors());
  }
}
