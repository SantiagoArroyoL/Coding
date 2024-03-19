package unam.ciencias.computoconcurrente;

import java.lang.reflect.InvocationTargetException;
import org.junit.jupiter.api.Test;

public class TwoValueCounterTest {
  final int EXECUTIONS = 10;
  final int ITERATIONS = 100;
  final int ACCEPTANCE_PERCENTAGE = 3;
  final int EXPECTED_VALUE = 2;

  @Test
  void reachTwo()
      throws InterruptedException, InvocationTargetException, NoSuchMethodException,
          InstantiationException, IllegalAccessException {
    FixedValueCounterTestExecutor executor =
        new FixedValueCounterTestExecutor(
            EXECUTIONS, ITERATIONS, ACCEPTANCE_PERCENTAGE, EXPECTED_VALUE, TwoValueCounter.class);
    executor.executeTest();
  }
}
