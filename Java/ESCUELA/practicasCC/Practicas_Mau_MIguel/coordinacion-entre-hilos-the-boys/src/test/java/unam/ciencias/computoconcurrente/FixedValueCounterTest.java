package unam.ciencias.computoconcurrente;

import org.junit.jupiter.api.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.Random;

public class FixedValueCounterTest {
  final int EXECUTIONS = 10;
  final int ITERATIONS = 100;
  final int ACCEPTANCE_PERCENTAGE = 3;

  final int DIFFERENT_VALUES = 10;

  @Test
  void reachFixedValue()
      throws InterruptedException, InvocationTargetException, NoSuchMethodException,
          InstantiationException, IllegalAccessException {
    Random random = new Random();
    for (int it = 0; it < DIFFERENT_VALUES; it++) {
      int expectedValue = Math.abs(random.nextInt() % (ITERATIONS - 2)) + 2;
      System.out.println("EXPECTED_VALUE: " + expectedValue);
      FixedValueCounterTestExecutor executor =
        new FixedValueCounterTestExecutor(
          EXECUTIONS, ITERATIONS, ACCEPTANCE_PERCENTAGE, expectedValue);
      executor.executeTest();
    }
  }
}
