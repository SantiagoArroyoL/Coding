package unam.ciencias.computoconcurrente;

import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.greaterThanOrEqualTo;

import java.lang.reflect.InvocationTargetException;

public class FixedValueCounterTestExecutor {
  private int executions;
  private int iterationsPerThread;
  private int acceptancePercentage;
  private int expectedValue;

  public FixedValueCounterTestExecutor(
      int executions,
      int iterationsPerThread,
      int acceptancePercentage,
      int expectedValue) {
    this.executions = executions;
    this.iterationsPerThread = iterationsPerThread;
    this.acceptancePercentage = acceptancePercentage;
    this.expectedValue = expectedValue;
  }

  public void executeTest()
      throws InterruptedException, NoSuchMethodException, InvocationTargetException,
          InstantiationException, IllegalAccessException {
    Thread[] threads = new Thread[2];
    int validExecutions = 0;
    for (int i = 0; i < executions; i++) {
      FixedValueCounter counter = new FixedValueCounter(this.expectedValue);
      counter.setRounds(iterationsPerThread);
      ThreadID.resetInitialThreadIDTo(0);
      threads[0] = new Thread(() -> incrementCounter(counter, iterationsPerThread));
      threads[1] = new Thread(() -> incrementCounter(counter, iterationsPerThread));
      threads[0].start();
      threads[1].start();
      threads[0].join();
      threads[1].join();

      if (counter.getValue() == this.expectedValue) {
        validExecutions++;
        System.out.println("iteration " + i + " passes");
      } else {
        System.out.println("iteration " + i + " fails with value " + counter.getValue());
      }
    }
    System.out.println(validExecutions + "/" + executions + " valid Executions");
    assertThat(validExecutions, is(greaterThanOrEqualTo(acceptancePercentage)));
  }

  private void incrementCounter(FixedValueCounter counter, int iterations) {
    for (int i = 0; i < iterations; i++) {
      counter.setIteration(i);
      counter.getAndIncrement();
    }
  }
}
