package unam.ciencias.computoconcurrente;

public class FixedValueCounter implements Counter {
  protected volatile int value;
  protected ThreadLocal<Integer> iteration;
  protected int rounds;
  protected final int valueToBeReached;

  public FixedValueCounter(int valueToBeReached) {
    this.value = 0;
    this.iteration = ThreadLocal.withInitial(() -> 0);
    this.rounds = 0;
    this.valueToBeReached = valueToBeReached;
  }

  public void setIteration(int iteration) {
    this.iteration.set(iteration);
  }

  public void setRounds(int rounds) {
    this.rounds = rounds;
  }

  @Override
  public int getAndIncrement() {
    int id = ThreadID.get();
    int it = iteration.get();

    // Verificar si el valor actual ya alcanzó el valor objetivo
    if (value < valueToBeReached) {
      // Incrementar el valor y la iteración
      value++;
      iteration.set(it + 1);
    }

    // Devolver el valor actual
    return value;
  }

  @Override
  public int getAndDecrement() {
    int id = ThreadID.get();
    int it = iteration.get();

    // Verificar si el valor actual es mayor que 0
    if (value > 0) {
      // Decrementar el valor y la iteración
      value--;
      iteration.set(it + 1);
    }

    // Devolver el valor actual
    return value;
  }

  @Override
  public int getValue() {
    return this.value;
  }
}
