package unam.ciencias.computoconcurrente;

public class FiveValueCounter extends FixedValueCounter {
  public FiveValueCounter() {
    super();
  }

  @Override
  public int getAndIncrement() {
    return 0;
  }

  @Override
  public int getAndDecrement() {
    return 0;
  }
}
