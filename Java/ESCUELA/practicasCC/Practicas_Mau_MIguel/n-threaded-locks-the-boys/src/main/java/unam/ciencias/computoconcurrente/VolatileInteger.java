package unam.ciencias.computoconcurrente;

public class VolatileInteger {
  public volatile int value;

  public VolatileInteger() {}

  public VolatileInteger(int value) {
    this.value = value;
  }

  public int getValue() {
    return value;
  }

  public void setValue(int value) {
    this.value = value;
  }
}
