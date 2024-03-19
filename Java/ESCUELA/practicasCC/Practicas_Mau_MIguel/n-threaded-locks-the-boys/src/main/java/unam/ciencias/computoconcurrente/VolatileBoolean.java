package unam.ciencias.computoconcurrente;

public class VolatileBoolean {
  public volatile boolean value;

  public VolatileBoolean() {}

  public VolatileBoolean(boolean value) {
    this.value = value;
  }

  public boolean isValue() {
    return value;
  }

  public void setValue(boolean value) {
    this.value = value;
  }
}
