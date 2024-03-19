package unam.ciencias.computoconcurrente;

public interface Counter {

  int getAndIncrement();

  int getAndDecrement();

  int getValue();
}
