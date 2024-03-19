package unam.ciencias.computoconcurrente;

public interface Semaphore {
  void down();

  void up();

  int permits();

  ThreadID getThreadId();
}
