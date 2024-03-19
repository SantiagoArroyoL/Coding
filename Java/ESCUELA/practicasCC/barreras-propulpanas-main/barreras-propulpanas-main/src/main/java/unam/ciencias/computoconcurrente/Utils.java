package unam.ciencias.computoconcurrente;

public class Utils {
  static void sleepCurrentThread(int ms) {
    try {
      Thread.sleep(ms);
    } catch (InterruptedException e) {
      String name = Thread.currentThread().getName();
      System.err.printf("Thread %s was interrupted.\n", name);
    }
  }
}
