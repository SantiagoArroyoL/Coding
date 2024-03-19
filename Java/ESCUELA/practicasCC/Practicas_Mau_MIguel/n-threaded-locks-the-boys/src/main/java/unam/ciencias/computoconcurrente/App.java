package unam.ciencias.computoconcurrente;


import java.util.concurrent.Semaphore;

public class App {
  static Semaphore semaphore = new Semaphore(0);
  static int counter = 0;

  public static void main(String[] args) throws InterruptedException {
    System.out.println("Hello World");

    new Thread(App::jobT2, "T2").start();
    new Thread(App::jobT1, "T1").start();
  }

  static void jobT1() {
    try {
      semaphore.acquire();
      System.out.printf("%s -> (2) Done waiting, Counter: %d%n", Thread.currentThread().getName(), counter);
    } catch (InterruptedException e) {
      throw new RuntimeException(e);
    }
  }

  static void jobT2() {
    for (int i = 0; i < 1000000; i++) {
      counter++;
    }
    System.out.printf("%s -> (1) Done working%n", Thread.currentThread().getName());
    semaphore.release();
  }

}
