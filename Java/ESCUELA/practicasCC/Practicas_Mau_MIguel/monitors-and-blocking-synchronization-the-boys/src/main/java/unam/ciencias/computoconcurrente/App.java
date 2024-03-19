package unam.ciencias.computoconcurrente;

import java.util.concurrent.ThreadLocalRandom;

public class App {

  static ThreadID threadID = new ThreadID();

  public static void main(String[] args) throws InterruptedException {
    // No need to do anything in this exercise in the App class
    System.out.println("Welcome to concurrent programming exercise #3");

    Thread t1 = new Thread(App::task);
    Thread t2 = new Thread(App::task);

    t1.start();
    t2.start();

    t1.join();
    t2.join();
  }

  static void task() {
    try {
      Thread.sleep(ThreadLocalRandom.current().nextInt(100, 1000));
    } catch (InterruptedException e) {
      e.printStackTrace();
    }
    // each thread get assigned a different
    System.out.println(
        "hello from thread "
            + threadID.get()
            + ", thread name "
            + Thread.currentThread().getName());
  }
}
