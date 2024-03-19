package unam.ciencias.computoconcurrente;

public class App {

  public static void main(String[] a) throws InterruptedException {
    System.out.println("Bienvenido al ejercicio de coordinación entre hilos");

    Thread t1 = new Thread(App::printId);
    Thread t2 = new Thread(App::printId);

    t1.start();
    t2.start();

    t1.join();
    t2.join();
  }

  static void printId() {
    System.out.println("Hello from thread " + ThreadID.get());
  }
}
