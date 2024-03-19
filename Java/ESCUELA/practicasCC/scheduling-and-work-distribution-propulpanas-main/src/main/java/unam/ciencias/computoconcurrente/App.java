package unam.ciencias.computoconcurrente;

import java.util.concurrent.*;
import unam.ciencias.computoconcurrente.ejemplos.FibForkJoin;

public class App {

  public static void main(String[] a) throws ExecutionException, InterruptedException {
    forkJoinPoolExample();
  }

  static void forkJoinPoolExample() throws ExecutionException, InterruptedException {
    FibForkJoin fibNTask = new FibForkJoin(5);
    ForkJoinPool forkJoinPool = ForkJoinPool.commonPool();
    Integer fibN = forkJoinPool.invoke(fibNTask);
    System.out.println(fibN);
  }

  static void completableFuturesExample() throws ExecutionException, InterruptedException {
    SquareCalculator calculator = new SquareCalculator();

    Future<Integer> asyncResultOne = calculator.asyncSquare(8);
    Future<Integer> asyncResultTwo = calculator.asyncSquare(7);

    // Aqui podemos hacer otras tareas
    while (!asyncResultOne.isDone() || !asyncResultTwo.isDone()) {
      System.out.printf(
          "Future One %s, Future Two %s \n",
          asyncResultOne.isDone() ? "done" : "not done",
          asyncResultTwo.isDone() ? "done" : "not done");
      Thread.sleep(250);
    }

    // Aquí preguntamos por el valor de future, es decir, esperamos hasta que realmente sea
    // necesario.
    System.out.println("The result for future one is " + asyncResultOne.get());
    System.out.println("The result for future two is " + asyncResultTwo.get());
    // Similar a async - await
    System.out.println("Main thread finishes");

    System.out.println(Thread.currentThread().getName());
    String myStr = "Hello   ";
    CompletableFuture<String> completableFuture =
        CompletableFuture.supplyAsync(
            () -> {
              System.out.println(Thread.currentThread().getName());
              String mySubStr = myStr.substring(0, 5);
              // ...
              // Aqui hacemos cálculos que son muy pesados en computo
              // ...
              return mySubStr;
            });
    CompletableFuture<String> next =
        completableFuture.thenApplyAsync(
            s -> {
              System.out.println(Thread.currentThread().getName());
              return s + " World";
            });
    System.out.println(
        next.thenApply(
                s -> {
                  System.out.println(Thread.currentThread().getName());
                  return s + " Alain";
                })
            .get());

    Future<String> completeExample = new SquareCalculator().calculateAsync();
    System.out.println(completeExample.get());

    CompletableFuture<String> completedExample =
        CompletableFuture.completedFuture("Value is completed");
    System.out.println(completedExample.get());

    CompletableFuture<String> firstFuture = CompletableFuture.supplyAsync(() -> "Example ");
    // Future<?>
    CompletableFuture<Void> secondFuture =
        firstFuture.thenAccept(s -> System.out.println(s + " 2"));
    secondFuture.get();

    CompletableFuture<String> futureExample3 =
        CompletableFuture.supplyAsync(() -> "Example ")
            .thenCompose(s -> CompletableFuture.supplyAsync(() -> s + " 3"));
    System.out.println(futureExample3.get());

    String name = null; // "Jesus";
    CompletableFuture<String> futureExample4 =
        CompletableFuture.supplyAsync(
                () -> {
                  if (name == null) {
                    throw new RuntimeException("Computation error!");
                  }
                  return "Hello, " + name;
                })
            .handle((s, t) -> s != null ? s : "Example 4");
    CompletableFuture<String> handleErrorFuture =
        futureExample4.handle((s, t) -> s != null ? s : "Example 4");

    System.out.println("Esperando a que se resuelva el error");
    System.out.println(futureExample4.get());
  }
}

class SquareCalculator {
  private ExecutorService executor = Executors.newCachedThreadPool();
  // Executors.newSingleThreadExecutor();
  // Executors.newFixedThreadPool(2);

  public Future<Integer> asyncSquare(Integer input) {
    return executor.submit(
        /*
        Esta es una implementación de una Interfaz Funcional
        new Callable<Integer>() {
            @Override
            public Integer call() throws Exception {
                System.out.println("Thread name " + Thread.currentThread().getName());
                Thread.sleep(2500);
                return input * input;
            }
        }
         */
        () -> {
          System.out.println("Thread name " + Thread.currentThread().getName());
          Thread.sleep(2500);
          return input * input;
        });
  }

  public Future<String> calculateAsync() throws InterruptedException {
    CompletableFuture<String> completableFuture = new CompletableFuture<>();

    Executors.newCachedThreadPool()
        .submit(
            () -> {
              Thread.sleep(500);
              // ...
              // Aqui hacemos operaciones muy complejas
              // ...
              completableFuture.complete("Manually completing a future");
              return null;
            });

    return completableFuture;
  }
}
