package unam.ciencias.computoconcurrente.ejemplos;

import java.util.concurrent.CompletableFuture;
import java.util.concurrent.Future;
import java.util.function.Supplier;

public class FibTaskCP implements Supplier<Integer> {

  int arg;

  public FibTaskCP(int n) {
    arg = n;
  }

  public Integer get() {
    try {
      if (arg > 2) {
        Future<Integer> left = CompletableFuture.supplyAsync(new FibTaskCP(arg - 1));
        Future<Integer> right = CompletableFuture.supplyAsync(new FibTaskCP(arg - 2));
        // ....
        // ....
        return left.get() + right.get();
      } else {
        return 1;
      }
    } catch (Exception ex) {
      ex.printStackTrace();
      return 1;
    }
  }
}
