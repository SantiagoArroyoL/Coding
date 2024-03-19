package unam.ciencias.computoconcurrente;

import java.util.concurrent.CompletableFuture;

public class ArraySum {

  private static final int THRESHOLD = 500;

  private ArraySum() {}

  public static int sum(int[] numbers) {
    return sumAsync(numbers, 0, numbers.length).join();
  }

  private static CompletableFuture<Integer> sumAsync(int[] numbers, int index, int length) {
    if (length <= THRESHOLD) {
      // Suma secuencial
      return CompletableFuture.completedFuture(sumaSecuencial(numbers, index, length));
    } else {
      // Dividir el arreglo
      int mid = index + length / 2;
      CompletableFuture<Integer> f1 =
          CompletableFuture.supplyAsync(
              () -> {
                return sumaSecuencial(numbers, index, mid - index);
              });

      return f1.thenApplyAsync(
          s -> {
            return s + sumaSecuencial(numbers, mid, length - (mid - index));
          });
    }
  }

  private static int sumaSecuencial(int[] numbers, int index, int length) {
    int sum = 0;
    for (int i = index; i < index + length; i++) {
      sum += numbers[i];
    }
    return sum;
  }
}
