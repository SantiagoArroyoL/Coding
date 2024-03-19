package unam.ciencias.computoconcurrente;

import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.RecursiveAction;
import lombok.AllArgsConstructor;

public class Sorting {
  private Sorting() {}

  public static void mergeSort(int[] array) {
    ForkJoinPool.commonPool().invoke(new MergeSortTask(array, 0, array.length - 1));
  }

  @AllArgsConstructor
  private static class MergeSortTask extends RecursiveAction {
    private static final int THRESHOLD = 500;
    int[] array;
    int startIndex;
    int endIndex;

    @Override
    protected void compute() {
      if (endIndex - startIndex <= THRESHOLD) {
        // Ordenar de manera secuencial si el tamaño es menor o igual al umbral
        mergeSortSecuencial();
      } else {
        // Dividir el arreglo en dos mitades y realizar la ordenación en paralelo
        int midIndex = (startIndex + endIndex) / 2;
        MergeSortTask leftTask = new MergeSortTask(array, startIndex, midIndex);
        MergeSortTask rightTask = new MergeSortTask(array, midIndex + 1, endIndex);
        invokeAll(leftTask, rightTask);

        // Combinar los resultados parciales
        merge(startIndex, midIndex, endIndex);
      }
    }

    private void mergeSortSecuencial() {
      // Implementación del merge sort secuencial
      if (startIndex < endIndex) {
        int midIndex = (startIndex + endIndex) / 2;
        MergeSortTask leftTask = new MergeSortTask(array, startIndex, midIndex);
        MergeSortTask rightTask = new MergeSortTask(array, midIndex + 1, endIndex);
        leftTask.compute();
        rightTask.compute();
        merge(startIndex, midIndex, endIndex);
      }
    }

    private void merge(int startIndex, int midIndex, int endIndex) {
      int[] tempArray = new int[endIndex - startIndex + 1];
      int leftIndex = startIndex;
      int rightIndex = midIndex + 1;
      int tempIndex = 0;

      while (leftIndex <= midIndex && rightIndex <= endIndex) {
        if (array[leftIndex] <= array[rightIndex]) {
          tempArray[tempIndex] = array[leftIndex];
          leftIndex++;
        } else {
          tempArray[tempIndex] = array[rightIndex];
          rightIndex++;
        }
        tempIndex++;
      }

      while (leftIndex <= midIndex) {
        tempArray[tempIndex] = array[leftIndex];
        leftIndex++;
        tempIndex++;
      }

      while (rightIndex <= endIndex) {
        tempArray[tempIndex] = array[rightIndex];
        rightIndex++;
        tempIndex++;
      }

      // Copiar los elementos del arreglo temporal de vuelta al arreglo original
      for (int i = 0; i < tempArray.length; i++) {
        array[startIndex + i] = tempArray[i];
      }
    }
  }
}
