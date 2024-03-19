package unam.ciencias.computoconcurrente;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;

import java.util.Arrays;
import java.util.Random;
import org.junit.jupiter.api.Test;

class SortingTest {

  @Test
  void sortEmptyArray() {
    int[] input = new int[0];
    int[] expectedOutput = new int[0];
    Sorting.mergeSort(input);
    assertArrayEquals(expectedOutput, input);
  }

  @Test
  void sortSingleElementArray() {
    int[] input = new int[] {1};
    int[] expectedOutput = new int[] {1};
    Sorting.mergeSort(input);
    assertArrayEquals(expectedOutput, input);
  }

  @Test
  void sortTwoElementsArray() {
    int[] input = new int[] {7, 1};
    int[] expectedOutput = new int[] {1, 7};
    Sorting.mergeSort(input);
    assertArrayEquals(expectedOutput, input);
  }

  @Test
  void sortThreeElementsArray() {
    int[] input = new int[] {7, 1, 5};
    int[] expectedOutput = new int[] {1, 5, 7};
    Sorting.mergeSort(input);
    assertArrayEquals(expectedOutput, input);
  }

  @Test
  void sortFourElementsArray() {
    int[] input = new int[] {7, 1, 5, 0};
    int[] expectedOutput = new int[] {0, 1, 5, 7};
    Sorting.mergeSort(input);
    assertArrayEquals(expectedOutput, input);
  }

  @Test
  void sortHugeArray() {
    Random rand = new Random();
    int[] input = new int[1000000];
    for (int i = 0; i < input.length; i++) {
      input[i] = rand.nextInt(1000);
    }
    int[] expectedOutput = input.clone();
    Arrays.sort(expectedOutput);
    Sorting.mergeSort(input);
    assertArrayEquals(expectedOutput, input);
  }
}
