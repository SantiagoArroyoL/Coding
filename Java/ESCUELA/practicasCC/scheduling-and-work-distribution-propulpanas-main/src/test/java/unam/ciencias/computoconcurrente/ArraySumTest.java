package unam.ciencias.computoconcurrente;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.is;
import static org.junit.jupiter.api.Assertions.*;

import java.util.Arrays;
import java.util.Random;
import org.junit.jupiter.api.Test;

class ArraySumTest {

  @Test
  void testEmpty() {
    int[] input = new int[0];
    int expectedResult = 0;
    assertThat(ArraySum.sum(input), is(expectedResult));
  }

  @Test
  void testSingleElement() {
    int[] input = new int[] {5};
    int expectedResult = 5;
    assertThat(ArraySum.sum(input), is(expectedResult));
  }

  @Test
  void testEvenLength() {
    int[] input = new int[] {5, 1, -8, 13};
    int expectedResult = 11;
    assertThat(ArraySum.sum(input), is(expectedResult));
  }

  @Test
  void testOddLength() {
    int[] input = new int[] {1, 7, 9, 3, 133};
    int expectedResult = 153;
    assertThat(ArraySum.sum(input), is(expectedResult));
  }

  @Test
  void testHuge() {
    Random rand = new Random();
    int[] input = new int[1000000];
    for (int i = 0; i < input.length; i++) {
      input[i] = rand.nextInt(1000);
    }
    int expectedResult = Arrays.stream(input).reduce(0, Integer::sum);
    assertEquals(expectedResult, ArraySum.sum(input));
  }
}
