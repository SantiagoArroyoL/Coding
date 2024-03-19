package unam.ciencias.computoconcurrente;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.Random;
import org.junit.jupiter.api.Test;

class PolynomialAdditionTest {

  @Test
  void addDegreeZero() {
    Polynomial p = new Polynomial(new int[] {7});
    Polynomial q = new Polynomial(new int[] {3});

    Polynomial expectedResult = new Polynomial(new int[] {10});

    assertEquals(expectedResult, Polynomial.add(p, q));
  }

  @Test
  void addDegreeOne() {
    Polynomial p = new Polynomial(new int[] {7, 11});
    Polynomial q = new Polynomial(new int[] {3, 5});

    Polynomial expectedResult = new Polynomial(new int[] {10, 16});

    assertEquals(expectedResult, Polynomial.add(p, q));
  }

  @Test
  void addDegreeTwo() {
    Polynomial p = new Polynomial(new int[] {7, 11, 9});
    Polynomial q = new Polynomial(new int[] {3, 5, 2});

    Polynomial expectedResult = new Polynomial(new int[] {10, 16, 11});

    assertEquals(expectedResult, Polynomial.add(p, q));
  }

  @Test
  void addDegreeThree() {
    Polynomial p = new Polynomial(new int[] {7, 11, 9, 4});
    Polynomial q = new Polynomial(new int[] {3, 5, 2, 0});

    Polynomial expectedResult = new Polynomial(new int[] {10, 16, 11, 4});

    assertEquals(expectedResult, Polynomial.add(p, q));
  }

  @Test
  void addHuge() {
    final int ARRAY_SIZE = 1000000;
    final int MAX_VALUE = 1000;
    Random rand = new Random();
    int[] polyA = new int[ARRAY_SIZE];
    int[] polyB = new int[ARRAY_SIZE];
    int[] polyC = new int[ARRAY_SIZE];
    for (int i = 0; i < polyA.length; i++) {
      polyA[i] = rand.nextInt(MAX_VALUE);
      polyB[i] = rand.nextInt(MAX_VALUE);
      polyC[i] = polyA[i] + polyB[i];
    }
    Polynomial polynomialA = new Polynomial(polyA);
    Polynomial polynomialB = new Polynomial(polyB);
    Polynomial expectedResult = new Polynomial(polyC);
    assertEquals(expectedResult, Polynomial.add(polynomialA, polynomialB));
  }
}
