package unam.ciencias.computoconcurrente;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.is;
import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.Random;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

@EnabledIf("testSuiteEnabled")
class PolynomialMultiplicationTest {

  static boolean testSuiteEnabled() {
    return PropertiesLoader.getBooleanProperty("polynomial-multiplication.enabled");
  }

  @Test
  void multiplyDegreeZero() {
    Polynomial p = new Polynomial(new int[] {7});
    Polynomial q = new Polynomial(new int[] {3});

    Polynomial expectedResult = new Polynomial(new int[] {21});

    assertEquals(expectedResult, Polynomial.multiply(p, q));
  }

  @Test
  void multiplyDegreeOne() {
    Polynomial p = new Polynomial(new int[] {7, 2});
    Polynomial q = new Polynomial(new int[] {3, 1});

    Polynomial expectedResult = new Polynomial(new int[] {21, 13, 2});

    assertEquals(expectedResult, Polynomial.multiply(p, q));
  }

  @Test
  void multiplyDegreeThree() {
    Polynomial p = new Polynomial(new int[] {7, 11, 9, 4});
    Polynomial q = new Polynomial(new int[] {3, 5, 2, 1});

    Polynomial expectedResult = new Polynomial(new int[] {21, 68, 96, 86, 49, 17, 4});

    assertEquals(expectedResult, Polynomial.multiply(p, q));
  }

  @Test
  void multiplyHugePolynomials() {
    Random rand = new Random();
    int degree = 5000;
    int[] pCoefficients = new int[degree + 1];
    int[] qCoefficients = new int[degree + 1];

    // Fill the coefficient arrays with random values
    for (int i = 0; i < pCoefficients.length; i++) {
      pCoefficients[i] = rand.nextInt(15);
      qCoefficients[i] = rand.nextInt(15);
    }

    Polynomial p = new Polynomial(pCoefficients);
    Polynomial q = new Polynomial(qCoefficients);

    // Compute the product of the two polynomials
    Polynomial product = Polynomial.multiply(p, q);

    // Check that the degree of the product is correct
    int expectedDegree = p.getDegree() + q.getDegree();
    assertThat(product.getDegree(), is(expectedDegree));

    // Check that the coefficient values are correct
    int[] expectedCoefficients = new int[expectedDegree + 1];
    for (int i = 0; i <= degree; i++) {
      for (int j = 0; j <= degree; j++) {
        expectedCoefficients[i + j] += pCoefficients[i] * qCoefficients[j];
      }
    }
    Polynomial expectedResult = new Polynomial(expectedCoefficients);
    assertThat(product, is(expectedResult));
  }
}
