package unam.ciencias.computoconcurrente;

import java.util.Arrays;
import java.util.Objects;
import java.util.concurrent.*;
import lombok.AllArgsConstructor;

public class Polynomial {
  int[] coefficients; // possibly shared by several polynomials int first; // index of my constant
  // coefficient
  int degree; // number of coefficients that are mine
  int first; // index of my constant coefficient

  public Polynomial(int degree) {
    coefficients = new int[degree + 1];
    this.degree = degree;
    first = 0;
  }

  public Polynomial(int[] coefficients) {
    this.coefficients = coefficients;
    this.first = 0;
    this.degree = coefficients.length - 1;
  }

  public Polynomial(int[] coefficients, int first, int degree) {
    this.coefficients = coefficients;
    this.first = first;
    this.degree = degree;
  }

  public int get(int index) {
    return coefficients[first + index];
  }

  public void set(int index, int value) {
    coefficients[first + index] = value;
  }

  public int getDegree() {
    return degree;
  }

  public Polynomial[] split() {
    Polynomial[] result = new Polynomial[2];
    int newDegree = degree / 2;
    result[0] = new Polynomial(coefficients, first, newDegree);
    result[1] =
        new Polynomial(coefficients, first + newDegree + 1, newDegree - (degree % 2 == 0 ? 1 : 0));
    return result;
  }

  public static Polynomial add(Polynomial p, Polynomial q) {
    Polynomial result = new Polynomial(p.getDegree());
    ForkJoinPool.commonPool().invoke(new PolynomialAdditionTask(p, q, result));
    return result;
  }

  public static Polynomial multiply(Polynomial p, Polynomial q) {
    int degree = p.getDegree() + q.getDegree();
    Polynomial result = new Polynomial(degree);
    ForkJoinPool.commonPool().invoke(new PolynomialMultiplicationTask(p, q, result, 1));
    return result;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    Polynomial that = (Polynomial) o;
    for (int i = 0; i <= this.getDegree(); i++) {
      if (this.get(i) != that.get(i)) {
        return false;
      }
    }
    return true;
  }

  @Override
  public int hashCode() {
    int result = Objects.hash(degree, first);
    result = 31 * result + Arrays.hashCode(coefficients);
    return result;
  }

  @Override
  public String toString() {
    StringBuilder stringBuilder = new StringBuilder();
    for (int i = 0; i <= this.getDegree(); i++) {
      if (stringBuilder.length() > 0) {
        stringBuilder.append(" + ");
      }
      stringBuilder.append(this.get(i)).append("x^").append(i);
    }
    return "Polynomial{" + stringBuilder + "}";
  }
}

@AllArgsConstructor
class PolynomialAdditionTask extends RecursiveAction {
  static final int THRESHOLD = 1000;
  final Polynomial p;
  final Polynomial q;
  final Polynomial result;

  @Override
  protected void compute() {
    if (p.getDegree() <= THRESHOLD) {
      // Realizar la suma de manera secuencial en un solo hilo
      for (int i = 0; i <= p.getDegree(); i++) {
        int suma = p.get(i) + q.get(i);
        // System.out.println(p.get(i) + " + " + q.get(i) + " = " + suma);
        result.set(i, suma);
      }
    } else {
      // Dividir el polinomio y realizar la suma de manera recursiva en subtareas
      Polynomial[] pParts = p.split();
      Polynomial[] qParts = q.split();
      Polynomial[] resultParts = result.split();
      PolynomialAdditionTask task1 =
          new PolynomialAdditionTask(pParts[0], qParts[0], resultParts[0]);
      PolynomialAdditionTask task2 =
          new PolynomialAdditionTask(pParts[1], qParts[1], resultParts[1]);
      task1.fork();
      task2.compute();
      task1.join();
      //      invokeAll(task1,task2); Es lo mismo hacer
    }
  }
}

@AllArgsConstructor
class PolynomialMultiplicationTask extends RecursiveAction {
  static final int THRESHOLD = 50000; // DEBUG
  //  static final int THRESHOLD = 30; //REAL
  //  static final int THRESHOLD = 2; //DEBUG
  private final Polynomial p;
  private final Polynomial q;
  private final Polynomial result;
  private final int n; // numThreads

  @Override
  protected void compute() {
    if (p.getDegree() <= THRESHOLD) {
      System.out.println();
      // Realizar la multiplicación de manera secuencial en un solo hilo
      int c = ThreadID.get();
      //      for (int i = 0; i <= p.getDegree(); i++) {
      //      System.out.println("Hilo: " + c + " dato " + p.get(i));
      //      }
      for (int i = 0; i <= p.getDegree(); i++) {
        for (int j = 0; j <= q.getDegree(); j++) {
          int product = p.get(i) * q.get(j);
          int term = result.get(c + j);
          //          System.out.println("prod["+c+"+"+j+"] = " + p.get(i) + " * " + q.get(j) + " +
          // " + result.get(c+j));
          result.set(c + j, term + product);
          //          System.out.println(ThreadID.get());
        }
        c += n != 0 ? n : 1; // diferenciar entre secuencial neto o paralelo
      }
    } else {
      // Dividir el polinomio y realizar la multiplicación de manera recursiva en subtareas
      Polynomial[] pParts = p.split();

      PolynomialMultiplicationTask task1 =
          new PolynomialMultiplicationTask(pParts[0], q, result, n + 2);
      PolynomialMultiplicationTask task2 =
          new PolynomialMultiplicationTask(pParts[1], q, result, n + 2);
      invokeAll(task1, task2);
    }
  }
}
