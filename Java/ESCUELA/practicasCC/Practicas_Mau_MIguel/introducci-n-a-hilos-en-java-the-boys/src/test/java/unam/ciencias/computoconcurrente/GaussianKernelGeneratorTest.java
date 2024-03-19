package unam.ciencias.computoconcurrente;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.*;
import static unam.ciencias.computoconcurrente.MatrixComparator.*;

import org.junit.jupiter.api.Test;

class GaussianKernelGeneratorTest {
  GaussianKernelGenerator generator;
  final float EPSILON = 0.0001f;
  final MatrixParser<Float> parser = new MatrixParser<>();
  private static final String DIR = "gaussian_kernel/";

  @Test
  void testRadiusOne() {
    testGaussianKernelCase(1, "radiusOne.txt");
  }

  @Test
  void testRadiusTwo() {
    testGaussianKernelCase(2, "radiusTwo.txt");
  }

  @Test
  void testRadiusFour() {
    testGaussianKernelCase(4, "radiusFour.txt");
  }

  @Test
  void testRadiusSix() {
    testGaussianKernelCase(6, "radiusSix.txt");
  }

  @Test
  void testRadiusTen() {
    testGaussianKernelCase(10, "radiusTen.txt");
  }

  void testGaussianKernelCase(int radius, String name) {
    generator = new GaussianKernelGenerator(radius, (float) Math.sqrt(3));

    Matrix<Float> kernel = generator.build();
    Matrix<Float> expectedKernel = parser.parse(DIR + name, Float::valueOf);

    assertThat(kernel.getRows(), is(equalTo(expectedKernel.getRows())));
    assertThat(kernel.getColumns(), is(equalTo(expectedKernel.getColumns())));
    assertThat(areSimilar(kernel, expectedKernel, EPSILON), is(true));

    double kernelWeight = kernel.reduce(0f, (r, c, acc, val) -> acc + val);
    assertThat(kernelWeight, is(closeTo(1.0, EPSILON)));
  }
}
