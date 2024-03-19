package unam.ciencias.computoconcurrente;

public class GaussianKernelGenerator {
  int radius;
  float variance;

  public GaussianKernelGenerator(int radius, float variance) {
    this.radius = radius;
    this.variance = variance;
  }

  public Matrix<Float> build() {
    Matrix<Float> kernel = new Matrix<>(this.radius * 2 + 1, this.radius * 2 + 1);

    float sum = 0;

    for (int i = 0; i < kernel.getRows(); i++) {
      for (int j = 0; j < kernel.getColumns(); j++) {
        int x = Math.abs(i - radius);
        int y = Math.abs(j - radius);
        float val =
            ((float) (Math.exp(-(x * x + y * y) / (2 * variance * variance)))
                / (float) (2 * Math.PI * variance * variance));
        kernel.setValue(i, j, val);
        sum += val;
      }
    }

    for (int i = 0; i < kernel.getRows(); i++) {
      for (int j = 0; j < kernel.getColumns(); j++) {
        float curr = kernel.getValue(i, j);
        float n = curr / sum;
        kernel.setValue(i, j, n);
      }
    }

    return kernel;
  }
}
