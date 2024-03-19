package unam.ciencias.computoconcurrente;

public interface MatrixConvolution {
  Image convolve(Image image, Matrix<Float> kernel) throws InterruptedException;
}
