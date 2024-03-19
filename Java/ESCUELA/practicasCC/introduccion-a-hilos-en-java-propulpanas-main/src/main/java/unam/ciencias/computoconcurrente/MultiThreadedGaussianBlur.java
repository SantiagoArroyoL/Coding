package unam.ciencias.computoconcurrente;

public class MultiThreadedGaussianBlur extends MultiThreadedOperation
    implements ImageProcessingAlgorithm {

  GaussianKernelGenerator gaussianKernelGen;
  Matrix<Float> kernel;
  MultiThreadedMatrixConvolution convolution;

  public MultiThreadedGaussianBlur() {
    this(1, 1);
  }

  public MultiThreadedGaussianBlur(Integer threads, Integer radius) {
    super(threads);
    this.gaussianKernelGen =
        new GaussianKernelGenerator(radius, (float) Math.sqrt(2.0 * radius + 1));
    this.kernel = this.gaussianKernelGen.build();
    convolution = new MultiThreadedMatrixConvolution(threads);
  }

  @Override
  public Image process(Image image) throws InterruptedException {
    Image result = convolution.convolve(image, this.kernel);
    return result;
  }
}
