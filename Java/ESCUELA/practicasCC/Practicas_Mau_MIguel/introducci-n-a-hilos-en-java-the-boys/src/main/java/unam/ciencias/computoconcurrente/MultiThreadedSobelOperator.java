package unam.ciencias.computoconcurrente;



public class MultiThreadedSobelOperator extends MultiThreadedOperation
    implements ImageProcessingAlgorithm {

  public MultiThreadedSobelOperator() {
    this(1);
  }

  public MultiThreadedSobelOperator(int threads) {
    super(threads);
    // TODO: implementación
  }

  @Override
  public Image process(Image image) throws InterruptedException {
    Matrix<Integer> result = new Matrix<>(0, 0);
    // TODO: implementación
    return new Image(result);
  }
}
