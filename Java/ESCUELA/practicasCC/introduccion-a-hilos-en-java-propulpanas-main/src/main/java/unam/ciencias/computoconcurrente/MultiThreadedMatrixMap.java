package unam.ciencias.computoconcurrente;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

public class MultiThreadedMatrixMap extends MultiThreadedOperation implements MatrixMap {

  public MultiThreadedMatrixMap() {
    super();
  }

  public MultiThreadedMatrixMap(int threads) {
    super(threads);
  }

  @Override
  public <I, E> Matrix<E> map(Matrix<I> matrix, Function<I, E> function)
      throws InterruptedException {
    Matrix<E> result = new Matrix<>(matrix.getRows(), matrix.getColumns());
    List<Thread> threadList = new ArrayList<>(this.threads);
    for (int i = 0; i < threads; i++) {
      int threadId = i;
      threadList.add(new Thread(() -> taskMap(threadId, function, matrix, result)));
    }
    this.runAndWaitForThreads(threadList);
    return result;
  }

  private <I, E> void taskMap(
      int threadId, Function<I, E> function, Matrix<I> input, Matrix<E> output) {
    for (int i = threadId; i < input.getRows(); i += this.threads) {
      for (int j = 0; j < input.getColumns(); j++) {
        output.setValue(i, j, function.apply(input.getValue(i, j)));
      }
    }
  }
}
