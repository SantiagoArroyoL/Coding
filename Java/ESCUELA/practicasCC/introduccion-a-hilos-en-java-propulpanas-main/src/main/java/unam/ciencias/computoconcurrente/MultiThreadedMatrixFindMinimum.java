package unam.ciencias.computoconcurrente;

import java.util.ArrayList;
import java.util.List;
import java.util.NoSuchElementException;

public class MultiThreadedMatrixFindMinimum extends MultiThreadedOperation
    implements MatrixFindMinimum {

  public MultiThreadedMatrixFindMinimum() {
    super();
  }

  public MultiThreadedMatrixFindMinimum(int threads) {
    super(threads);
  }

  @Override
  public <N extends Comparable<N>> N findMinimum(Matrix<N> matrix) throws InterruptedException {
    List<N> minimums = new ArrayList<>(this.threads);
    List<Thread> threadList = new ArrayList<>(this.threads);
    for (int i = 0; i < this.threads; i++) {
      int threadId = i;
      minimums.add(null);
      /*
      Runnable runnable = new Runnable() {
          @Override
          public void run() {
              taskFindMinimum(finalI, matrix);
          }
      };
       */
      threadList.add(new Thread(() -> taskFindMinimum(threadId, minimums, matrix)));
    }
    this.runAndWaitForThreads(threadList);
    return minimums.stream().min(Comparable::compareTo).orElseThrow(NoSuchElementException::new);
  }

  private <N extends Comparable<N>> void taskFindMinimum(
      int threadId, List<N> minimums, Matrix<N> matrix) {
    N min = null;
    for (int i = threadId; i < matrix.getRows(); i += this.threads) {
      N rowMin =
          matrix.getRow(i).stream()
              .min(Comparable::compareTo)
              .orElseThrow(NoSuchElementException::new);
      if (min == null) {
        min = rowMin;
      } else {
        min = rowMin.compareTo(min) < 0 ? rowMin : min;
      }
    }
    minimums.set(threadId, min);
  }
}
