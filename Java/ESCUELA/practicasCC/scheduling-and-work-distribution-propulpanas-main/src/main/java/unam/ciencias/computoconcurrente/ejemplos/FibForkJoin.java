package unam.ciencias.computoconcurrente.ejemplos;

import java.util.concurrent.RecursiveTask;

public class FibForkJoin extends RecursiveTask<Integer> {

  int arg;

  public FibForkJoin(int n) {
    arg = n;
  }

  public Integer compute() {
    try {
      if (arg > 1) {
        FibForkJoin rightTask = new FibForkJoin(arg - 1);
        rightTask.fork();
        FibForkJoin leftTask = new FibForkJoin(arg - 2);
        leftTask.fork();
        return rightTask.join() + leftTask.join(); // + leftTask.compute();
      } else {
        return 1;
      }
    } catch (Exception ex) {
      ex.printStackTrace();
      return 1;
    }
  }
}
