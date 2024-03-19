package unam.ciencias.computoconcurrente;

import java.util.ArrayList;
import java.util.List;

public class MultiThreadedWordSearch extends MultiThreadedOperation implements WordSearch {

  public MultiThreadedWordSearch() {
    this(1);
  }

  public MultiThreadedWordSearch(int threads) {
    super(threads);
  }

  @Override
  public List<WordSearchAnswer> solve(char[][] board, List<String> words)
      throws InterruptedException {
    return new ArrayList<>();
  }
}
