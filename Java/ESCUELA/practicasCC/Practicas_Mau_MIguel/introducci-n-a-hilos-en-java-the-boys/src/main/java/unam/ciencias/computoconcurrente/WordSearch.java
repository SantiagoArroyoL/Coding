package unam.ciencias.computoconcurrente;

import java.util.List;

public interface WordSearch {
  List<WordSearchAnswer> solve(char[][] board, List<String> words) throws InterruptedException;
}
