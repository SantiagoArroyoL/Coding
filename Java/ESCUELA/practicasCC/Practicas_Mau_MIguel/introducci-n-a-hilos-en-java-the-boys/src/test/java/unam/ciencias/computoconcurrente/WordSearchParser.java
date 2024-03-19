package unam.ciencias.computoconcurrente;

import java.io.IOException;
import java.util.List;
import java.util.Scanner;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class WordSearchParser {

  private static final String DIR = "word_search/";

  public static char[][] loadBoardFromFile(String filename) {
    try (Stream<String> lines = LineReader.getLinesFromResourceFile(DIR + filename)) {
      List<String> rows = lines.collect(Collectors.toList());
      char[][] board = new char[rows.size()][];
      int rowNum = 0;
      for (String row : rows) {
        board[rowNum++] = row.toCharArray();
      }
      return board;
    } catch (IOException ioException) {
      throw new RuntimeException(ioException);
    }
  }

  public static List<String> loadWordsFromFile(String filename) {
    try (Stream<String> lines = LineReader.getLinesFromResourceFile(DIR + filename)) {
      return lines.collect(Collectors.toList());
    } catch (IOException ioException) {
      throw new RuntimeException(ioException);
    }
  }

  public static List<WordSearchAnswer> loadsAnswersFromFile(String filename) {
    try (Stream<String> lines = LineReader.getLinesFromResourceFile(DIR + filename)) {
      return lines
          .map(
              line -> {
                Scanner scanner = new Scanner(line);
                WordSearchAnswer answer = new WordSearchAnswer();
                answer.setWord(scanner.next());
                answer.setRow(scanner.nextInt());
                answer.setColumn(scanner.nextInt());
                answer.setDirection(scanner.next());
                return answer;
              })
          .collect(Collectors.toList());
    } catch (IOException ioException) {
      throw new RuntimeException(ioException);
    }
  }
}
