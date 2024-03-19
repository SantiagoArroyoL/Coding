package unam.ciencias.computoconcurrente;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.List;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

@EnabledIf("testSuiteEnabled")
class WordSearchTest {

  static boolean testSuiteEnabled() {
    return PropertiesLoader.getBooleanProperty("word-search.enabled");
  }

  @Test
  void exampleSingleThreaded() throws InterruptedException {
    WordSearch wordSearch = new MultiThreadedWordSearch();
    exampleTestCase(wordSearch);
  }

  void exampleTestCase(WordSearch wordSearch) throws InterruptedException {
    executeTestCase(wordSearch, "exampleBoard.txt", "exampleWords.txt", "exampleAnswers.txt");
  }

  @Test
  void boardOneSingleThreaded() throws InterruptedException {
    WordSearch wordSearch = new MultiThreadedWordSearch();
    boardOneTestCase(wordSearch);
  }

  @Test
  void boardOneTwoThreaded() throws InterruptedException {
    WordSearch wordSearch = new MultiThreadedWordSearch(2);
    boardOneTestCase(wordSearch);
  }

  @Test
  void boardOneFourThreaded() throws InterruptedException {
    WordSearch wordSearch = new MultiThreadedWordSearch(4);
    boardOneTestCase(wordSearch);
  }

  @Test
  void boardOneEightThreaded() throws InterruptedException {
    WordSearch wordSearch = new MultiThreadedWordSearch(8);
    boardOneTestCase(wordSearch);
  }

  void boardOneTestCase(WordSearch wordSearch) throws InterruptedException {
    executeTestCase(wordSearch, "board1.txt", "words1.txt", "answers1.txt");
  }

  @Test
  void boardTwoSingleThreaded() throws InterruptedException {
    WordSearch wordSearch = new MultiThreadedWordSearch();
    boardOneTestCase(wordSearch);
  }

  @Test
  void boardTwoTwoThreaded() throws InterruptedException {
    WordSearch wordSearch = new MultiThreadedWordSearch(2);
    boardTwoTestCase(wordSearch);
  }

  @Test
  void boardTwoFourThreaded() throws InterruptedException {
    WordSearch wordSearch = new MultiThreadedWordSearch(4);
    boardTwoTestCase(wordSearch);
  }

  @Test
  void boardTwoEightThreaded() throws InterruptedException {
    WordSearch wordSearch = new MultiThreadedWordSearch(8);
    boardTwoTestCase(wordSearch);
  }

  void boardTwoTestCase(WordSearch wordSearch) throws InterruptedException {
    executeTestCase(wordSearch, "board2.txt", "words2.txt", "answers2.txt");
  }

  @Test
  void boardThreeSingleThreaded() throws InterruptedException {
    WordSearch wordSearch = new MultiThreadedWordSearch();
    boardThreeTestCase(wordSearch);
  }

  @Test
  void boardThreeTwoThreaded() throws InterruptedException {
    WordSearch wordSearch = new MultiThreadedWordSearch(2);
    boardThreeTestCase(wordSearch);
  }

  @Test
  void boardThreeFourThreaded() throws InterruptedException {
    WordSearch wordSearch = new MultiThreadedWordSearch(4);
    boardThreeTestCase(wordSearch);
  }

  @Test
  void boardThreeEightThreaded() throws InterruptedException {
    WordSearch wordSearch = new MultiThreadedWordSearch(8);
    boardThreeTestCase(wordSearch);
  }

  void boardThreeTestCase(WordSearch wordSearch) throws InterruptedException {
    executeTestCase(wordSearch, "board3.txt", "words3.txt", "answers3.txt");
  }

  void executeTestCase(
      WordSearch wordSearch, String boardFile, String wordsFile, String answersFiles)
      throws InterruptedException {
    char[][] board = WordSearchParser.loadBoardFromFile(boardFile);
    List<String> words = WordSearchParser.loadWordsFromFile(wordsFile);
    List<WordSearchAnswer> expectedSearchResults =
        WordSearchParser.loadsAnswersFromFile(answersFiles);
    assertEquals(expectedSearchResults, wordSearch.solve(board, words));
  }
}
