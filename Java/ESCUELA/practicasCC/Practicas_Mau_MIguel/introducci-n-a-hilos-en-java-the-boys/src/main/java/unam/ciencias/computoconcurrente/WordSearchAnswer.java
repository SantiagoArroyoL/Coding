package unam.ciencias.computoconcurrente;

import lombok.AllArgsConstructor;
import lombok.EqualsAndHashCode;
import lombok.Getter;
import lombok.NoArgsConstructor;
import lombok.Setter;

@Getter
@Setter
@EqualsAndHashCode
@NoArgsConstructor
@AllArgsConstructor
public class WordSearchAnswer implements Comparable<WordSearchAnswer> {
  private String word;
  private int row;
  private int column;
  private String direction;

  @Override
  public int compareTo(WordSearchAnswer o) {
    int diff = this.word.compareTo(o.word);
    if (diff == 0) {
      return this.row == o.row ? this.column - o.column : this.row - o.row;
    }
    return diff;
  }
}
