package unam.ciencias.computoconcurrente;

import lombok.Data;
import lombok.Getter;

@Data
@Getter
public abstract class Semaphore {

  protected ThreadID threadID = new ThreadID();

  public abstract void down();

  public abstract void up();
}
