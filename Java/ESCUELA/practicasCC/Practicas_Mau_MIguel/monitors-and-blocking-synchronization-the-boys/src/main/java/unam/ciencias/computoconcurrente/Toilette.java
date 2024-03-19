package unam.ciencias.computoconcurrente;

import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class Toilette {
  private volatile long timesMalesEntered;
  private volatile long timesFemalesEntered;

  private volatile long males;
  private volatile long females;


  public Toilette() {
    this.timesMalesEntered = 0;
    this.timesFemalesEntered = 0;
  }

  public void enterMale() throws InterruptedException {
    males++;
    timesMalesEntered++;
  }

  public void leaveMale() {
    males--;
  }

  public void enterFemale() throws InterruptedException {
    females++;
    timesFemalesEntered++;
  }

  public void leaveFemale() {
    females--;
  }

  public long getTimesMalesEntered() {
    return timesMalesEntered;
  }

  public long getTimesFemalesEntered() {
    return timesFemalesEntered;
  }

  public long getMales() {
    return males;
  }

  public long getFemales() {
    return females;
  }
}
