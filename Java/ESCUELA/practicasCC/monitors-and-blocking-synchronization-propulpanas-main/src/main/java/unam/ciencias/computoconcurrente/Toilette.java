package unam.ciencias.computoconcurrente;


public class Toilette {
  private ThreadLocal<Long> myTurn;

  private volatile long timesMalesEntered;
  private volatile long timesFemalesEntered;

  private volatile long males;
  private volatile long females;

  public Toilette() {
    this.timesMalesEntered = 0;
    this.timesFemalesEntered = 0;
    this.males = 0;
    this.females = 0;
  }

  /**
   * This function should be called only by male agents. Must enter the toilette if it is free or if
   * only males are using it and no female is waiting to enter. If there are females using the
   * bathroom it should wait a bounded amount of time to enter the toilette.
   */
  public void enterMale() throws InterruptedException {}

  public void leaveMale() {}

  /**
   * This function should be called only by female agents. Must enter the toilette if it is free or
   * if only females are using it and no male is waiting to enter. If there are males using the
   * bathroom it should wait a bounded amount of time to enter the toilette.
   */
  public void enterFemale() throws InterruptedException {}

  public void leaveFemale() {}

  /** Returns the total count any male has entered the bathroom */
  public long getTimesMalesEntered() {
    return timesMalesEntered;
  }

  /** Returns the total count any female has entered the bathroom */
  public long getTimesFemalesEntered() {
    return timesFemalesEntered;
  }

  /** Returns the current number of males using the bathroom */
  public long getMales() {
    return males;
  }

  /** Returns the current number of females using the bathroom */
  public long getFemales() {
    return females;
  }
}
