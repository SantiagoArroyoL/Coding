package unam.ciencias.computoconcurrente;

import java.util.Random;

public abstract class Participant implements Runnable {
  public static long MIN_SLEEP_TIME = 100;
  public static long MAX_SLEEP_TIME = 300;

  protected Toilette toilette;
  private Random random;
  private long timesEnteredTheToilette;

  public Participant(Toilette toilette) {
    this.toilette = toilette;
    this.random = new Random();
    this.timesEnteredTheToilette = 0;
  }

  public abstract void enterToilette() throws InterruptedException;

  public abstract void leaveToilette() throws InterruptedException;

  public void run() {
    try {
      System.out.printf(
          "%s.%s starting simulation\n", Thread.currentThread().getName(), getClass().getName());
      while (true) {
        enterToilette();
        doStuff();
        leaveToilette();
        sleepRandomTime();
      }
    } catch (InterruptedException ie) {
      System.out.printf(
          "%s.%s finishing simulation, used the toilette %d\n",
          Thread.currentThread().getName(), getClass().getName(), timesEnteredTheToilette);
    }
  }

  private void doStuff() throws InterruptedException {
    this.timesEnteredTheToilette++;
    sleepRandomTime();
  }

  private void sleepRandomTime() throws InterruptedException {
    long timeToSleep = Math.abs((MIN_SLEEP_TIME + random.nextInt()) % MAX_SLEEP_TIME);
    Thread.sleep(timeToSleep);
  }

  public long getTimesEnteredTheToilette() {
    return this.timesEnteredTheToilette;
  }
}
