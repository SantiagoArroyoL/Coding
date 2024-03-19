package unam.ciencias.computoconcurrente;

import java.util.Random;

public class ThiefImpl implements Thief {
  private Vault vault;
  private Random random;
  private int guessUpperBound;

  private int participants;
  private int thiefId;
  private int tries;

  public ThiefImpl(Vault vault, int guessUpperBound, int thiefId, int participants) {
    this.vault = vault;
    this.random = new Random();
    this.guessUpperBound = guessUpperBound;
    this.thiefId = thiefId;
    this.participants = participants;
    this.tries = 0;
  }

  @Override
  public void tryToFindPassword() {
    while (!vault.isPasswordFound()) {
      int min = thiefId * (guessUpperBound / participants);
      int max = min + (guessUpperBound / participants);
      System.out.println("Thread: " + thiefId + " Min: " + min + " Max: " + max);
      int guess = this.random.ints(min, guessUpperBound).findFirst().getAsInt();
      //    int guess = this.getRandom(min, max);
      int police = random.nextInt(guessUpperBound);
      System.out.println("Intento del thread" + thiefId + ": " + guess);
      System.out.println("Police: " + police);
      if (vault.isPassword(guess)) {
        System.out.println("Thief " + thiefId + "found the password!");
      } else if (police == guess) {
        Thread.currentThread().interrupt(); // posibilidad extra ded que gane la police
      }
      System.out.println("INTENTO: " + tries);
      tries++;
    }
  }

  /**
   * Generamos un numero aleatorio en un rango particular
   *
   * @param min cota minima
   * @param max cota maxima
   * @return numero entero aleatorio
   */
  public int getRandom(int min, int max) {
    return random.nextInt(max - min) + min;
  }

  @Override
  public int getId() {
    return thiefId;
  }

  @Override
  public int getTries() {
    return this.tries;
  }

  @Override
  public String toString() {
    return "ThiefImpl{" + "thiefId=" + thiefId + ", tries=" + tries + '}';
  }
}
