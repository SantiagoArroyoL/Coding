package unam.ciencias.computoconcurrente;

import java.util.ArrayList;
import java.util.List;

public class PoliceThiefGameSimulation {
  public final int THIEVES = 2;
  public final int VERIFICATIONS = 100;

  private List<Thief> thieves;
  private Vault vault;
  private int simulationDurationInMS;
  private Lock lock;
  private int passwordUpperBound;

  private List<Integer> threads = new ArrayList<>(THIEVES);

  public PoliceThiefGameSimulation(
          int password, int passwordUpperBound, int simulationDurationInMS) {
    this.lock = new PetersonLock();
    this.passwordUpperBound = passwordUpperBound;
    this.vault = new VaultImpl(password, this.lock);
    this.simulationDurationInMS = simulationDurationInMS;
  }

  public PoliceThiefGameWinner runSimulation() {
    thieves = new ArrayList<>(THIEVES);
    List<Thread> thievesThreads = new ArrayList<>(THIEVES);
    long start = System.currentTimeMillis();

    for (int i = 0; i < THIEVES; i++) {
      thieves.add(new ThiefImpl(vault, passwordUpperBound, i, THIEVES));
    }

    for (Thief t : thieves) {
      ThreadID.resetInitialThreadIDTo(0);
      Thread thief = new Thread(t::tryToFindPassword);
      thievesThreads.add(thief);
      threads.add((int) thief.getId());
    }

    Thread police = new Thread(this::getThieves);
    for (Thread t : thievesThreads) {
      t.start();
    }
    police.start();

    while (System.currentTimeMillis() - start < simulationDurationInMS) {
      if (vault.isPasswordFound()) return PoliceThiefGameWinner.THIEF;
      if (police.isInterrupted()) return PoliceThiefGameWinner.THIEF;
    }

    if (vault.isPasswordFound()) return PoliceThiefGameWinner.THIEF;
    return PoliceThiefGameWinner.POLICE;
  }

  public List<Thief> getThieves() {
    while (!vault.isPasswordFound() && !threads.isEmpty()) {
      try {
        for (int i = 0; i < VERIFICATIONS; i++)
          Thread.sleep(this.simulationDurationInMS / VERIFICATIONS);
      } catch (InterruptedException ie) {
        break;
      }
      System.out.println("Police caught thief: " + Thread.currentThread().getId());
      threads.remove(Thread.currentThread().getId());
      Thread.currentThread().interrupt();
    }
    return thieves;
  }
}
