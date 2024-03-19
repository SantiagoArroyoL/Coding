package unam.ciencias.computoconcurrente;

import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.greaterThan;
import static org.hamcrest.Matchers.lessThan;

import java.util.Random;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

public class PoliceThiefGameSimulationTest {
  final int SIMULATIONS = 10;
  final int DURATION_IN_MS = 500;
  int PASSWORD_UPPER_BOUND;

  @Test
  @Timeout(DURATION_IN_MS * SIMULATIONS)
  void runSimulations() throws InterruptedException {
    calibrateMaxPassword();
    Random random = new Random();
    int policeWinCount = 0;
    for (int i = 0; i < SIMULATIONS; i++) {
      int currentPassword = random.ints(0, PASSWORD_UPPER_BOUND).findFirst().getAsInt();
      // Starting simulation " + i
      PoliceThiefGameSimulation simulation =
          new PoliceThiefGameSimulation(currentPassword, PASSWORD_UPPER_BOUND, DURATION_IN_MS);
      PoliceThiefGameWinner winner = simulation.runSimulation();
      if (winner == PoliceThiefGameWinner.POLICE) {
        // Police caught the thieves
        policeWinCount++;
      }
    }

    System.out.println("Simulations ended. Police wins " + policeWinCount + "/" + SIMULATIONS);

    assertThat(policeWinCount, is(greaterThan(0)));
    assertThat(policeWinCount, is(lessThan(SIMULATIONS)));
  }

  private void calibrateMaxPassword() throws InterruptedException {
    Thread t = new Thread(this::runDuration);
    t.start();
    Thread.sleep(DURATION_IN_MS);
    t.interrupt();
    t.join();
    System.out.println("PASSWORD_UPPER_BOUND: " + PASSWORD_UPPER_BOUND);
  }

  void runDuration() {
    long currentTimestamp = System.currentTimeMillis();
    int opsCounter = 0;
    while (true) {
      opsCounter++;
      if ((System.currentTimeMillis() - currentTimestamp) % 100 == 0) {
        if (Thread.interrupted()) {
          PASSWORD_UPPER_BOUND = opsCounter / 2;
          return;
        }
      }
    }
  }
}
