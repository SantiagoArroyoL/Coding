package unam.ciencias.computoconcurrente;

import static org.hamcrest.MatcherAssert.*;
import static org.hamcrest.CoreMatchers.*;
import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.concurrent.ThreadLocalRandom;

public class SavingsAccountTest {

  SavingsAccount savingsAccount;

  boolean stateIsValid;

  List<BigDecimal> producedDeposits;
  List<BigDecimal> producedWithdrawals;
  List<BigDecimal> producedWithdrawalsWithPreference;

  BigDecimal lastPendingWithdrawal;
  BigDecimal lastPendingWithdrawalWithPref;

  @Test
  void testSequentialBehaviour() throws InterruptedException {
    savingsAccount = new SavingAccountsImpl();
    stateIsValid = true;
    producedDeposits = new ArrayList<>();
    producedWithdrawals = new ArrayList<>();
    producedWithdrawalsWithPreference = new ArrayList<>();

    Thread verifier = new Thread(this::verify, "Verifier");
    verifier.setDaemon(true);

    Thread producer = new Thread(() -> produce(1000), "Producer");
    Thread consumer = new Thread(() -> consume(1000), "Consumer");
    Thread consumerWithPreference = new Thread(() -> consumeWithPref(700), "ConsumerWithPreference");

    verifier.start();
    consumer.start();
    consumerWithPreference.start();
    producer.start();

    producer.join();
    consumerWithPreference.join(1000);
    consumer.join(1000);

    if (consumer.isAlive()) {
      consumer.interrupt();
    }

    if (consumerWithPreference.isAlive()) {
      consumerWithPreference.interrupt();
    }

    assertThat(stateIsValid, is(true));

    BigDecimal totalDeposits = producedDeposits.stream()
      .reduce(BigDecimal.ZERO, BigDecimal::add);

    BigDecimal totalWithdrawals = producedWithdrawals.stream()
      .reduce(BigDecimal.ZERO, BigDecimal::add);

    BigDecimal totalWithdrawalsWithPref = producedWithdrawalsWithPreference.stream()
      .reduce(BigDecimal.ZERO, BigDecimal::add);

    System.out.println("\nTotal deposits: " + totalDeposits + ". Deposit count: " + producedDeposits.size());
    System.out.println("\nTotal withdrawals " + totalWithdrawals + ". Withdrawals count: " + producedWithdrawals.size());
    System.out.println("\nTotal withdrawals with pref " + totalWithdrawalsWithPref + ". Withdrawals count: " + producedWithdrawalsWithPreference.size());

    assertThat(savingsAccount.getBalance(), is(equalTo(totalDeposits.subtract(totalWithdrawalsWithPref).subtract(totalWithdrawals))));
    if (Objects.nonNull(lastPendingWithdrawalWithPref)) {
      System.out.println("Last pending withdrawal with pref: " + lastPendingWithdrawalWithPref);
      System.out.println("Current balance: " + savingsAccount.getBalance());
      assertThat(lastPendingWithdrawalWithPref.compareTo(savingsAccount.getBalance()) > 0, is(true));
    } else if (Objects.nonNull(lastPendingWithdrawal)) {
      System.out.println("Last pending withdrawal: " + lastPendingWithdrawal);
      System.out.println("Current balance: " + savingsAccount.getBalance());
      assertThat(lastPendingWithdrawal.compareTo(savingsAccount.getBalance()) > 0, is(true));
    }
  }

  void produce(int deposits) {
    for (int i = 0; i < deposits; i++) {
      sleepRandomTime(10);
      BigDecimal newDeposit = BigDecimal.valueOf(
        Math.abs(
          ThreadLocalRandom.current().nextInt() % 1000
        )
      );
      savingsAccount.deposit(newDeposit);
      producedDeposits.add(newDeposit);
    }
  }

  void consume(int withdrawals) {
    try {
      consumeAux(withdrawals);
    } catch (RuntimeException re) {
      System.out.println(Thread.currentThread().getName() + " stopped by interruption: " + re.getMessage());
    }
  }

  void consumeAux(int withdrawals) {
    for (int i = 0; i < withdrawals; i++) {
      BigDecimal newWithdrawal = BigDecimal.valueOf(
        Math.abs(
          ThreadLocalRandom.current().nextInt() % 1000
        )
      );
      lastPendingWithdrawal = newWithdrawal;
      savingsAccount.withdraw(newWithdrawal);
      producedWithdrawals.add(newWithdrawal);
      lastPendingWithdrawal = null;
      sleepRandomTime(10);
    }
  }

  void consumeWithPref(int withdrawals) {
    try {
      consumeWithPrefAux(withdrawals);
    } catch (RuntimeException re) {
      System.out.println(Thread.currentThread().getName() + " stopped by interruption: " + re.getMessage());
    }
  }

  void consumeWithPrefAux(int withdrawals) {
    for (int i = 0; i < withdrawals; i++) {
      BigDecimal newWithdrawal = BigDecimal.valueOf(
        Math.abs(
          ThreadLocalRandom.current().nextInt() % 1000
        )
      );
      lastPendingWithdrawalWithPref = newWithdrawal;
      savingsAccount.withdrawWithPreference(newWithdrawal);
      producedWithdrawalsWithPreference.add(newWithdrawal);
      lastPendingWithdrawalWithPref = null;
      sleepRandomTime(10);
    }
  }

  void verify() {
    while (stateIsValid) {
      stateIsValid = stateIsValid
        && savingsAccount.getBalance().compareTo(BigDecimal.ZERO) >= 0;
      sleepRandomTime(5);
    }
  }

  void sleepRandomTime(int limit) {
    try {
      Thread.sleep(Math.abs(ThreadLocalRandom.current().nextInt() % limit));
    } catch (InterruptedException e) {
      throw new RuntimeException(e);
    }
  }
}
