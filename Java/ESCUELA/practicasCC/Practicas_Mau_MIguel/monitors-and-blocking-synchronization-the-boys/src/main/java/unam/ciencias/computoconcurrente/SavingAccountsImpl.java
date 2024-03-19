package unam.ciencias.computoconcurrente;

import lombok.EqualsAndHashCode;
import lombok.ToString;

import java.math.BigDecimal;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

@EqualsAndHashCode
@ToString
public class SavingAccountsImpl implements SavingsAccount {
  private BigDecimal balance;
  private Lock balanceLock = new ReentrantLock();
  private Condition sufficientFundsCondition = balanceLock.newCondition();
  private Condition preferredWithdrawCondition = balanceLock.newCondition();
  private int preferredWithdrawalsPending = 0;

  public SavingAccountsImpl() {
    this(BigDecimal.ZERO);
  }

  public SavingAccountsImpl(BigDecimal initialBalance) {
    this.balance = initialBalance;
  }

  @Override
  public void deposit(BigDecimal amount) {
    balanceLock.lock();
    try {
      balance = balance.add(amount);
      sufficientFundsCondition.signalAll(); // Notify all threads waiting for funds.
      if (preferredWithdrawalsPending > 0) {
        preferredWithdrawCondition.signal(); // Notify one preferred withdrawal if any.
      }
    } finally {
      balanceLock.unlock();
    }
  }

  @Override
  public void withdraw(BigDecimal amount) {
    balanceLock.lock();
    try {
      while (balance.compareTo(amount) < 0 || preferredWithdrawalsPending > 0) {
        sufficientFundsCondition.await();
      }
      balance = balance.subtract(amount);
    } catch(InterruptedException ie){
      Thread.currentThread().interrupt();
    } finally {
      balanceLock.unlock();
    }
  }

  @Override
  public void withdrawWithPreference(BigDecimal amount) {
    balanceLock.lock();
    try {
      preferredWithdrawalsPending++;
      while (balance.compareTo(amount) < 0) {
        preferredWithdrawCondition.await();
      }
      balance = balance.subtract(amount);
      preferredWithdrawalsPending--;
      if (preferredWithdrawalsPending == 0) {
        sufficientFundsCondition.signalAll(); // Let ordinary withdrawals proceed if no preferred withdrawals are waiting.
      }
    } catch(InterruptedException ie) {
      Thread.currentThread().interrupt();
    } finally {
      balanceLock.unlock();
    }
  }

  @Override
  public void transfer(BigDecimal amount, SavingsAccount srcAccount) {
    // Lock ordering to prevent deadlocks
    Lock firstLock = balanceLock;
    Lock secondLock = ((SavingAccountsImpl) srcAccount).balanceLock;

    firstLock.lock();
    secondLock.lock();
    try {
      srcAccount.withdraw(amount);
      this.deposit(amount);
    } finally {
      secondLock.unlock();
      firstLock.unlock();
    }
  }

  @Override
  public BigDecimal getBalance() {
    balanceLock.lock();
    try {
      return balance;
    } finally {
      balanceLock.unlock();
    }
  }
}
