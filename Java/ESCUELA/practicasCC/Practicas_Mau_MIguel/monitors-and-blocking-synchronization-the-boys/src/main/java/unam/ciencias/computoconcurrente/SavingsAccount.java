package unam.ciencias.computoconcurrente;

import java.math.BigDecimal;

public interface SavingsAccount {
  void deposit(BigDecimal amount);
  void withdraw(BigDecimal amount);
  void withdrawWithPreference(BigDecimal amount);
  void transfer(BigDecimal amount, SavingsAccount srcAccount);
  BigDecimal getBalance();
}
