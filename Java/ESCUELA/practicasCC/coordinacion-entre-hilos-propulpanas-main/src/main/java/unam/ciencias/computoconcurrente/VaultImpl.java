package unam.ciencias.computoconcurrente;

public class VaultImpl implements Vault {
  private int password;
  private boolean passwordFound;
  private Lock lock;

  public VaultImpl(int password, Lock lock) {
    this.password = password;
    System.out.println("PASSWORD:" + password);
    this.passwordFound = false;
    this.lock = lock;
  }

  public boolean isPassword(int guess) {
    if (guess == this.password) {
      this.passwordFound = true;
      lock.lock();
      return true;
    }
    return false;
  }

  public boolean isPasswordFound() {
    return passwordFound;
  }
}
