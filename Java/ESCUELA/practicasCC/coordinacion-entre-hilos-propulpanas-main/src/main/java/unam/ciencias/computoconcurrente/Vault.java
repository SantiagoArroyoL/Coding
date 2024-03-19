package unam.ciencias.computoconcurrente;

public interface Vault {
  boolean isPassword(int guess);

  boolean isPasswordFound();
}
