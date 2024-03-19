package unam.ciencias.computoconcurrente;

import lombok.Getter;
import lombok.RequiredArgsConstructor;
import lombok.Setter;

@Getter
@Setter
@RequiredArgsConstructor
public class VolatileField<T> {
  private volatile T value;

  public VolatileField(T value) {
    this.value = value;
  }
}
