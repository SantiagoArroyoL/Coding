package unam.ciencias.computoconcurrente;

import lombok.*;

@Getter
@Setter
@NoArgsConstructor
public class VolatileField<T> {
  private volatile T value;

  public VolatileField(T value) {
    this.value = value;
  }
}
