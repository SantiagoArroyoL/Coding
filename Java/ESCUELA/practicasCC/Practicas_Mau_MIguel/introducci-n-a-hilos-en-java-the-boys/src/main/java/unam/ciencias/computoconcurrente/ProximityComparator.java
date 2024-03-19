package unam.ciencias.computoconcurrente;

public interface ProximityComparator<T> {
  boolean test(T a, T b, float epsilon);
}
