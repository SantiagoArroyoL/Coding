package alglin;

import static com.google.common.truth.Truth.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import java.util.Random;

public class PruebaMatriz {

    private static final int MAX_M = 8;
    private static final int MAX_N = 8;
    private static final int MIN_M = 2;
    private static final int MIN_N = 2;
    private static double TOLERANCE = 1.0e-3;
    private static Random rnd;
    private int m, n;
    private Matriz m1, m2, m3, m4;

    @BeforeAll
    public static void initRandom() {
        rnd = new Random();
    }

    @BeforeEach
    public void initDim() {
        m = n = 0;
        while (m == n) {
            m = MIN_M + rnd.nextInt(MAX_M - MIN_M + 1);
            n = MIN_N + rnd.nextInt(MAX_N - MIN_N + 1);
        }
        int p = m < n ? n : m;
        m1 = new Matriz(m, n);
        m2 = new Matriz(m, n);
        m3 = new Matriz(p, p);
        m4 = new Matriz(p, p);
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < n; j++) {
                m1.asignarEntrada(nextOneDecimalDouble(), i, j);
                m2.asignarEntrada(nextOneDecimalDouble(), i, j);
            }
        }
        for (int i = 0; i < p; i++) {
            for (int j = 0; j < p; j++) {
                m3.asignarEntrada(nextOneDecimalDouble(), i, j);
                m4.asignarEntrada(nextOneDecimalDouble(), i, j);
            }
        }
    }

    @Test
    @DisplayName("Constructor")
    public void probarConstructor() {
        m1 = new Matriz(m, n);
        m2 = new Matriz(m, n);
        m3 = new Matriz(n, m);
        assertThat(m1 == m2).isFalse();
        assertThat(m1).isEqualTo(m2);
        assertThat(m1).isNotEqualTo(m3);
        m1.asignarEntrada(1, rnd.nextInt(m), rnd.nextInt(n));
        assertThat(m1).isNotEqualTo(m2);
    }

    @Test
    @DisplayName("Obtener/asignar entrada")
    public void probarObtenerYAsignar() {
        for (int repeat = 0; repeat < 100; repeat++) {
            int i = rnd.nextInt(m), j = rnd.nextInt(n);
            double e = -rnd.nextDouble();
            m1.asignarEntrada(e, i, j);
            assertThat(m1.obtenerEntrada(i, j)).isWithin(TOLERANCE).of(e);
        }
    }

    @Test
    @DisplayName("toString()")
    public void probarToString() {
        m1 = new Matriz(m, n);
        String filaEsperada[] = new String[n];
        java.util.Arrays.fill(filaEsperada, "0.0");
        m1.toString().lines().forEach(
            fila -> assertThat(fila).isEqualTo(String.join(" ", filaEsperada)));
        for (var matriz: new Matriz[]{m2, m3, m4}) {
            m2.toString().lines().forEach(new java.util.function.Consumer<String>() {
                int i, j;
                public void accept(String fila) {
                    for (String dato: fila.split(" ")) {
                        assertThat(Double.parseDouble(dato))
                            .isWithin(TOLERANCE).of(m2.obtenerEntrada(i, j));
                        j++;
                    }
                    j = 0; i++;
                }
            });
        }
    }

    @Test
    @DisplayName("Suma de matrices")
    public void probarSuma() {
        assertThat(m1.sumar(m3)).isNull();
        Matriz suma1 = m1.sumar(m2);
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < n; j++) {
                assertThat(suma1.obtenerEntrada(i, j)).isWithin(TOLERANCE)
                    .of(m1.obtenerEntrada(i, j) + m2.obtenerEntrada(i, j));
            }
        }
    }

    @Test
    @DisplayName("Multiplicación por escalar")
    public void probarEscalar() {
        double c = rnd.nextDouble() * 1000;
        Matriz mult = m1.escalar(c);
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < n; j++) {
                assertThat(mult.obtenerEntrada(i, j)).isWithin(TOLERANCE)
                    .of(m1.obtenerEntrada(i, j) * c);
            }
        }
    }

    @Test
    @DisplayName("Eliminar fila")
    public void probarEliminarFila() {
        for (int fila = 0; fila < m; fila++) {
            Matriz elim = m1.eliminarFila(fila);
            try {
                elim.obtenerEntrada(m - 1, 0);
                assert_().withMessage("La dimensión por filas debió haber decrementado.").fail();
            } catch (ArrayIndexOutOfBoundsException e) {
                assertThat(e).hasMessageThat().contains((m - 1) + "");
            }
            for (int i = 0; i < m; i++) {
                for (int j = 0; j < n; j++) {
                    if (i < fila) {
                        assertThat(elim.obtenerEntrada(i, j)).isEqualTo(m1.obtenerEntrada(i, j));
                    } else if (i > fila) {
                        assertThat(elim.obtenerEntrada(i - 1, j)).isEqualTo(m1.obtenerEntrada(i, j));
                    }
                }
            }
        }
    }

    @Test
    @DisplayName("Eliminar columna")
    public void probarEliminarColumna() {
        for (int columna = 0; columna < n; columna++) {
            Matriz elim = m1.eliminarColumna(columna);
            try {
                elim.obtenerEntrada(0, n - 1);
                assert_().withMessage("La dimensión por columnas debió haber decrementado.").fail();
            } catch (ArrayIndexOutOfBoundsException e) {
                assertThat(e).hasMessageThat().contains((n - 1) + "");
            }
            for (int i = 0; i < m; i++) {
                for (int j = 0; j < n; j++) {
                    if (j < columna) {
                        assertThat(elim.obtenerEntrada(i, j)).isEqualTo(m1.obtenerEntrada(i, j));
                    } else if (j > columna) {
                        assertThat(elim.obtenerEntrada(i, j - 1)).isEqualTo(m1.obtenerEntrada(i, j));
                    }
                }
            }
        }
    }

    @Test
    @DisplayName("Determinante")
    public void probarDeterminante() {
        int p = m < n ? n : m;
        for (int i = 0; i < p; i++) {
            m3.asignarEntrada(0, i, 0);
        }
        assertThat(m3.determinante()).isWithin(TOLERANCE).of(0);
        for (int j = 0; j < p; j++) {
            m4.asignarEntrada(0, 0, j);
        }
        assertThat(m4.determinante()).isWithin(TOLERANCE).of(0);
        Matriz matriz = new Matriz(4, 4);
        double[][] ds = {{9, 1, 2, 8}, {2, 9, 7, 3}, {3, 4, 8, 5}, {5, 8, 3, 3}};
        for (int i = 0; i < 4; i++) {
            for (int j = 0; j < 4; j++) {
                matriz.asignarEntrada(ds[i][j], i, j);
            }
        }
        assertThat(matriz.determinante()).isWithin(TOLERANCE).of(-372);
    }

    private double nextOneDecimalDouble() {
        return Double.parseDouble(String.format("%.1f", rnd.nextDouble() * 10));
    }

}
