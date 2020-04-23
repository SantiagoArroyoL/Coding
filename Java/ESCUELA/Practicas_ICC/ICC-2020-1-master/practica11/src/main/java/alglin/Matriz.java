package alglin;

/**
 * Representa una matriz de mxn con entradas en los reales.
 *
 * @author Arroyo Lozano Santiago
 * @version 18/10/2019 A
 */
public class Matriz {

    private double[][] datos;
    private int m, n;

    /**
     * Crea una matriz de mxn donde todas las entradas son cero.
     *
     * @param m el número de filas
     * @param n el número de columnas
     */
    public Matriz(int m, int n) {
      this.datos = new double[m][n];
      this.m = m;
      this.n = n;
      for (int i = 0; i < m; i++) {
         for (int j = 0; j < n; j++) {
            datos[i][j] = 0;
         }
      }
    }

    /**
     * Regresa la entrada en la i-ésima fila y j-ésima columna de esta matriz.
     *
     * @param i la fila de la entrada deseada
     * @param j la columna de la entrada deseada
     * @return la entrada i,j
     */
    public double obtenerEntrada(int i, int j) {
      return datos[i][j];
    }

    /**
     * Inserta el dato dado en la i-ésima fila y j-ésima columna de esta matriz.
     *
     * @param dato el número que se insertará en esta matriz
     * @param i    la fila donde se insertará <code>dato</code>
     * @param j    la columna donde se insertará <code>dato</code>
     */
    public void asignarEntrada(double dato, int i, int j) {
      datos[i][j] = dato;
    }

    /**
     * Suma esta matriz con otra. Regresa <code>null</code> si las matrices no tienen las mismas
     * dimensiones.
     *
     * @param otra la otra matriz con la cual se sumará esta
     * @return una matriz nueva que resulta de sumar esta con <code>otra</code>
     */
    public Matriz sumar(Matriz otra) {
      if (this.m == otra.m && this.n == otra.n) {
         Matriz sumada = new Matriz(m,n);
         for (int i = 0; i < m; i++) {
            for (int j = 0; j < n; j++) {
               sumada.datos[i][j] = this.datos[i][j] + otra.datos[i][j];
            }
         }
         return sumada;
      } else {
         return null;
      }
   }//Cierre del método

    /**
     * Multiplica esta matriz por un escalar.
     *
     * @param c el escalar real
     * @return una matriz nueva que resulta de multiplicar esta por <code>c</code>
     */
    public Matriz escalar(double c) {
      Matriz escalada = new Matriz(m,n);
      for (int i = 0; i < m; i++) {
         for (int j = 0; j < n; j++) {
            escalada.datos[i][j] = this.datos[i][j] * c;
         }
      }
      return escalada;
    }

    /**
     * Elimina una fila de esta matriz.
     *
     * @param k la fila a eliminar
     * @return una matriz nueva que resulta de eliminar la k-ésima fila de esta matriz
     */
    public Matriz eliminarFila(int k) {
      Matriz eliminada = new Matriz(m-1,n);
         for (int i = 0; i < m; i++) {
            for (int j = 0; j < n; j++) {
               if (i != k) {
                  if (i > k) {
                     eliminada.datos[i-1][j] = datos[i][j];
                  } else {
                     eliminada.datos[i][j] = datos[i][j];
                  }
               }
            }
         }
      return eliminada;
    }//Cierre del método

    /**
     * Elimina una columna de esta matriz.
     *
     * @param k la columna a eliminar
     * @return una matriz nueva que resulta de eliminar la k-ésima columna de esta matriz
     */
    public Matriz eliminarColumna(int k) {
      Matriz eliminada = new Matriz(m,n-1);
         for (int i = 0; i < m; i++) {
            for (int j = 0; j < n; j++) {
               if (j != k) {
                  if (j > k) {
                     eliminada.datos[i][j-1] = datos[i][j];
                  } else {
                     eliminada.datos[i][j] = datos[i][j];
                  }
               }
            }
         }
      return eliminada;
   }//Cierre del método

   /**
    * Calcula el determinante de esta matriz.
    *
    * @return el determinante de esta matriz
    */
	public double determinante() {
      int signo;
      double menor;
      int comodin = 1;
      double determinante = 0.0;
      Matriz matrizCofactor;
      if (m == n) {
         if (m == 1) {
            return this.datos[0][0];
         }
         for (int i = 0; i < m; i++) {
            for (int j = 0; j < n; j++) {
               signo = ((j+i) % 2 == 0) ? 1:-1;
               if (i < 1) {
                  if (m > 2) {
                     menor = datos[i][j];
                     matrizCofactor = eliminarFila(i).eliminarColumna(j);
                     determinante += signo * menor * matrizCofactor.determinante();
                  } else {
                     comodin = (j == 1) ? -1:comodin;
                     determinante += signo * datos[i][j]*datos[i+1][j+comodin];
                  }
               }
            }
         }
      }
      return determinante;
   } // Cierre del método

    /**
     * Regresa los datos de esta matriz de tal forma que las columnas están separadas por un espacio
     * y las filas están separadas por un salto de línea. Por ejemplo: <br>
     * "2.0 3.0 0.0 1.0 <br>
     * &nbsp;4.0 0.0 9.0 8.0 <br>
     * &nbsp;5.0 7.0 2.0 4.0"
     *
     * @return la representación en <code>String</code> de esta matriz
     */
    @Override
    public String toString(){
      String matrizCadenosa = "";
      for(int i = 0; i < m; i++) {
         for(int j = 0; j < n; j++) {
            matrizCadenosa += "" + datos[i][j];
            if(j < n-1){
               matrizCadenosa += " ";
            }
         }
         if(i < m-1){
            matrizCadenosa += "\n";
         }
      }
      return matrizCadenosa;
    }

    /**
     * Regresa <code>true</code> si y sólo si <code>obj</code> es una instancia de
     * {@link alglin.Matriz} y las matrices son iguales entrada por entrada.
     *
     * @param obj el objeto a comparar
     * @return <code>true</code> si <code>this</code> y <code>obj</code> son iguales entrada por
     *         entrada
     */
    @Override
    public boolean equals(Object obj) {
      boolean x = false;
      if (this == obj) {
         x = true;
      }
      if (obj != null && getClass() == obj.getClass()) {
         Matriz otra = (Matriz) obj;
         if (m == otra.m && n == otra.n) {
            x = true;
         }
      }
      if (x) {
         Matriz otra = (Matriz) obj;
         for (int  i = 0; i < m; i++) {
            for (int j = 0; j < n; j++) {
               if (datos[i][j] != otra.datos[i][j]) {
                  x = false;
               }
            }
         }
      }
      return x;
   }//Cierre del método

}// Cierre de la clase
