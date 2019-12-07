/**
 * Esta clase va a ser nuestra principal columna, porque va a controlar:
 * Si están libres los espacios o no (Lo cual nos dirá si la pieza puede rotar, caer o nada)
 * Si está ocupada toda una linea debe eliminarla
 * Deber añadir piezas cada cierto tiempo, en esta clase manejaremos también la bolsa de las 7 piezas
 *
 * @author Santi y Clau ^^
 */

package tetris;
import java.io.Serializable;
import java.util.Random;


public class Malla implements Serializable {

	/**
	 * Clase auxiliar Casillas que nos señala si existe la pieza en la casilla o no
	 */
	private class Casilla implements Serializable {

		private Tetramino pieza;

		public Tetramino obtenerPieza() {
			return pieza;
		}

		public void asignarPieza(Tetramino pieza) {
			this.pieza = pieza;
		}

		public boolean esVacio() {
			return pieza == null;
		}

	}//Cierre de la clase auxiliar Casillas

	Random rand = new Random();
	private int[] bolsita = new int[7];
	Casilla[][] casilllas = new Casilla[40][10];
	private static final Malla INSTANCIA = new Malla();

	//Ahorita funciona con una matriz de enteros

    public Malla() {

		//Bucle for que genera la bolsita de próximas piezas
		for (int i = 0; i < bolsita.length; i++) {
        	bolsita[i] = rand.nextInt(7);
        }

		//Bucle for que crea la malla
	    for (int i = 0; i < 40; i ++) {
	      for (int j = 0; j < 10; j ++) {
	        casilllas[i][j] = new Casilla();
	      }
	    }
    }

	public static Malla obtenerInstancia() {
        return INSTANCIA;
    }


	/**
     *Método para acceder a la matriz
	 *
	 * @return casilllas - la matriz de enteros
     */
    public Casilla[][] getCasilllas() {
	  	return casilllas;
    }//Cierre del método


}//Cierre de la Clase
