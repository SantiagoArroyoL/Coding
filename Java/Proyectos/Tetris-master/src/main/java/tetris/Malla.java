/**
 * Esta clase va a ser nuestra principal columna, porque va a controlar:
 * Si están libres los espacios o no (Lo cual nos dirá si la pieza puede rotar, caer o nada)
 * Si está ocupada toda una linea debe eliminarla
 * Deber añadir piezas cada cierto tiempo, en esta clase manejaremos también la bolsa de las 7 piezas
 *
 * @author Santi y Clau ^^
 */
package tetris;
import java.util.Random;
import tetris.Tetramino;
import java.util.LinkedList;
import java.util.List;
public class Malla {

	private Random rand = new Random();
	private boolean[][] casillas = new boolean[40][10];
	private boolean[][] temp = new boolean [4][4];
	private boolean[] filasLlenas = new boolean [20];

	/*
	 * Constructor
	 */
    public Malla() {
		for (int i = 0; i < 40; i++) {
			for (int j = 0; j < 10; j++) {
				casillas[i][j] = false;
			}
		}
    } //Cierre del constructor

	public void asignarEspacioMalla(Tetramino pieza) {
		boolean[][] temp = pieza.getEspacio();
		for (int i = 0; i < 4; i++) {
			for (int j = 0; j < 4; j++) {
				casillas[i+21][j+4] = temp[i][j];
			}
		}
	}


	/**
     *Método para acceder a la matriz
	 *
	 * @return casilllas - la matriz de enteros
	 */
    public boolean[][] getCasilllas() {
	  	return casillas;
    }//Cierre del método


	public void dropMalla() {
		for (int i = 0; i < 40 ; i++) {
			for (int j = 0; j < 10 ; j++) {
				if (casillas[i][j] == true && casillas[i+1][j] != false) {
					casillas[i+1][j] = casillas[i][j];
					casillas[i][j] = false;
				}
				// System.out.println(i + " " + j);
			}
		}
	}//Cierre del método

	public boolean revisaFilas() {
		for (int i = 0; i < 40 ; i++) {
			for (int j = 0; j < 10 ; j++) {
				if (casillas[i][j] == true) {
					if (i+1 <= 40) {
						return casillas[i+1][j] == false;
					}
				}
			}
		}
		return false;
	}


	/**
	 *Método para saber cuando una fila está llena
	 * Sirve de auxiliar para el de abajo, si sabes como hacer que todo este en una sola fila, hazlo.
	 * @param int n - el número de fila que va a checar
	 * @return filaLLena - si hay o no una fila llena
	 */
	public boolean hayFilaLlenaAux(int n ) {
		boolean filaLlena = true;
		for(int i = 0; i<10; i++) {
			if (casillas [n][i] == false) {
				filaLlena = false;
			}
		}
		return filaLlena;
		}
		/**
		 *Método para identificar que fila está llena
		 * llama al anterior para cada fila y llena el boolean [] filasLlenas para saber que filas estén llenas
		 * @return hayfilaLlena - true hay una fila llena.
		 **/
	public void hayFilaLlena() {
		boolean hayfilaLlena = false;
		for(int j = 0; j < 20; j++) {
			if(hayFilaLlenaAux(j)) {
				filasLlenas[j]= true;
			}
		}
	}//Cierre de la Clase

	/**
	 * Método que elimina las filas llenas
	 */
	public void eliminaFilas() {
		for(int j = 0; j < 20; j++) {
			for (int i = 0; i < 10; i++) {
				if(filasLlenas[j] == casillas[j][i]) {
					casillas[j][i] = false;
				}
			}
		}
	}

}
