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


public class Casillas implements Serializable {

	private int [][] cells = new int[40][10];
	//Ahorita funciona con una matriz de enteros

    public Casillas() {
	    for (int i = 0; i < 40; i ++) {
	      for (int j = 0; j < 10; j ++) {
	        cells[i][j] = 0;
	      }
	    }
    }

    /**
     * Método que nos avisa si la casilla está libre o no
     * Si la casilla es distinta de cero entonces no está libre
     *
     * @return true si esta libre - false en caso contrario
     */
    public Boolean estaLibre (int x, int y) {
	    return cells[x][y] == 0;
    } //Cierre del método

	/**
     *Método para acceder a la matriz
	 *
	 * @return cells - la matriz de enteros
     */
    public int[][] getCells() {
	  	return cells;
    }//Cierre del método

}//Cierre de la Clase
