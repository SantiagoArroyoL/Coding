package ajedrez.piezas;
import ajedrez.Tablero;
import java.util.List;
import java.util.LinkedList;

/**
 * Clase Peón.
 *
 * @author Arroyo Lozano Santiago
 * @version 22/10/2019 A
 */
public class Peon extends Pieza {

	/**
	 * Constructor Peón
	 *
	 * @param color El color del peoń
	 * @param posicion la posición del peoń
	 */
	public Peon(Color color, Posicion posicion){
		super(color,posicion);
	}


	/**
	 * Método para obtener Jugadas Legales
	 * @return una lista con todas las posiciones legales
	 */
	@Override
	public List<Posicion> obtenerJugadasLegales() {

		LinkedList<Posicion> jugadas = new LinkedList<>();
		int fila = obtenerPosicion().obtenerFila();
		int columna = obtenerPosicion().obtenerColumna();
		Tablero tab = Tablero.obtenerInstancia();
		Pieza p1,p2;

		if (obtenerColor() == Color.BLANCO) {
			if (fila == 6) {
				jugadas.add(new Posicion(fila - 2, columna));
			}
			p1 = tab.obtenerPieza(fila-1,columna-1);
			if (p1 != null && p1.obtenerColor() != Color.BLANCO) {
				jugadas.add(new Posicion(fila - 1, columna - 1));
			}
			p2 = tab.obtenerPieza(fila-1,columna+1);
			if (p2 != null && p2.obtenerColor() != Color.BLANCO) {
				jugadas.add(new Posicion(fila - 1, columna + 1));
			}
			if (fila -1 >= 0) {
				jugadas.add(new Posicion(fila - 1, columna));
			}
		} else {
			if (fila == 1) {
				jugadas.add(new Posicion(fila + 2, columna));
			}
			p1 = tab.obtenerPieza(fila+1,columna+1);
			if (p1 != null && p1.obtenerColor() != Color.NEGRO) {
				jugadas.add(new Posicion(fila + 1, columna + 1));
			}
			p2 = tab.obtenerPieza(fila+1,columna+1);
			if (p2 != null && p2.obtenerColor() != Color.NEGRO) {
				jugadas.add(new Posicion(fila + 1, columna - 1));
			}
			if (fila + 1 <= 7) {
				jugadas.add(new Posicion(fila + 1, columna));
			}
		}
		return jugadas;
	}
}
