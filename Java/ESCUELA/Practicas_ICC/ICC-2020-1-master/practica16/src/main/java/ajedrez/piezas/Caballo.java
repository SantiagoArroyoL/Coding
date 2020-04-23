package ajedrez.piezas;
import ajedrez.Tablero;
import java.util.List;
import java.util.LinkedList;

/**
 * Clase Caballo.
 *
 * @author Arroyo Lozano Santiago
 * @version 24/10/2019 A
 */
public class Caballo extends Pieza{

	/**
	 * Constructor Caballo.
	 *
	 * @param color El color de la Caballo
	 * @param posicion La posicion de la Caballo
	 */
	public Caballo(Color color, Posicion posicion) {
		super(color,posicion);
	}

	Tablero tab = Tablero.obtenerInstancia();

	/**
	 * Método para obtener Jugadas Legales
	 * @return una lista con todas las posiciones legales
	 */
	@Override
	public List<Posicion> obtenerJugadasLegales() {

		int n = 1;
		int m = 1;
		Pieza p1,p2;
		LinkedList<Posicion> jugadas = new LinkedList<>();
		int fila = obtenerPosicion().obtenerFila();
		int columna = obtenerPosicion().obtenerColumna();

		//Diagonal -+
		if (fila - 1 >= 0 && columna + 1 <= 7) {
			fila--;
			columna++;
			p2 = tab.obtenerPieza(fila + 1,columna - 1);
			if (fila - 1 >= 0 && p2.obtenerColor() != this.obtenerColor()) {
				jugadas.add(new Posicion(fila - 1, columna));
			}
			if (columna + 1 <= 7 && p2.obtenerColor() != this.obtenerColor()) {
				jugadas.add(new Posicion(fila, columna + 1));
			}
		}
		//Diagonal ++
		if (fila + 1 <= 7 && columna + 1 <= 7) {
			fila++;
			columna++;
			p2 = tab.obtenerPieza(fila + 1,columna - 1);
			if (fila + 1 <= 7 && p2.obtenerColor() != this.obtenerColor()) {
				jugadas.add(new Posicion(fila + 1, columna));
			}
			if (columna + 1 <= 7 && p2.obtenerColor() != this.obtenerColor()) {
				jugadas.add(new Posicion(fila, columna + 1));
			}
		}
		//Diagonal +-
		if (fila + 1 <= 7 && columna - 1 >= 0) {
			fila++;
			columna--;
			p2 = tab.obtenerPieza(fila + 1,columna - 1);
			if (fila + 1 <= 7 && p2.obtenerColor() != this.obtenerColor()) {
				jugadas.add(new Posicion(fila + 1, columna));
			}
			if (columna - 1 >= 0 && p2.obtenerColor() != this.obtenerColor()) {
				jugadas.add(new Posicion(fila, columna - 1));
			}
		}
		//Diagonal --
		if (fila - 1 >= 0 && columna - 1 >=0) {
			fila--;
			columna--;
			p2 = tab.obtenerPieza(fila + 1,columna - 1);
			if (fila - 1 >= 0 && p2.obtenerColor() != this.obtenerColor()) {
				jugadas.add(new Posicion(fila - 1, columna));
			}
			if (columna - 1 >= 0 && p2.obtenerColor() != this.obtenerColor()) {
				jugadas.add(new Posicion(fila, columna - 1));
			}
		}

		return jugadas;
	}
}
