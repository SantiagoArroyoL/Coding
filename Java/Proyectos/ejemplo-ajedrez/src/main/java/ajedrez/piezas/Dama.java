package ajedrez.piezas;

import java.util.List;
import java.util.LinkedList;
import ajedrez.Tablero;

public class Dama extends Pieza {

    public Dama(Color color, Posicion posicion) {
        super(color, posicion);
    }

    @Override
    public List<Posicion> obtenerJugadasLegales() {
        var jugadas = new LinkedList<Posicion>();
        int fila = obtenerPosicion().obtenerFila(),
            columna = obtenerPosicion().obtenerColumna();
        for (int j = columna - 1; j >= 0; j--) {
            if (f(fila, j, jugadas)) {
                break;
            }
        }
        for (int j = columna + 1; j <= 7; j++) {
            if (f(fila, j, jugadas)) {
                break;
            }   
        }
        for (int i = fila - 1; i >= 0; i--) {
            if (f(i, columna, jugadas)) {
                break;
            }   
        }
        for (int i = fila - 1, j = columna + 1; i >= 0 && j <= 7; i--, j++) {
            if (f(i, j, jugadas)) {
                break;
            }   
        }
        return jugadas;
    }

    private boolean f(int i, int j, List<Posicion> lista) {
        Tablero tablero = Tablero.obtenerInstancia();
        if (tablero.obtenerPieza(i, j) == null || obtenerColor() != tablero.obtenerPieza(i, j).obtenerColor()) {
            lista.add(new Posicion(i, j));
        }
        return tablero.obtenerPieza(i, j) != null;
    }

}