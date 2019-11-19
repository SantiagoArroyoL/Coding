package ajedrez.piezas;

import java.util.List;
import java.util.LinkedList;
import ajedrez.Tablero;

public class Peon extends Pieza {

    public Peon(Color color, Posicion posicion) {
        super(color, posicion);
    }

    @Override
    public List<Posicion> obtenerJugadasLegales() {
        var jugadas = new LinkedList<Posicion>();
        Tablero tablero = Tablero.obtenerInstancia();
        int fila = obtenerPosicion().obtenerFila(),
            columna = obtenerPosicion().obtenerColumna();
        if (obtenerColor() == Color.BLANCO) {
            if (tablero.obtenerPieza(fila - 1, columna) == null) {
                jugadas.add(new Posicion(fila - 1, columna));
            }
        } else {
            if (tablero.obtenerPieza(fila + 1, columna) == null) {
                jugadas.add(new Posicion(fila + 1, columna));
            }
        }
        return jugadas;
    }

}