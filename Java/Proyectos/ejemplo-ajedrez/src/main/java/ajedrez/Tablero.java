package ajedrez;

import java.util.List;
import ajedrez.piezas.Color;
import ajedrez.piezas.Posicion;
import ajedrez.piezas.Pieza;
import ajedrez.piezas.Dama;
import ajedrez.piezas.Peon;

public class Tablero {

    private class Casilla {

        private Pieza pieza;

        public Pieza obtenerPieza() {
            return pieza;
        }

        public void asignarPieza(Pieza pieza) {
            this.pieza = pieza;
        }

        public boolean esVacio() {
            return pieza == null;
        }

    }

    private static final Tablero INSTANCIA = new Tablero();

    private Casilla[][] casillas;
    private List<Pieza> piezasBlancasVivas;
    private List<Pieza> piezasNegrasVivas;
    private Color turno;

    private Tablero() {
        casillas = new Casilla[8][8];
        piezasBlancasVivas = new java.util.LinkedList<>();
        piezasNegrasVivas = new java.util.LinkedList<>();
        turno = Color.BLANCO;
        for (int i = 0; i < 8; i++) {
            for (int j = 0; j < 8; j++) {
                casillas[i][j] = new Casilla();
                if (i >= 2 && i <= 5) continue; // Casillas vacías
                
                Posicion posicion = new Posicion(i, j);
                Color color = (i >= 6) ? Color.BLANCO : Color.NEGRO;
                Pieza pieza = null;
                if (i == 1 || i == 6) {
                    pieza = new Peon(color, posicion);
                }                                       // switch
                if (i == 7 && j == 3) {
                    pieza = new Dama(color, posicion);
                }
                casillas[i][j].asignarPieza(pieza);
                (color == Color.BLANCO ? piezasBlancasVivas : piezasNegrasVivas).add(pieza);
            }
        }
    }

    public static Tablero obtenerInstancia() {
        return INSTANCIA;
    }

    public Pieza obtenerPieza(int i, int j) {
        return casillas[i][j].obtenerPieza();
    }

    public Color obtenerTurno() {
        return turno;
    }

    public void asignarPieza(Pieza pieza, int fila, int columna) {
        if (pieza != null) {
            pieza.asignarPosicion(new Posicion(fila, columna));
        }
        casillas[fila][columna].asignarPieza(pieza);
    }

    public void moverPieza(Pieza pieza, int fila, int columna) {
        if (pieza == null
                || (fila == pieza.obtenerPosicion().obtenerFila()    
                        && columna == pieza.obtenerPosicion().obtenerColumna())
                || turno != pieza.obtenerColor()
                || !pieza.esJugadaLegal(fila, columna)) {
            return;
        }
        Pieza capturada = obtenerPieza(fila, columna);
        asignarPieza(null, pieza.obtenerPosicion().obtenerFila(), 
                     pieza.obtenerPosicion().obtenerColumna());
        asignarPieza(pieza, fila, columna);
        if (turno == Color.BLANCO) {
            piezasNegrasVivas.remove(capturada);
            turno = Color.NEGRO;
        } else {
            piezasBlancasVivas.remove(capturada);
            turno = Color.BLANCO;
        }
    }

}