package ajedrez;
import java.util.List;
import ajedrez.piezas.*;
import java.io.Serializable;

public class Tablero implements Serializable{

    private class Casilla implements Serializable {

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
                }
                if (i == 0 || i == 7) {
                   switch (j) {
                      case 0: pieza = new Torre(color, posicion); break;
                      case 1: pieza = new Caballo(color, posicion); break;
                      case 2: pieza = new Alfil(color, posicion); break;
                      case 3: pieza = new Dama(color, posicion); break;
                      case 4: pieza = new Rey(color, posicion); break;
                      case 5: pieza = new Alfil(color, posicion); break;
                      case 6: pieza = new Caballo(color, posicion); break;
                      case 7: pieza = new Torre(color, posicion); break;
                   }
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
        if ((i >= 0 && i <= 7) && (j >= 0 && j <= 7)) {
            return casillas[i][j].obtenerPieza();
		} else {
			return null;
		}
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
