package app;

import processing.core.PApplet;
import processing.core.PImage;
import processing.event.MouseEvent;
import java.util.HashMap;
import ajedrez.Tablero;
import ajedrez.piezas.Color;
import ajedrez.piezas.Posicion;
import ajedrez.piezas.Pieza;
import ajedrez.piezas.Peon;
import ajedrez.piezas.Dama;

public class Main extends PApplet {

	private Tablero tablero;
	private HashMap<String, PImage> imagenes; 
	private Pieza piezaSeleccionada;
	private boolean seleccionandoJugada;

	public static void main(String[] args) {
		PApplet.main("app.Main");
	}

	@Override
	public void settings() {
		size(displayHeight * 4 / 5, displayHeight * 4 / 5);
	}

	@Override
	public void setup() {
		tablero = Tablero.obtenerInstancia();
		imagenes = new HashMap<>();
		imagenes.put("PeonBLANCO",
					 loadImage(getClass().getResource("/w-pawn.png").getPath()));
		imagenes.put("PeonNEGRO",
					 loadImage(getClass().getResource("/b-pawn.png").getPath()));
		imagenes.put("DamaBLANCO",
					 loadImage(getClass().getResource("/w-queen.png").getPath()));
		imagenes.put("DamaNEGRO",
					 loadImage(getClass().getResource("/b-queen.png").getPath()));
		noLoop();
	}

	@Override
	public void draw() {
		background(0xffffffff);

		for (int i = 0; i < 8; i++) {
			for (int j = 0; j < 8; j++) {
				stroke(0xff000000);
				strokeWeight(1);
				if ((i + j) % 2 == 0) {
					fill(0xffffffff);
				} else {
					fill(0x44000000);
				}
				rect(j * (height / 8), i * (height / 8),
					 height / 8, height / 8);
			}
		}



		if (piezaSeleccionada != null) {
			int fila = piezaSeleccionada.obtenerPosicion().obtenerFila(),
				columna = piezaSeleccionada.obtenerPosicion().obtenerColumna();
			stroke(0xffff0000);
			strokeWeight(3);
			for (Posicion pos: piezaSeleccionada.obtenerJugadasLegales()) {
				fill((pos.obtenerFila() + pos.obtenerColumna()) % 2 == 0 ? 0xffffffff : 0x44000000);
				rect(pos.obtenerColumna() * (width / 8),
					 pos.obtenerFila() * (width / 8),
				 	 width / 8, width / 8);
			}
			stroke(0xff0000ff);
			strokeWeight(3);
			fill((fila + columna) % 2 == 0 ? 0xffffffff : 0x44000000);
			rect(columna * (width / 8), fila * (width / 8),
				 width / 8, width / 8);
		}

		for (int i = 0; i < 8; i++) {
			for (int j = 0; j < 8; j++) {
				Pieza pieza = tablero.obtenerPieza(i, j);
				if (pieza != null) {
					image(imagenes.get(pieza.getClass().getSimpleName() + pieza.obtenerColor()),
						  j * (height / 8), i * (height / 8),
						  height / 8, height / 8);
				}
			}
		}
	}

	@Override
    public void mouseClicked(MouseEvent event) {
    	int fila = event.getY() / (width / 8);
    	int columna = event.getX() / (width / 8);
    	if (seleccionandoJugada) {
    		tablero.moverPieza(piezaSeleccionada, fila, columna);
    		seleccionandoJugada = false;
    		piezaSeleccionada = null;
    	} else {
    		piezaSeleccionada = tablero.obtenerPieza(fila, columna);
    		if (piezaSeleccionada == null
    				|| tablero.obtenerTurno() != piezaSeleccionada.obtenerColor()) {
    			piezaSeleccionada = null;
    		}
    		seleccionandoJugada = piezaSeleccionada != null;
    	}

    	redraw();
    }

}
