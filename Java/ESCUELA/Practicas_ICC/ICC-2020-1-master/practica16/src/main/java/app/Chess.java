/**
 * Programa que dibuja el tablero de ajedrez
 * @author Arroyo Lozano Santiago
 * @version 18/10/2019 A
 */
package app;

import ajedrez.Tablero;
import ajedrez.piezas.*;
import java.util.HashMap;
import java.awt.Component;
import java.io.IOException;
import processing.core.PImage;
import processing.core.PApplet;
import processing.core.PApplet;
import javax.swing.JOptionPane;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import processing.event.MouseEvent;
/**
* Clase que diuja el tablero y las fichas
*
* @author Arroyo Lozano Santiago
* @version 29/10/2019 A
*/
public class Chess extends PApplet {

   private Tablero tablero;
   private HashMap<String, PImage> imagenes;
   private Pieza piezaSeleccionada;
	private boolean seleccionandoJugada;

   public static void main(String[] args) {
      PApplet.main("app.Chess");
   }

   /**
   * Método que configura
   */
   @Override
   public void settings() {
      //Diferenciamos entre pantallas de 16:9 y 4:3
      size(displayHeight * 4 / 5, displayHeight * 4 / 5);
   }


   /**
   * Método que configura
   */
   @Override
   public void setup() {
       try (var in = new ObjectInputStream(new FileInputStream("juego"))) {
            tablero = (Tablero) in.readObject();
       } catch (IOException | ClassNotFoundException e) {
           tablero = Tablero.obtenerInstancia();
       }
      imagenes = new HashMap<>();
      imagenes.put("PeonBLANCO", loadImage(getClass().getResource("/w-pawn.png").getPath()));
      imagenes.put("PeonNEGRO", loadImage(getClass().getResource("/b-pawn.png").getPath()));
      imagenes.put("DamaBLANCO", loadImage(getClass().getResource("/w-queen.png").getPath()));
      imagenes.put("DamaNEGRO", loadImage(getClass().getResource("/b-queen.png").getPath()));
      imagenes.put("CaballoBLANCO", loadImage(getClass().getResource("/w-knight.png").getPath()));
      imagenes.put("CaballoNEGRO", loadImage(getClass().getResource("/b-knight.png").getPath()));
      imagenes.put("AlfilBLANCO", loadImage(getClass().getResource("/w-bishop.png").getPath()));
      imagenes.put("AlfilNEGRO", loadImage(getClass().getResource("/b-bishop.png").getPath()));
      imagenes.put("TorreBLANCO", loadImage(getClass().getResource("/w-rook.png").getPath()));
      imagenes.put("TorreNEGRO", loadImage(getClass().getResource("/b-rook.png").getPath()));
      imagenes.put("ReyBLANCO", loadImage(getClass().getResource("/w-king.png").getPath()));
      imagenes.put("ReyNEGRO", loadImage(getClass().getResource("/b-king.png").getPath()));
      noLoop();
   }

   /**
    * Método que dibuja el rectángulo que necesitamos (Se repite las veces necesarias)
    */
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

      // Colores de las piezas seleccionadas y las que no
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
   }//Cierre del método

   /**
   * Método que detecta el mouse para mover una pieza
   * @param event El botón del mouse
   */
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
    		if (piezaSeleccionada == null	|| tablero.obtenerTurno() != piezaSeleccionada.obtenerColor()) {
    			piezaSeleccionada = null;
    		}
    		seleccionandoJugada = piezaSeleccionada != null;
    	}
    	redraw();
   }//Cierre del método

   /**
   * Método que guarda las jugadas hechas
   */
   public void exit() {
       try (var out = new ObjectOutputStream(new FileOutputStream("juego"))) {
   			out.writeObject(tablero);
       	} catch (IOException ioe) {
            ioe.printStackTrace();
        } finally {
            Component temporaryLostComponent = null;
            JOptionPane.showMessageDialog(temporaryLostComponent, "Felicidades! Saliste del juego!");
            dispose();
            System.exit(0);
        }
    } //Cierre del método

}//Cierre de la clase
