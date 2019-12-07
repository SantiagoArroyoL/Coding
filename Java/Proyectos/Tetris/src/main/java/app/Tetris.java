/**
 * Programa que dibuja el tablero de ajedrez
 * @author Arroyo Lozano Santiago
 * @version 18/10/2019 A
 */
package app;

import tetris.Malla;
import tetris.Tetramino;
import java.io.File;
import processing.core.*;
import processing.event.*;
import java.awt.Component;
import java.io.IOException;
import java.io.InputStream;
import javax.swing.JOptionPane;
import java.io.FileInputStream;
import javax.sound.sampled.Clip;
import java.io.FileOutputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.AudioInputStream;
/**
 *Esta clase será la Principal
 * Casi toda la parte gráfica se hace en este archivo
 * Se manejan los eventos del teclado que llaman a los métodos de las piezas
 *
 * @author Santi y Clau ^^
 * @version 4/Dic/2019
 */
public class Tetris extends PApplet {

    private int dt = 500; //Valor en milisegundos de la diferencia de tiempo
    private Tetramino pieza; //Referencia a la pieza ya existente en la clase casilla
    private Boolean gameOn = false; //Variables que nos dirán si el juego ya terminó o no
    private Boolean gameOver = false;
    private Malla malla = new Malla(); //La malla del juego
    private int tiempoTrans = millis(); //Valor en milisegundos del tiempo actual

    public static void main(String[] args) {
      PApplet.main("app.Tetris");
      musica("/../../resources/Tetris.wav");
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
            malla = (Malla) in.readObject();
        } catch (IOException | ClassNotFoundException e) {
            // malla = malla.obtenerInstancia();
            // System.exit(0);
        }
    }


    /**
     *CMétodo que dibuja la malla en relación a ala altura de la ventana
     */
    @Override
    public void draw() {

        background(0xFF262525);

        for (int i = 0; i < 20; i++) {
            for (int j = 0; j < 10; j++) {
                stroke(0xffffffff);
                strokeWeight(1);
                if ((i + j) % 2 == 0) {
					fill(0xFF262525);
				}
                rect(j * (height / 20), i * (height / 20), height / 10, height / 10);
            }
        }


        if (gameOn) {
            int actual = millis();
            if (actual - tiempoTrans > dt) {
                tiempoTrans = actual;
                pieza.drop();
            }
        } else {
            // System.out.println("Presiona espacio para iniciar");
            //No será un println pero bueno
        }

        // if (pieza != null) {
        //     switch (pieza.obtenerColor()) {
        //         case 0:
        //         case 1:
        //         case 2:
        //         case 3:
        //         case 4:
        //         case 5:
        //     }
        // }

        // if (pieza.tetris()) {
        //     for (int i = 0; i < 4; i++) {
        //         for (int j = 0; j < 10; j++) {
        //             fill(0xffffff00);
        //             r
        //         }
        //     }
        // }

    }//Cierre del método

    /**
     *Método que configura la música del juego
     *
     * @param filepath -- La ruta del archivo de música (Sölo puede ser .wav)
     */
    public static void musica(String filepath) {
        try {
            File musicPath = new File(filepath);
            if (musicPath.exists()) {
                AudioInputStream audioInput = AudioSystem.getAudioInputStream(musicPath);
                Clip clip = AudioSystem.getClip();
                clip.open(audioInput);
                clip.start();

                JOptionPane.showMessageDialog(null, "Error");
            } else {
                System.out.println("No se puede encontrar el archivo de sonido");
            }
        } catch(Exception e) {
            JOptionPane.showMessageDialog(null, "Error");
        }
    }//Cierre del método


   /**
   * Método que guarda las jugadas hechas
   */
   public void exit() {
       try (var out = new ObjectOutputStream(new FileOutputStream("juego"))) {
   			out.writeObject(malla);
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
