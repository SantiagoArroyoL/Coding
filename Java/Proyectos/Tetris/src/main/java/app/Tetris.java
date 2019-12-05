/**
 * Programa que dibuja el tablero de ajedrez
 * @author Arroyo Lozano Santiago
 * @version 18/10/2019 A
 */
package app;

import tetris.*;
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

    private int tmntxt = 20;
    private int tiempoTrans = millis();
    private int cols, filas,dt;
    private Boolean gameOn = false;
    private Boolean gameOver = false;
    private Casillas malla = new Casillas(); //Esta clase todavía no esta terminada XD
    private int altura = displayHeight * 4 / 5;
    private int textColor = color(34, 230, 190);
    // Tetramino pieza = new Tetramino();

    public static void main(String[] args) {
      PApplet.main("app.Tetris");
      musica("/resources/Tetris.wav");
    }

    /**
     *Configuramos la serializacion del objeto
     */
    @Override
    public void setup() {
        textSize(20);
        try (var in = new ObjectInputStream(new FileInputStream("juego"))) {
             malla = (Casillas) in.readObject();
        } catch (IOException | ClassNotFoundException e) {
            // malla = Casillas.obtenerInstancia();
        }
    } //Cierre del método

    /**
     *Configuramos el tamaño de la ventana
     */
    @Override
    public void settings() {
        size(altura, altura);
    }//Cierre del método


    /**
     *CMétodo que dibuja la malla en relación a ala altura de la ventana
     */
    @Override
    public void draw() {

        background(0xffffffff);

          for (int i = 0; i < 20; i++) {
              for (int j = 0; j < 10; j++) {
                  stroke(0xff000000);
                  strokeWeight(1);
                  if ((i + j) % 2 == 0) {
                      fill(0xffffffff);
                  } else {
                      fill(0x44000000);
                  }
                  rect(j * (height / 8), i * (height / 8), height / 8, height / 8);
              }
          }

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
