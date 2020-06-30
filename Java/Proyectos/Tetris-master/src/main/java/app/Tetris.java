/**
 * Programa que dibuja el tablero de ajedrez
 * @author Arroyo Lozano Santiago
 * @version 18/10/2019 A
 */
package app;

import tetris.*;
import java.io.File;
import java.util.List;
import java.util.Random;
import java.util.Arrays;
import processing.core.*;
import processing.event.*;
import processing.sound.*;
import java.awt.Component;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.LinkedList;
import javax.swing.JOptionPane;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

/**
 *Esta clase será la Principal
 * Casi toda la parte gráfica se hace en este archivo
 * Se manejan los eventos del teclado que llaman a los métodos de las piezas
 *
 * @author Santi y Clau ^^
 * @version 4/Dic/2019
 */
public class Tetris extends PApplet {

    private int fila;
    private int n = 0;
    private int Aux = 0;
    private int dt = 500; //Valor en milisegundos de la diferencia de tiempo
    private float columna;
    private SoundFile file; //Variable para la música
    private Boolean gameOn = false; //Variables que nos dirán si el juego ya terminó o no
    private int numeroDeRotaciones ;
    private Tetramino piezaGuardada;
    private Boolean gameOver = false;
    private Malla malla = new Malla(); //La malla del juego
    private int tiempoTrans = millis(); //Valor en milisegundos del tiempo actual
    private Random rand = new Random();
    private Puntos puntos = new Puntos(); //Marcador global del juego
    private List<Tetramino> piezasBloqueadas = new LinkedList<>();
    private int numeroDeRotacionesIzq;
    private Tetramino[] tempArray = new Tetramino[]{new Tetramino(),new Tetramino(),new Tetramino(),new Tetramino(),new Tetramino(),new Tetramino(),new Tetramino()};

    private List<Tetramino> bolsita = Arrays.asList(tempArray); //Bolsita con 7 tetraminos generados al azar
    private Tetramino pieza = bolsita.get(n); //Obtenemos una pieza de dicha casilla
    private int tipo = pieza.getTipo();
    private Tetramino piezaDibujada = pieza;


    public static void main(String[] args) {
        PApplet.main("app.Tetris");
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
        file = new SoundFile(this,getClass().getResource("/Tetris.mp3").getPath());
        file.loop();
        try (var in = new ObjectInputStream(new FileInputStream("Marcadores"))) {
            puntos = (Puntos) in.readObject();
        } catch (IOException | ClassNotFoundException e) {
            puntos = Puntos.obtenerInstancia();
            // System.exit(0);
        }
    }


    /**
     *Método que dibuja la malla en relación a ala altura de la ventana
     */
    @Override
    public void draw() {

        background(0xFF262525);

        //Lleanamos la bolsita cada que se vacíe
        if (n == 6) {
            bolsita = null;
            bolsita.add(new Tetramino());
            bolsita.add(new Tetramino());
            bolsita.add(new Tetramino());
            bolsita.add(new Tetramino());
            bolsita.add(new Tetramino());
            bolsita.add(new Tetramino());
            bolsita.add(new Tetramino());
            n = 0;
        }


        if (gameOn) {

            if (pieza.getBandera()) {
                n++;
                piezasBloqueadas.add(pieza);
                // bolsita.remove(pieza);
                pieza = bolsita.get(n);
            }

            textSize(32);
        	fill(20, 245, 48);
        	text("Puntaje: " + puntos.getMarcador(), 500, 100);
            text("Pieza Guardada: ", 500, 250);
            if (piezaGuardada != null) {
                dibuja(piezaGuardada);
            }

            for (int i = 0; i < 20; i++) {
                for (int j = 0; j < 10; j++) {
                    stroke(0xffffffff);
                    strokeWeight(1);
                    if ((i + j) % 2 == 0) {
    					fill(0xFF262525);
    			    }
                rect(j * (height / 20), i * (height / 20), height / 20, height / 20);
                }
            }

            int actual = millis();
            if (actual - tiempoTrans > dt) {
                tiempoTrans = actual;
                if (!malla.revisaFilas()) {
                    pieza.drop();
                    malla.dropMalla();
                }
            }

            dibuja(pieza);

            for (Tetramino p : piezasBloqueadas) {
                dibuja(p);
            }

        } else if (gameOver) {
            textSize(32);
            fill(255,3,24);
            text("Felicidades, tu puntaje ha sido de " + puntos.getMarcador(), height/4, height/2);
        } else {
            textSize(32);
            fill(255,3,24);
            text("Pulsa Espacio para jugar", height/4, height/2);
        }


    }//Cierre del método

    public void dibuja(Tetramino x) {
        fila = x.getFila();
        columna = x.getColumna();
        tipo = x.getTipo();


        // System.out.println("Fila: " + fila);
        // System.out.println("Columna: " + columna);

        //Dibujamos la forma inicial de cada pieza
        switch(tipo) {

            case 0: {
              //columna = columna +8;
              if(numeroDeRotaciones==0){

                stroke(0xffffffff);
                strokeWeight(3);

                fill(83, 137, 250);

                rect((columna+6)*(height / 40), fila*(height / 40), height / 20, height / 20);
                rect((columna+4)*(height /40), fila*(height /40), height /20, height/ 20);
                rect((columna)*(height /40), fila*(height /40), height /20, height/ 20);
                rect((columna+2)*(height /40), fila*(height /40), height /20, height/ 20);
              }

              if(numeroDeRotaciones == 1 || numeroDeRotaciones == -1){

                stroke(0xffffffff);
                strokeWeight(3);

                fill(83, 137, 250);
                rect((columna+2)*(height /40), fila*(height /40), height /20, height/ 20);
                rect((columna+2)*(height /40), (fila+2)*(height /40), height /20, height/ 20);
                rect((columna+2)*(height /40), (fila+4)*(height /40), height /20, height/ 20);
                rect((columna+2)*(height /40), (fila+6)*(height /40), height /20, height/ 20);
              }

              if(numeroDeRotaciones == 2 || numeroDeRotaciones == -2){
                stroke(0xffffffff);
                strokeWeight(3);

                fill(83, 137, 250);
                rect((columna+4)*(height / 40), (fila+2)*(height / 40), height / 20, height / 20);
                rect((columna+2)*(height /40), (fila+2)*(height /40), height /20, height/ 20);
                rect((columna)*(height /40), (fila+2)*(height /40), height /20, height/ 20);
                rect((columna+6)*(height /40), (fila+2)*(height /40), height /20, height/ 20);
              }
              if(numeroDeRotaciones == 3 || numeroDeRotaciones == -3){
                columna = columna+4;
                stroke(0xffffffff);
                strokeWeight(3);

                fill(83, 137, 250);
                rect((columna+4)*(height /40), fila*(height /40), height /20, height/ 20);
                rect((columna+4)*(height /40), (fila+2)*(height /40), height /20, height/ 20);
                rect((columna+4)*(height /40), (fila+4)*(height /40), height /20, height/ 20);
                rect((columna+4)*(height /40), (fila+6)*(height /40), height /20, height/ 20);
              }

                break;
            }

            case 1: {

              if(numeroDeRotaciones == 0){
                stroke(0xffffffff);
                strokeWeight(3);

                fill(0, 67, 206);
                rect((columna)*(height/40), fila*(height /40), height / 20, height / 20);
                rect((columna)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna+4)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna+2)*(height/40), (fila+2)*(height / 40), height /20, height /20);
              }
              if(numeroDeRotaciones == 1 || numeroDeRotaciones == -1){
                columna = columna-2;
                stroke(0xffffffff);
                strokeWeight(3);

                fill(0, 67, 206);
                  rect((columna+6)*(height/40), fila*(height /40), height / 20, height / 20);
                  rect((columna+4)*(height/40), fila*(height /40), height / 20, height / 20);
                  rect((columna+4)*(height/40), (fila+2)*(height /40), height / 20, height / 20);
                  rect((columna+4)*(height/40), (fila+4)*(height /40), height / 20, height / 20);

              }
              if(numeroDeRotaciones == 2 || numeroDeRotaciones == -2){
                stroke(0xffffffff);
                strokeWeight(3);

                fill(0, 67, 206);
                rect((columna)*(height/40), (fila+2)*(height /40), height / 20, height / 20);
                rect((columna+4)*(height/40), (fila+2)*(height /40), height / 20, height / 20);
                rect((columna+2)*(height/40), (fila+2)*(height /40), height / 20, height / 20);
                rect((columna+4)*(height/40), (fila+4)*(height /40), height / 20, height / 20);


              }
              if(numeroDeRotaciones == 3 || numeroDeRotaciones == -3){
                columna = columna +2;
                stroke(0xffffffff);
                strokeWeight(3);

                fill(0, 67, 206);
                rect((columna-2)*(height/40), (fila+4)*(height /40), height / 20, height / 20);
                rect((columna)*(height/40), (fila)*(height /40), height / 20, height / 20);
                rect((columna)*(height/40), (fila+2)*(height /40), height / 20, height / 20);
                rect((columna)*(height/40), (fila+4)*(height /40), height / 20, height / 20);
              }
                break;

            }

            case 2: {
              if(numeroDeRotaciones == 0){
                stroke(0xffffffff);
                strokeWeight(3);

                fill(252, 114, 0);
                rect((columna+4)*(height/40), fila*(height /40), height / 20, height / 20);
                rect((columna)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna+2)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna+4)*(height/40), (fila+2)*(height / 40), height /20, height /20);
              }
              if (numeroDeRotaciones == 1 || numeroDeRotaciones == -1){
                columna = columna -2;
                stroke(0xffffffff);
                strokeWeight(3);

                fill(252, 114, 0);
                rect((columna+4)*(height/40), (fila)*(height / 40), height /20, height /20);
                rect((columna+4)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna+4)*(height/40), (fila+4)*(height / 40), height /20, height /20);
                rect((columna+6)*(height/40), (fila+4)*(height / 40), height /20, height /20);
              }
              if(numeroDeRotaciones == 2 || numeroDeRotaciones == -2){

                stroke(0xffffffff);
                strokeWeight(3);

                fill(252, 114, 0);
                rect((columna)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna+2)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna+4)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna)*(height/40), (fila+4)*(height / 40), height /20, height /20);

              }
              if(numeroDeRotaciones == 3 || numeroDeRotaciones == -3){
                columna = columna +2;
                stroke(0xffffffff);
                strokeWeight(3);

                fill(252, 114, 0);
                rect((columna)*(height/40), (fila)*(height / 40), height /20, height /20);
                rect((columna)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna)*(height/40), (fila+4)*(height / 40), height /20, height /20);
                rect((columna-2)*(height/40), (fila)*(height / 40), height /20, height /20);

              }
                break;
            }

            case 3: {
              columna = columna +2;
                stroke(0xffffffff);
                strokeWeight(3);

                fill(252, 203, 0);
                rect((columna-2)*(height/40), fila*(height /40), height / 20, height / 20);
                rect((columna)*(height/40), fila*(height /40), height / 20, height / 20);
                rect((columna-2)*(height/40), (fila+2)*(height /40), height / 20, height / 20);
                rect(columna*(height/40), (fila+2)*(height /40), height / 20, height / 20);



                break;

            }

            case 4: {

              if(numeroDeRotaciones == 0){
                stroke(0xffffffff);
                strokeWeight(3);

                fill(157, 255, 46);
                rect((columna+2)*(height/40), fila*(height / 40), height /20, height /20);
                rect((columna+4)*(height/40), fila*(height / 40), height /20, height /20);
                rect((columna+2)*(height/40), (fila+2)*(height /40), height / 20, height / 20);
                rect((columna)*(height/40), (fila+2)*(height /40), height / 20, height / 20);
              }
              if (numeroDeRotaciones == 1 || numeroDeRotaciones == -1){
                columna = columna -2;
                stroke(0xffffffff);
                strokeWeight(3);

                fill(157, 255, 46);
                rect((columna+4)*(height/40), fila*(height / 40), height /20, height /20);
                rect((columna+4)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna+6)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna+6)*(height/40), (fila+4)*(height / 40), height /20, height /20);

              }
              if(numeroDeRotaciones == 2 || numeroDeRotaciones == -2){

                stroke(0xffffffff);
                strokeWeight(3);

                fill(157, 255, 46);
                rect((columna)*(height/40), (fila+4)*(height / 40), height /20, height /20);
                rect((columna+2)*(height/40), (fila+4)*(height / 40), height /20, height /20);
                rect((columna+2)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna+4)*(height/40), (fila+2)*(height / 40), height /20, height /20);

              }
              if(numeroDeRotaciones == 3 || numeroDeRotaciones == -3){
                columna = columna + 2;
                stroke(0xffffffff);
                strokeWeight(3);

                fill(157, 255, 46);
                rect((columna-2)*(height/40), (fila)*(height / 40), height /20, height /20);
                rect((columna-2)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna)*(height/40), (fila+4)*(height / 40), height /20, height /20);

              }
                break;
            }

            case 5: {

              if(numeroDeRotaciones == 0){
                stroke(0xffffffff);
                strokeWeight(3);

                fill(126, 0 , 255);
                rect((columna)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna+2)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna+4)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna+2)*(height/40), fila*(height / 40), height /20, height /20);
              }
              if(numeroDeRotaciones == 1 || numeroDeRotaciones == -1){
                columna = columna -2;
                stroke(0xffffffff);
                strokeWeight(3);

                fill(126, 0 , 255);
                rect((columna+4)*(height/40), (fila)*(height / 40), height /20, height /20);
                rect((columna+4)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna+4)*(height/40), (fila+4)*(height / 40), height /20, height /20);
                rect((columna+6)*(height/40), (fila+2)*(height / 40), height /20, height /20);

              }
              if(numeroDeRotaciones == 2 || numeroDeRotaciones == -2){
                stroke(0xffffffff);
                strokeWeight(3);

                fill(126, 0 , 255);
                rect((columna)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna+2)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna+4)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna+2)*(height/40), (fila+4)*(height / 40), height /20, height /20);

              }
              if(numeroDeRotaciones == 3 || numeroDeRotaciones == -3){
                columna = columna + 2 ;
                stroke(0xffffffff);
                strokeWeight(3);

                fill(126, 0 , 255);
                rect((columna)*(height/40), (fila)*(height / 40), height /20, height /20);
                rect((columna)*(height/40), (fila+2)*(height / 40), height /20, height /20);
                rect((columna)*(height/40), (fila+4)*(height / 40), height /20, height /20);
                rect((columna-2)*(height/40), (fila+2)*(height / 40), height /20, height /20);

              }
                break;
            }
            case 6:{

              if(numeroDeRotaciones == 0 ){
                stroke(0xffffffff);
                strokeWeight(3);

                fill(255, 0, 0);
                rect((columna)*(height / 40), fila*(height / 40), height / 20, height / 20);
                rect((columna+2)*(height / 40), fila*(height / 40), height / 20, height / 20);
                rect((columna+4)*(height / 40), (fila+2)*(height / 40), height / 20, height / 20);
                rect((columna+2)*(height / 40), (fila+2)*(height / 40), height / 20, height / 20);
              }
              if(numeroDeRotaciones == 1 || numeroDeRotaciones == -1){
                columna = columna -2;
                stroke(0xffffffff);
                strokeWeight(3);

                fill(255, 0, 0);
                rect((columna+6)*(height / 40), fila*(height / 40), height / 20, height / 20);
                rect((columna+6)*(height / 40), (fila+2)*(height / 40), height / 20, height / 20);
                rect((columna+4)*(height / 40), (fila+2)*(height / 40), height / 20, height / 20);
                rect((columna+4)*(height / 40), (fila+4)*(height / 40), height / 20, height / 20);

              }
              if(numeroDeRotaciones == 2 || numeroDeRotaciones == -2){

                stroke(0xffffffff);
                strokeWeight(3);

                fill(255, 0, 0);
                rect((columna)*(height / 40), (fila+2)*(height / 40), height / 20, height / 20);
                rect((columna+2)*(height / 40), (fila+2)*(height / 40), height / 20, height / 20);
                rect((columna+2)*(height / 40), (fila+4)*(height / 40), height / 20, height / 20);
                rect((columna+4)*(height / 40), (fila+4)*(height / 40), height / 20, height / 20);


              }
              if(numeroDeRotaciones == 3 || numeroDeRotaciones == -3){
                columna = columna +2;
                stroke(0xffffffff);
                strokeWeight(3);

                fill(255, 0, 0);
                rect((columna)*(height / 40), (fila)*(height / 40), height / 20, height / 20);
                rect((columna)*(height / 40), (fila+2)*(height / 40), height / 20, height / 20);
                rect((columna-2)*(height / 40), (fila+2)*(height / 40), height / 20, height / 20);
                rect((columna-2)*(height / 40), (fila+4)*(height / 40), height / 20, height / 20);

              }
                break;
            }
        }//Cierre de un switch
    }//Cierre del método

    public void guardar() {
        piezaGuardada = pieza;
        piezaGuardada.setFila(25);
        piezaGuardada.setColumna(25);
        pieza = null;
    }
    /**
    * Método que detecta el mouse para mover una pieza
    */
    @Override
    public void keyPressed() {
        switch(keyCode) {
            case 32: gameOn = true; break; // Espacio
            case LEFT: pieza.izquierda(); break;
            case RIGHT: pieza.derecha(); break;
            case DOWN: pieza.drop(); break;
            case UP: {
                if (!piezasBloqueadas.contains(pieza)) {
                    Aux++;
                    numeroDeRotaciones = Aux % 4;
                }
              break;
            }
            case 90: {
                if (!piezasBloqueadas.contains(pieza)) {
                    Aux--;
                    numeroDeRotaciones = Aux % 4;
                }
              break;
            }//z
            case 99: guardar(); break;
            default: break;
        }
    }//Cierre del método

   /**
   * Método que guarda las jugadas hechas
   */
   public void exit() {
       try (var out = new ObjectOutputStream(new FileOutputStream("juego"))) {
   			out.writeObject(puntos);
       	} catch (IOException ioe) {
            ioe.printStackTrace();
        } finally {
            dispose();
            System.exit(0);
        }
    } //Cierre del método

}//Cierre de la clase
