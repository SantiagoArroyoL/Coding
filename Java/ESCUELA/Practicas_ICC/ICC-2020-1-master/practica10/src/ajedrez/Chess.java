/**
 * Programa que dibuja el tablero de ajedrez
 * @author Arroyo Lozano Santiago
 * @version 18/10/2019 A
 */
package ajedrez;

import processing.core.PApplet;

public class Chess extends PApplet {

   public static void main(String[] args) {
      PApplet.main(Chess.class.getName());
   }

   @Override
   public void settings() {
      //Diferenciamos entre pantallas de 16:9 y 4:3
      if (displayWidth/16 == 120) {
        int m = displayHeight/9;
        size(displayWidth/2, displayHeight-m);
     } else {
        int m = displayHeight/3;
        size(displayWidth/2, displayHeight-m);
     }
   }

   @Override
   public void setup() {
   }

   /**
    * Método que dibuja el rectángulo que necesitamos (Se repite las veces necesarias)
    */
   @Override
   public void draw() {
      if (displayWidth/16 == 120) {
         //Para pantallas 16:9
         int m = displayHeight/9;
         int n = displayWidth/16;
         for (int i = 0; i < 8; i ++) {
            for (int j = 0; j < 8; j ++) {
               if ((i + j + 1) % 2 == 0) {
                  fill(0, 0, 0);
               } else {
                  fill(255, 255, 255);
               }
               rect(i * n, j * m, (i + 1) * n, (j + 1) * m);
            }
         }
      } else {
         //Para pantallas 4:3
         int m = displayHeight/12;
         int n = displayWidth/16;
         for (int i = 0; i < 8; i ++) {
            for (int j = 0; j < 8; j ++) {
               if ((i + j + 1) % 2 == 0) {
                  fill(0, 0, 0);
               } else {
                  fill(255, 255, 255);
               }
               rect(i * n, j * m, (i + 1) * n, (j + 1) * m);
            }
         }
      }
   }//Cierre del método
}//Cierre de la clase
