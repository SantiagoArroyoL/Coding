package tetris;
import processing.core.*;
import java.util.Random;

public class Tetramino {

    private int fila;
    private float columna;
    private Random random = new Random();
    private int tipo = random.nextInt(7);
    private boolean[][] espacio = new boolean[4][4];
    private boolean bandera = false;

    /**
     * Constructor de los tetraminos que genera unn tipo de pieza al azar
     * Le damos la forma de cada tetramino para los 6 tipos de pieza que hay en el juego
     * Si la matriz tiene true es porque ahí hay un cuadro de una pieza
     */
    public Tetramino () {
    fila = -2;
    columna = 6;

    switch (tipo) {

        // I
        case 0 : {
            for (int i = 0; i < 4; i++) {
              for (int j = 0; j < 4; j++) {
                espacio[i][j] = (i == 1) ? true : false;
              }
            }
            break;
        }

        // J
        case 1 : {
            for (int i = 0; i < 4; i++) {
              for (int j = 0; j < 4; j++) {
                espacio[i][j] = (i == 1 && j < 3) ? true : false;
              }
            }
            espacio[0][0] = true;
            break;
        }

        // L
        case 2 : {
            for (int i = 0; i < 4; i++) {
              for (int j = 0; j < 4; j++) {
                espacio[i][j] = (i == 1 && j > 0) ? true : false;
              }
            }
            espacio[3][3] = true;
            break;
        }

        // O
        case 3 : {
            for (int i = 0; i < 4; i++) {
              for (int j = 0; j < 4; j++) {
                espacio[i][j] = ((i == 0 || i == 1 ) && (j == 1 || j == 2)) ? true : false;
              }
            }
            break;
        }

        // S
        case 4 : {
            for (int i = 0; i < 4; i++) {
              for (int j = 0; j < 4; j++) {
                espacio[i][j] = ((i == 1 && j < 2) || (i == 0 && j == 1)) ? true : false;
              }
            }
            espacio[0][2] = true;
            break;
        }

        // T
        case 5 : {
            for (int i = 0; i < 4; i++) {
              for (int j = 0; j < 4; j++) {
                espacio[i][j] = (i == 1 && j < 3) ? true : false;
              }
            }
            espacio[0][1] = true;
            break;
        }

        // Z
        case 6 : {
            for (int i = 0; i < 4; i++) {
              for (int j = 0; j < 4; j++) {
                espacio[i][j] = ((i == 0 && j < 2) || (i == 1 && j == 1)) ? true : false;
              }
            }
            espacio[1][3] = true;
            break;
        }

        }//Cierre del switch
    }//Cierre del método constructor

  public int getTipo(){
  return tipo;
}
  /**
   * Método que rota la pieza hacia la derecha
   */
  public void rotarDerecha() {
    System.out.println("hey");
  }//Cierre del método

  /**
   * Método que rota la pieza hacia la izquierda
   */
  public void rotarIzquierda() {
    System.out.println("hey");
  }//Cierre del método


  /**
   * Método que mueve la pieza hacia la izquierda
   */
  public void izquierda() {
    if (columna <=16 && columna>0 && fila<36) {
        columna--;
        columna--;
    }
  }//Cierre del método


  /**
   * Método que mueve la pieza hacia la derecha
   */
  public void derecha() {
    if(tipo == 3){
    if (columna <= 15 && fila<36) {
       columna++;
       columna++;
    }
  }else if(tipo >0){
    if(columna <= 13 && fila < 36){
      columna++;
      columna++;
    }
  }else{
    if(columna <=11 && fila <36){
      columna++;
      columna++;
    }
  }
  }
  //Cierre del método


  /**
   * Método que hace caer la pieza una fila
   */
  public void drop() {
        if (tipo == 0 && fila < 38) {
            fila++;
            fila++;
        } else if(fila < 36) {
	        fila++;
	        fila++;
    	} else {
            bandera = true;
        }
  }//Cierre del método

  /**
  * Método para obtener la fila de la Pieza
  * @return fila donde se encuentra la Pieza
  */
  public int getFila() {
    return fila;
  }//Cierre del método


  /**
  * Método para obtener la columna de la Pieza
  * @return columna donde se encuentra la Pieza
  */
  public float getColumna() {
    return columna;
  }//Cierre del método


  /**
  * Método para asignar la fila de la Pieza
  * @param fila fila a asignar
  */
  public void setFila(int fila) {
    this.fila = fila;
  }//Cierre del método


  /**
  * Método para asignar la columna de la Pieza
  * @param columna columna a asignar
  */
  public void setColumna(float columna) {
    this.columna = columna;
  }//Cierre del método


  /**
  * Método para obtener el espacio de la pieza
  * @return La matriz booleana con el espacio de la pieza
  */
  public boolean[][] getEspacio() {
    return espacio;
  }//Cierre del método

  public boolean getBandera(){
      return bandera;
  }

}//Cierre de la clase
