/**
 * Clase que simula el comportamiento de un robot
 * Los condicionales if que están en cada método aseguran que sólo se pueda acceder a dicho método cuando el robot está despierto, cada uno tiene su return al final para cubrir todos los casos
 * @author Arroyo Lozano Santiago
 * @version 14/09/2019 A
 */
public class Robot {
    private String nombre;
    private String marca;
    private String numSerie;
    private boolean estaDormido;

    /**
     * Constructor de un robot a partir de su nombre, marca y número de serie
     * @param n - nombre del robot
     * @param m - marca del robot
     * @param num - número de serie del robot
     */
    public Robot (String n, String m, String num) {
         asignarNombre(n);
         asignarMarca(m);
         asignarNumSerie(num);
   }

    /**
     * Método para asignar nombre al robot
     * @param nomb -- cadena con el nombre del robot
     */
    public void asignarNombre(String nomb) {
      this.nombre = nomb;
    }
    /**
     * Método para asignar marca al robot
     * @param marca -- cadena con la marca del robot
     */
    public void asignarMarca(String marca) {
      this.marca = marca;
    }
    /**
     * Método para asignar numSerie al robot
     * @param num -- cadena con el numero de serie del robot
     */
    public void asignarNumSerie(String num) {
      this.numSerie = num;
    }
    /**
     * Método para obtener el nombre del robot
     * @return String -  nombre del robot
     */
    public String obtenerNombre() {
         return nombre;
    }
    /**
     * Método para obtener la marca del robot
     * @return String -  marca del robot
     */
    public String obtenerMarca() {
         return marca;
    }
    /**
     * Método para obtener el número de Serie del robot
     * @return String -  número de serie del robot
     */
    public String obtenerNumSerie() {
         return numSerie;
    }
    /**
     * Método para hacer dormir al robot
     */
    public void dormir() {
      this.estaDormido = true;
      System.out.println("ZZZ ZZZ");

    }
    /**
     * Método para despertar al robot
     */
    public void despertar() {
      this.estaDormido = false;
    }
    /**
     * Método para saber si el robot está despierto
     * @return boolean -- Si es true el robot está despierto y false si esta dormindo
     */
    public boolean estaDespierto() {
      if (this.estaDormido) {
         return false;
      } else {
         return true;
      }
    }
    /**
     * Método para que el robot repita lo que se le dice
     * @param rollo -- cadena con el rollo que se desea repita el robot
     */
    public void repetir(String rollo) {
      if (!this.estaDormido) {
         System.out.println(rollo);
      }
    }
    /**
     * Método para determinar si dos robots son iguales
     * @param robot -- robot con el que se va a comparar
     * @return boolean -- true si son iguales y false en otro caso.
     */
    public boolean equals (Robot robot) {
         return this == robot;
    }
    /**
     * Método para devolver una cadena con el nombre del robot.
     * @return String -- cadena que devolvera
     */
    public String toString () {
         return this.nombre;
    }

    /**
     * Método para que el robot reste los números que se le dan
     * @param num1 -- minuendo
     * @param num2 -- sustraendo
     */
    public void restar(long num1, long num2) {
      if (!this.estaDormido) {
         long resultado = num1-num2;
         System.out.println("La resta de " + num1 + " y " + num2 + " es " + resultado);
      }
    }
    /**
     * Método para que el robot sume los números que se le dan
     * @param num1 -- primer sumando
     * @param num2 -- segundo sumando
     */
    public void sumar(long num1, long num2) {
      if (!this.estaDormido) {
         long resultado = num1+num2;
         System.out.println("La suma de " + num1 + " y " + num2 + " es " + resultado);
      }
    }

    /**
     * Método para que el robot multiplique los números que se le dan
     * @param num1 -- primer factor
     * @param num2 -- segundo factor
     */
    public void multiplicar(long num1, long num2) {
      if (!this.estaDormido) {
         long resultado = num1*num2;
         System.out.println("La multiplicación de " + num1 + " y " + num2 + " es " + resultado);
      }
    }
    /**
     * Método para que el robot divida los números que se le dan
     * @param num1 -- dividendo
     * @param num2 -- divisor
     */
    public void dividir(long num1, long num2) {
      if (!this.estaDormido) {
         if (num2 == 0) {
            System.out.println("No puedo dividir entre cero");
         }else{
            long resultado = num1/num2;
            System.out.println("La división de " + num1 + " y " + num2 + " es " + resultado);
         }
      }
    }
}
