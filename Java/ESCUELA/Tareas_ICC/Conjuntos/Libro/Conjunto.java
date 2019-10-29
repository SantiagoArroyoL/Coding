/**
 *  Clase que implementa la representacion de un Conjunto de numeros enteros
 *  cuyo valor esta entre 1 y 100.
 *
 *  @author Arroyo Lozano Santiago
 *  @version 5/10/2019
 *
 */
public class Conjunto {

    /*
     *  Arreglo que nos sirve para determinar que elementos
     *  pertenecen al Conjunto.
     */
   private int[] conjunto = new int[10];

   /**
    *  Constructor que inicializa un Conjunto vacio.
    *  Es decir, un Conjunto sin ningun elemento.
    */
   public Conjunto() {
     // Escribe aqui el codigo de este metodo
     this.conjunto = new int[] {};
   }

   /**
    *  Metodo que inicializa un Conjunto que contenga
    *  los enteros pasados como parametro.
    *  El arreglo pasado como parametro contiene, solamente,
    *  enteros cuyo valor esta entre 1 y 100.
    *  @param elementosIniciales Elementos que debera de contener el nuevo Conjunto.
    */
   public Conjunto(int[] elementosIniciales){
      this.conjunto = elementosIniciales;
      for (int i = 0; i < this.conjunto.length; i++) {
         if (this.conjunto[i] == 0) {
            eliminar(this.conjunto[i]);
         }
      }
   }

   /**
    * Devuelve el valor del arreglo dentro del conjunto
    * @return Arreglo dentro del Conjunto
    */
   private int[] getArreglo(){
      return this.conjunto;
   }

   /**
    *  Devuelve un Conjunto que contiene la union de el Conjunto
    *  que manda a llamar al metodo con el Conjunto c.
    *  @param c Conjunto que se va a unir.
    *  @return Nuevo Conjunto resultado de la union de ambos Conjuntos.
    */
   public Conjunto union(Conjunto c){
     // Escribe aqui el codigo de este metodo
     int[] temp = c.getArreglo();
     Conjunto union = new Conjunto(this.conjunto);
     for (int i = 0; i < temp.length; i++) {
        //Eliminamos los elementos repetidos
        if (!union.pertenece(temp[i])) {
           union.introducir(temp[i]);
        }
     }
     return union;
   }

   /**
    *  Devuelve un Conjunto que contiene la interseccion de el Conjunto
    *  que manda a llamar al metodo con el Conjunto c.
    *  @param c Conjunto que se va a unir.
    *  @return Nuevo Conjunto resultado de la interseccion de ambos Conjuntos.
    */
   public Conjunto interseccion(Conjunto c){
     int[] temp = c.getArreglo();
     Conjunto interseccion = new Conjunto();
     for (int i = 0; i < temp.length; i++) {
        //Incluimos sólo los elementos repetidos
        if (pertenece(temp[i])) {
           interseccion.introducir(temp[i]);
        }
     }
     return interseccion;
   }

   /**
    *  Devuelve un Conjunto resultado de la diferencia entre el Conjunto
    *  que llama al metodo y el Conjunto c.
    *  @param c Conjunto cuyos elementos seran restados al Conjunto que llama al metodo.
    *  @return Resultado de la diferencia entre ambos Conjuntos.
    */
   public Conjunto diferencia(Conjunto c){
      int[] temp = c.getArreglo();
      for (int i = 0; i < temp.length; i++) {
         if (pertenece(temp[i])) {
            eliminar(temp[i]);
         }
      }
      return new Conjunto(this.conjunto);
   }

   /**
    *  Determina si el elemento pasado como parametro pertenece o no
    *  al Conjunto.
    *  @param elemento Elemento que sera buscado dentro del Conjunto.
    *  @return true - Si el elemento esta en el Conjunto. false - En otro caso.
    */
   public boolean pertenece(int elemento){
      boolean x = false;
      for (int i = 0; i < this.conjunto.length; i++) {
         if (this.conjunto[i] == elemento) {
            x = true;
         }
      }
      return x;
   }

   /**
    *  Metodo que introducir un nuevo elemento al Conjunto.
    *  @param elemento Elemento que sera introducido al Conjunto.
    */
   public void introducir(int elemento){
      /*Modificamos el tamaño del arreglo y almacenamos sus valores en un arreglo temporal
       * para después volver a insertarlo */
       if (!pertenece(elemento)) {
         //Para que no haya elementos repetidos
         if (elemento <= 100 && elemento >= 1) {
            // Sólo números del 1 al 100
            if (this.conjunto.length != 0) {
               //Caso para conjuntos con elementos
               int[] temp = this.conjunto;
               this.conjunto = null;
               this.conjunto = new int[temp.length+1];
               for (int i = 0; i < temp.length; i++) {
                  this.conjunto[i] = temp[i];
                  this.conjunto[i+1] = elemento;
               }
            }else {
               //Caso para conjuntos vacíos
               this.conjunto = null;
               this.conjunto = new int[]{elemento};
            }
         }else {
            System.out.println("No se puede introducir el " + elemento + " en el conjunto.");
         }
      }
   }

   /**
    *  Metodo que eliminar un elemento del Conjunto.
    *  @param elemento Elemento que sera eliminado del Conjunto.
    */
   public void eliminar(int elemento){
      /*Modificamos el tamaño del arreglo y almacenamos sus valores en un arreglo temporal
       * para después volver a insertarlo */
      int[] temp = this.conjunto;
      this.conjunto = null;
      for(int i = 0; i < temp.length; i++){
         if(temp[i] == elemento){
            this.conjunto = new int[temp.length-1];
            for (int index = 0; index < i; index++) {
               this.conjunto[index] = temp[index];
            }
            for(int j = i; j < temp.length - 1; j++){
                 this.conjunto[j] = temp[j+1];
            }
         }
      }
   }

   /**
    *  Metodo que determina si dos Conjuntos son o no iguales.
    *  @param c Conjunto que sera comparado.
    *  @return true - Si son iguales. false - En otro caso.
    */
   public boolean equals(Conjunto c){
      int[] temp = c.getArreglo();
      int n = 0;
      if (this.conjunto.length == temp.length) {
         for (int i = 0; i < this.conjunto.length; i++) {
            if (this.conjunto[i] == temp[i]) {
               n++;
            }
         }
      }
      return n == this.conjunto.length;
   }

   /**
    *  Metodo que devuelve la representacion en cadena del Conjunto.
    *  La cadena resultante tiene un formato como el que sigue:
    *  {4, 6, 80, 99}
    *  @return Representacion en cadena del Conjunto.
    */
   public String toString(){
      String arreglo = "{";
      int j = 0;
      if (this.conjunto.length != 0) {
         for (int i = 0; i < this.conjunto.length-1; i++) {
               arreglo += this.conjunto[i] + ", ";
               j++;
         }
         arreglo += this.conjunto[j];
      }
      return arreglo + "}";
   }
}
