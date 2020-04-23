/**
* Clase main
*
* Genera Streams conforme a los métodos declarados
* @author Arroyo Lozano Santiago
* @version 12/11/2019 A
**/

package src;

import java.util.stream.Stream;
import java.util.stream.IntStream;
import java.util.stream.Collectors;
import java.util.List;
import java.util.LinkedList;
import java.util.function.Supplier;
import java.util.Arrays;
import java.util.Random;

public class Main {

   public static void main(String args[]) {

		System.out.println("\nEjercicio 1:");
      List<String> prueba = Arrays.asList("a","abc","ab");
		ordena(prueba).forEach(System.out::println);

		System.out.println("Ejercicio 2:\n");
      Stream<Integer> prueba2 = Stream.of(new Integer[] {-1, 11, 0, 12, -7, 7});
		espanol(prueba2).forEach(System.out::println);

		System.out.println("\nEjercicio 3:");
		sucesion("ab").limit(10).forEach(System.out::println);

      System.out.println("\nEjercicio 4:");
      extra(5).forEach(System.out::println);
	} //Cierre del main



	//******Ejercicio 1**********
   /**
    * Método que recibe un List<String> y devuelve un Stream<String> con las mismas cadenas pero ordenadas por su tamaño
    * @param a Una Lista de cadenas que contiene las cadenas a ordenar
    * @return Un stream de cadenas con las cadenas ordenadas de mayor a menor
    **/
	public static Stream<String> ordena(List<String> a) {
		return a.stream() //Lo hacemos un stream
               .sorted((x, y) -> y //Lo ordenamos
               .compareTo(x)); //En relación a quien es más grande
               //Si x es diferente de y y es más grande entonces mandará positivo e irá haciendo un merge sort
	}//Cierre del método

	//******Ejercicio 2**********
   /**
    * Un método que recibe un Stream<Integer>, descarta todos los elementos menores a cero o mayores a nueve
    * y regresa la representación en español de cada dígito.
    * @param e Un stream de enteros con los números a manipular
    * @return Un stream de cadenas con la representación en español de cade número menor a 9 y mayor a 0 del stream original
    **/
	public static Stream<String> espanol(Stream<Integer> e) {
		String[] codigo = new String[]{"cero","uno","dos","tres","cuatro","cinco","seis","siete","ocho","nueve"};
		return e.filter(n -> (n >= 0 && n < 9)).map(x -> codigo[x]);
   }//Cierre del método

	//******Ejercicio 3**********
   /**
    * Un método que recibe una cadena s y devuelve un Stream<String> infinito donde despues de "" s+s se repite sucesivamente
    * @param s La cadena a repetir
    * @return Un stream de cadenas infinitas con s+s repetido infinitamente
    **/
	public static Stream<String> sucesion(String s) {
		return Stream.generate(new Supplier<String>() {
			int i = 0;
			public String get() {
				return s.repeat(i++);
			}
		});
	}//cierre del método

	//******Ejercicio 4**********
   /**
    * Un método que recibe un entero k, genere un IntStream infinito con elementos aleatorios entre 0 y 1000, descarte aquellos elementos
    * que no sean m´ultiplo de k y regrese un List<String> de los primeros 50 elementos del IntStream.
    * @param k El entero del cual se examinarán sus múltiplos
    * @return Una lista de enteros que contenga los primeros 50 valores del stream manipulado
    **/
	public static List<String> extra(int k) {
		return new Random().ints(0,1001) // Generamos un IntStream infinito de valores entre 0 y 1000
                                    .filter(n -> n % k == 0) //Eliminamos los que no sean múltiplos de k
                                    .limit(50) //Escogemos sólo los primeros 50
                                    .boxed() //Lo transformamos a un Stream<Integer>
                                    .map(s -> String.valueOf(s)) //Lo transformamos a un Stream<String>
                                    .collect(Collectors.toList()); //Lo transformamos a una List<String>
	}//Cierre del método

}//Cierre de la clase
