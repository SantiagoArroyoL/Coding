package ajedrez.piezas;
import java.util.Random;
import java.util.List;
import java.util.LinkedList;
import java.util.Scanner;

public class Main {
	public static void main(String[] args) {
		int j = 0,n = 0;
		boolean validacion = false;
		Color color = Color.BLANCO;
		Scanner leer = new Scanner(System.in);
		Posicion pos = new Posicion(6,1);
		Peon uno = new Peon(color,pos);
		int fila = pos.obtenerFila();
		List<Posicion> jugadas = uno.obtenerJugadasLegales();

		do {
			j = 0;
			for (Posicion p : jugadas) {
				Posicion actual = jugadas.get(j);
				System.out.println("----------------------------Opcion " + j + "--------------------------------");
				System.out.println("La posicion a la que te puedes mover es a la fila: " + actual.obtenerFila());
				System.out.println("La posicion a la que te puedes mover es a la columna:" + actual.obtenerColumna());
				j++;
			}
			try{
				if (jugadas.size() == 0) {
					System.out.println("Llegaste al final del tablero");
					validacion = true;
					break;
				}
				System.out.println("-------------------------------------------------------");
				System.out.println("A cuál de las 2 opciones te quieres mover?");
				n = leer.nextInt();
				Posicion pos2 = jugadas.get(n);
				uno.asignarPosicion(pos2);
				jugadas = uno.obtenerJugadasLegales();
			} catch (Exception e) {
				System.out.println("Por favor introduce sólo el número de las opciones mostradas");
				System.exit(0);
			}
		} while (!validacion);
	}
}
