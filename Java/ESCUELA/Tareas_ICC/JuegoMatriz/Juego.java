import java.util.Scanner;

public class Juego{

	public static void main(String[] args) {
		Scanner lector = new Scanner(System.in);		
		Tablero tablero = new Tablero(5,5);
		int intentos = 3;
		while(intentos > 0){
			System.out.println("Intentos restantes: " + intentos);
			System.out.println(tablero);
			System.out.print("Ingresa la fila: ");
			int i = lector.nextInt();
			System.out.print("Ingresa la columna: ");
			int j = lector.nextInt();
			System.out.print("Ingresa el número: ");
			int numero = lector.nextInt();
			if(tablero.adivinoCelda(i,j,numero)){
				System.out.println(tablero);
				System.out.println("GANASTE");
				
				System.exit(0);
			}
			System.out.println("No adivinaste, intenta de nuevo...");
			intentos--;			
		}
		tablero.descubreCeldas();
		System.out.println(tablero);
		System.out.println("Se acabaron tus intentos... PERDISTE");
	}
}