import java.util.Scanner;
public class inputs{
	public static void main(String[] args) {

		Scanner in = new Scanner(System.in);
		System.out.println("What is your name?");
		String name = in.nextLine();

		System.out.println("How old are you?");
		int age = in.nextInt();

		System.out.println("Your name is " + name + " and you are " + age + " years old");

		//OTRA MANERA DE HACERLO ES:
		Scanner puma1 = new Scanner(System.in);

		System.out.println("¿Cómo te llamas?");

		String nombre = puma1.nextLine();

		System.out.println("¿Cuántos años tienes?");

		int edad = 0;
		boolean gotIt = false;
		while(!gotIt){
			try{
				edad = puma1.nextInt();
				gotIt = true;
			} catch (Exception ex){
				System.out.println("That is not a valid number!");
				//Esto Evita que se quede loopeando infinitamente, poruq elo que pasa es que si no pones "puma1.next" siempre se quedará el valor erroneo y no te dejará avanzar
				puma1.next();
				continue;
			}
		}

		System.out.println("Te llamas " + nombre + " y tienes " + edad + " años de edad");
	}
}
