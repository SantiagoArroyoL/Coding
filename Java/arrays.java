public class arrays{

	public static void main(String[] args) {
		String[] namesOfWorkers = { "Bill", "Bob", "Ollie", "Jade"};

		System.out.println(namesOfWorkers[3]);
		// Recuerda que se cuenta desde el 0
		System.out.println("Ejemplos de uso:");

		int x = 0;
		System.out.println("There are " + namesOfWorkers.length + " workers, and their names are: ");

		while(x < 4){
			System.out.println(namesOfWorkers[x]);
			x++;
		}

		//Otra manera de declarar un array es:
		String[] ejemplo = new String[4];

		ejemplo[0] = "Cero";
		ejemplo[1] = "Uno";
		ejemplo[2] = "Dos";
		ejemplo[3] = "Tres";

	}
}
