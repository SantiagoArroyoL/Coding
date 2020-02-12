public class bulean {

	public static void main(String[] args) {

		int a = 10;
		int b = 20;
		int c = 30;

		//Está creando la variable test y dándole un valor V o F dependiendo de la comparación

		boolean test = a == b;

		if (test) {
			System.out.println("Hola");
		}
		else {
			System.out.println("Adios");
		}

		// Usando otros poeradores lógicos

		boolean var = (a < b) && (b > c) || (b + a != c);

		System.out.println("Var es igual a " + var);
	}
}
