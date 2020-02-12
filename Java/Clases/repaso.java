/*
	REPASO:
		- Variables
		- Operadores matematicos
		- Strings(Cadena de caracteres)
		- Methods(Funciones)
		- Lógica booleana
		- If, else & else if
		- Booleans con if
		- Loops
		- Arrays
		- For loop
		- Enchanced For Loop
		- OOP (Object Oriented Programing)
		- Constructors
		*/
public class repaso{
	public static void main(String[] args) {
		//Variable type, identifier, assign a value
		int a = 10;
		int b = 20;
		int c = -1;

		//El % te da el residuo de una operación
		//Usando los operadores matematicos:
		int d = (( a * b * c) + (a + b) - (c * (b - a)) %  c) * a;

		System.out.println("Operadores matematicos:" + d);

		//Usando Strings:
		String name = "Ollie";
		String hello = "Hello ";

		System.out.println(hello + name);
		//(Los methods se encuentran al final de la página)
		//Methods:
		print("Esto que estoy escribiendo va a reemplazar a la variable s");
		int x = add(34, 6);
		System.out.println(x);

		//Booleans con If,else
		int e = 100;
		int r = 20;

		boolean test = e > r;
		//if test == true
		if (test) {
			System.out.println("e es mayor que r");
		}
		else if (e == r) {
			System.out.println("e es igual que r");
		}
		else {
			System.out.println("e es menor que r");
		}

		boolean testA = e > 0;
		boolean testB = r > 0;

		//Usando operadores lógicos;
		if (testA && testB) {
			System.out.println("Las dos son verdaderas");
		}
		else if (testA || testB){
			System.out.println("Alguna de las dos es verdadera");
		}
		else{
			System.out.println("Ninguna es verdadera");
		}

		//LOOPS:
		boolean loop = true;
		int l = 0;
		//While loop
		while(loop) {
			System.out.println(l);
			l++;
			if (l >= 10) {
				loop = false;
				System.out.println("Loop has stopped");
			}
		}
		//Do while loop
		do {
			System.out.println(x);
		} while (x < 10);
		//ARRAYS
		//Método uno:
		String[] namesExample = {"Ollie", "Hason" };
		//Método dos:
		String[] nombresEjemplo = new String[3];

		nombresEjemplo[0] = "Santiago";
		nombresEjemplo[1] = "Pepe";
		nombresEjemplo[2] = "Andrés";

		//Usarlos:
		System.out.println(nombresEjemplo[0] + " " + nombresEjemplo[1] + " " + nombresEjemplo[2]);

		System.out.println("-----------------------------------------------------------");

		//FOR LOOP:
		String[] nombres = {"Santiago", "Pepe", "Patiño", "Sofía" };

		for (int i = 0; i < nombres.length; i++) {
			System.out.println(nombres[i]);
		}
		//.length es una función de los arreglos.
		//Enchanced FOR LOOP (each) (Cada uno, uno por uno)
		for (String z : nombres ) {
			System.out.println(z);
		}

		//OOP(Se necesita el constructor)
		mascota max = new mascota("Mascota: Max", "Dueño: Ollie");
		mascota shadow = new mascota("Mascota: Shadow","Dueño: Santiago");

		System.out.println(max.nombre);
		System.out.println(max.amo);

		System.out.println(shadow.nombre);
		System.out.println(shadow.amo);
	}


	//METHODS
	static void print(String s)   {
		System.out.println(s);
	}
	//No importa que "int a" e "int b" ya estén declaradas
	static int add(int a, int b)   {
		return a + b;
	}
}
