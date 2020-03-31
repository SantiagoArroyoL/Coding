import java.util.Scanner;
public class Intervalos {
	public static void main(String[] args) {
		String[] strs;
		String entrada;
		int a,b,c;
		Scanner leer = new Scanner(System.in);
		entrada = leer.nextLine();
		strs = entrada.trim().split("\\s+");

		a = Integer.parseInt(strs[0]);
		b = Integer.parseInt(strs[1]);
		c = Integer.parseInt(strs[2]);

		if (c > a && c > b)
			System.out.println("DERECHA");
		else if (c < a && c < b)
			System.out.println("IZQUIERDA");
		else
			System.out.println("INTERVALO");
	}
}
