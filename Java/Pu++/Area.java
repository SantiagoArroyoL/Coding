import java.util.Scanner;
public class Area {
	public static void main(String[] args) {
		Scanner leer = new Scanner(System.in);
		int n = leer.nextInt();
		int resultado = poligonoIdeal(n);
		System.out.println(resultado);
	}

	private static int poligonoIdeal(int n) {
		if (n == 1)
			return 1;
		return (4*(n-1))+poligonoIdeal(n-1);
	}
}
