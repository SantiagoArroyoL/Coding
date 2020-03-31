import java.util.Scanner;
public class Barbulla {
	public static void main(String[] args) {
		int numFinal = 0, n;
		Scanner leer = new Scanner(System.in);
		n = leer.nextInt();
		for (int x = 1; x <= n; x++)
			numFinal += x*(x+1)/2;
		System.out.println(numFinal);
	}
}
