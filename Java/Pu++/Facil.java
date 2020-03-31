import java.util.Scanner;
public class Facil {
	public static void main(String[] args) {
		Scanner leer = new Scanner(System.in);
		String entrada = leer.nextLine();
		String[] strs = entrada.trim().split("\\s+");
		long n = Long.parseLong(strs[0]);
		long m = Long.parseLong(strs[1]);
		System.out.println(n*m);
	}
}
