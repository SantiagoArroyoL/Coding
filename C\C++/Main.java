import java.util.Scanner;
public class Main {
	public static void main(String[] args) {
		Scanner s = new Scanner(System.in);
		// int t = Integer.valueOf(args[0]);
		int area, t;
		t = s.nextInt();
		for (int i = 0; i < t; i++) {
			area = s.nextInt();
			System.out.println("Area a comprar: " + area*2);
		}
	}
}
