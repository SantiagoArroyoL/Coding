public class Pepe{
	public static void main(String[] args) {
		int uno = 1;
		int dos = 1;
		int i = 0;

		for (i=1;i<50;i++) {
			System.out.println(uno += dos);
			System.out.println(dos += uno);
		}
	}
}
