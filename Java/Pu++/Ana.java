import java.util.Scanner;
public class Ana {
	public static void main(String[] args) {
		float[] a;
		float min;
		int[] indice;
		String[] strs;
		String entrada;
		int i,s,n,t;
		Scanner leer = new Scanner(System.in);
		Scanner sc = new Scanner(System.in);

		t = leer.nextInt();
		indice = new int[t];
		for(i = 0; i < t; i++) {
			entrada = sc.nextLine();
			strs = entrada.trim().split("\\s+");

			s = Integer.parseInt(strs[0]);
			n = Integer.parseInt(strs[1]);

			entrada = sc.nextLine();
			strs = entrada.trim().split("\\s+");

			a = new float[strs.length];
			for (int j = 0; j < strs.length; j++)
	 		   a[j] = Float.parseFloat(strs[j]);

			min = a[0];
			indice[i] = 1;
			for(int j = 1; j < a.length; j++)
	   			if(a[j] < min){
	   				min = a[j];
					indice[i] = j+1;
				}
		}
		for (int k = 0; k < i; k++)
			System.out.println("Case " + (k+1) + ": comprar en dia " + indice[k]);
	}
}
