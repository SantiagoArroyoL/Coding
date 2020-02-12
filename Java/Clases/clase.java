import java.util.Scanner;
public class clase{
	public static void main(String[] args){

		int a = 0;
        int b = 0;
        int c = 0;
  	  	int cateto1 = 0;
  	  	int cateto2 = 0;
  	  	double h = 0;

    	double x = pitagoras();
		double y = general();

		System.out.println(x);
		System.out.println(y);
}







  public static double general(int a,int b, int c)  {
      //FORMULA GENREAL, LA CHICHARRONERA


      System.out.println("\n Introduce los valores de a,b,c para sacar el resultado de una operación con la formula general");

      System.out.println("Ingresa a: \n");
      Scanner puma1 = new Scanner(System.in);
      a = puma1.nextInt();


      System.out.println("Ingresa b: \n");
      Scanner puma2 = new Scanner(System.in);
      b = puma2.nextInt();

      System.out.println("Ingresa c: \n");
      Scanner puma3 = new Scanner(System.in);
      c = puma3.nextInt();

      double d = ((-b) + (Math.sqrt((b * b)) - (4 * a * c))) / (2 * a);

	  System.out.println("El resultado es: " + d);
	  return d;
  }



    public static double pitagoras(int cateto1, int cateto2, double h)  {

    //TEOREMA DE PITAGORAS


        System.out.println("Introduce los valores de a y de b para sacar la hipotenusa utilizando el teorema de pitagoras");

        System.out.println("Ingresa a: \n");
        Scanner puma4 = new Scanner(System.in);
        cateto1 = puma4.nextInt();


        System.out.println("Ingresa b: \n");
        Scanner puma5 = new Scanner(System.in);
        cateto2 = puma5.nextInt();

        h = Math.sqrt(cateto1 * cateto1 + cateto2 * cateto2);

		System.out.println("La hipotenusa vale: \n" + h);
		return h;
 }


}
