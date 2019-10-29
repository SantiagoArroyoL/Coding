public class PruebaHora {

	public static void main(String[] args) {
		/*Usa el primer constructor*/
		Hora hora1 = new Hora();
		/*Usar el segundo*/
		Hora hora2 = new Hora(12,1,30);
		/*Constructor 3*/
		Hora hora3 = new Hora(hora2);

		hora2.formatoDoce();

		System.out.println(hora2.getHora());
		System.out.println("Hora1: " + hora1);
		System.out.println("Hora2: " + hora2);
		System.out.println("Hora3: " + hora3);

		}
}
