
public class swenum {

	enum Days{
		MONDAY, TUESDAY, WEDNESDAY, THURSDAY, FRIDAY, SATURDAY, SUNDAY;
	}
	//Debes ponerle el mismo nombre poruqe como tal no es un method, es un aextensión de class
	public swenum()  {

		Days day = Days.SATURDAY;

		switch (day) {
			case MONDAY;
				break;
		switch (day) {
			case WEDNESDAY;
				break;
		switch (day) {
			case TUESDAY;
				break;
		switch (day) {
			case MONDAY;
				break;
		}
		/*
		int a = 10;

		switch(a){
			case 10:
				System.out.println("a is 10");
				break;
			case 5:
				System.out.println("a is 5");
				break;
			default:
				System.out.println("a is not a valid value");
				break;
		}
		*/
	}




	public static void main(String[] args) {
		new swenum();
	}
}
