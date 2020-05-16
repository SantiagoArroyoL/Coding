// oop = "Object Oriented Programing"
public class oop{

	public static void main(String[] args) {

		person person1 = new person("Ollie", 17, "17/03/95");
		person person2 = new person("Martin", 50, "13/02/63");
		person person3 = new person("Aidan", 10, "26/06/00");

		/* Asignar los paramaetros fuera del paréntesis
		person1.name = "Ollie";
		person1.age = 17;
		person1.dob = "17/03/95";

		person2.name = "Martin";
		person2.age = 50;
		person2.dob = "13/02/63";

		person3.name = "Aidan";
		person3.age = 10;
		person3.dob = "26/06/00";*/

		System.out.println("Person 1\n" + "Name: " + person1.name + "\n" + "Age: " + person1.age + "\n" + "Date of birth: " + person1.dob + "\n");

		System.out.println("Person 2\n" + "Name: " + person2.name + "\n" + "Age: " + person2.age + "\n" + "Date of birth: " + person2.dob + "\n");

		System.out.println("Person 3\n" + "Name: " + person3.name + "\n" + "Age: " + person3.age + "\n" + "Date of birth: " + person3.dob + "\n");
	}
}
