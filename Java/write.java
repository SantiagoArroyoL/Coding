import java.util.Scanner;
public class write{
	public static void main(String[] args) {

		Scanner x = new Scanner(System.in);

		System.out.println("What is your name");

		String name = x.nextLine();

		System.out.println("How old are you?");

		int age = 0;
		boolean gotIt = false;
		while (!gotIt) {
			try{
				age = x.nextInt();
				gotIt = true;
			} catch (Exception ex) {
				System.out.println("That is not a valid number");
				x.next();
				continue;
			}
		}

		System.out.println("Your name is " + name + " and your age is " + age);
	}
}
