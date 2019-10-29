public class for_loop{

	public static void main(String[] args) {

		String[] names = {"Ollie", "Alex", "Ellie", "Jason"};
		for (int x = 0; x < names.length; x++ ) {
			System.out.println(names[x]);
		}

		System.out.println("Enhanced for loop: ");
		//Enhanced for loop (each)

		for(String name : names){
			System.out.println(name);
		}
		// El ":" hace que vaya nombre por nombre en el array
	}
}
