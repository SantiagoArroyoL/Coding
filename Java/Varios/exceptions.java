public class exceptions{
	public static void main(String[] args) {

		int[] array = {0, 1};

		try{

			System.out.println(array[2]);
		} catch(Exception e){
			System.err.println("Could not access array element");
			e.printStackTrace(System.err);
		}

	}
}
