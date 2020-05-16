public class multiarreglo {
	public static void main(String[] args) {
		//Multidimensional arrays
		float[][][] coordinates = new float [16][16][16];

		for (int x = 0; x < 16; x++) {
			System.out.println("First dimension" + x);
			for (int y = 0; y < 16; y++) {
				System.out.println("\tSecond dimension" + y);
				for (int z = 0; z < 16; z++ ) {
					System.out.println("\t\tThird dimension" + z);
					coordinates[x][y][z] = 3.14f;
				}
			}
		}



	}
}
