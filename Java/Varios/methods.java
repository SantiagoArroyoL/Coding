class methods{

	public static void main(String[] args) {

		int answer = add(10, 5);
		print("The answer is " + answer);
	}

	static void print(String s){
		System.out.println(s);
	}

	static int add(int a, int b){
		int c = a + b;
		return c;
	}


}
