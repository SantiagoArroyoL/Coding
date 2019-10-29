public class string {
	public static void main (String[] args){
		String name = "OLlie";
		String name2 = "Santiago";

		//Se debe poner así y no con el "=" cuando comparas strings porque si no compara su valor como booleanos
		if(name.equals(name2)){
			System.out.println("Hello");
		}
		else {
			System.out.println("Adiou");
		}


		String sentence = "The quick brown fox jumped over the lazy dog";

		String[] data = sentence.split(" ", 3);

		System.out.println(data[2]);

		sentence = "                         The quick brown fox jumped over the lazy dog";

		System.out.println(sentence);

		sentence = sentence.trim();

		System.out.println(sentence);
	}
}
