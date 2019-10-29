import java.io.BufferedWriter;
import java.io.BufferedReader;
import java.io.FileWriter;
import java.io.FileReader;
//Esta última librería es para no tener que andar poniendo try and catch
import java.io.IOException;

public class readwrite {
	public static void main(String[] args) throws IOException {

		// Todo este código es para que haga el nuevo archivo y escriba algo en el
		BufferedWriter write = new BufferedWriter(new FileWriter("C:/Users/santi/Desktop/text.txt"));

		write.write("Hello World");
		write.newLine();
		write.write("This is a test...");

		write.close();
		

		BufferedReader read = new BufferedReader(new FileReader("C:/Users/santi/Desktop/text.txt"));

		String line;
		while((line = read.readLine()) != null){
			System.out.println(line);
		}
	}
}
