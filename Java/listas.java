import java.util.ArrayList;
public class listas {
	public static void main(String[] args) {

		ArrayList list = new ArrayList();

		String name1 = "Ollie";
		String name2 = "Santiago";

		list.add(name1);
		list.add(name2);

		System.out.println(list.get(0));
		System.out.println(list.get(1));

		list.remove(0);

		System.out.println(list.get(0));
	}
}
