import java.awt.Frame;
import java.awt.Robot;
import java.awt.Panel;
import java.awt.Point;
import java.awt.Window;
import java.awt.Button;
import java.awt.event.*;
import java.awt.TextField;
import java.awt.MouseInfo;
import java.awt.Component;
import java.awt.Container;
import javax.swing.JFrame;

/**
 * @author Santiago Arroyo
 * @version 1.0
 * @date 22 dic 2021
 *
 * Clase que modela y acciona un bot que mueve el raton por un tiempo determinado
 */
class robomouse extends Frame implements ActionListener {
	/* Frame */
	static JFrame f;
	/* textField */
	static TextField x, y;
	/* constructor */
	robomouse(){}

	// main function
	public static void main(String args[]) {

		robomouse rm = new robomouse();

		f = new JFrame("robomouse");

		f.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

		//  textfield
		x = new TextField(7);
		y = new TextField(7);

		//  button
		Button b = new Button("OK");

		b.addActionListener(rm);

		Panel p = new Panel();

		// anadimos items al panel
		p.add(x);
		p.add(y);
		p.add(b);
		f.add(p);

		f.setSize(300, 300);

		f.show();
	}

	/**
	 * Metodo que revisa si ya se hizo la accion
	 *
	 * @param e El evento a manejar
	 */
	public void actionPerformed(ActionEvent e) {
		try {
			Robot r = new Robot();
			int xi1, yi1, xi, yi;

			// obtenemos info actual del mouse
			Point p = MouseInfo.getPointerInfo().getLocation();
			xi = p.x;
			yi = p.y;

			xi1 = Integer.parseInt(x.getText());
			yi1 = Integer.parseInt(y.getText());
			int i = xi, j = yi;

			// movemos lentamente el mouse
			while (i != xi1 || j != yi1) {
				r.mouseMove(i, j);
				if (i < xi1)
					i++;
				if (j < yi1)
					j++;
				if (i > xi1)
					i--;
				if (j > yi1)
					j--;
				// esperamos 100ms
				Thread.sleep(10);
			}
		}
		catch (Exception evt) {
			System.err.println(evt.getMessage());
		}
	}
}
