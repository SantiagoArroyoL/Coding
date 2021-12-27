import java.awt.Font;
import java.awt.Point;
import java.awt.Robot;
import java.awt.Dimension;
import java.awt.MouseInfo;
import java.awt.FlowLayout;
import java.awt.GridLayout;
import java.awt.AWTException;
import java.awt.event.InputEvent;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import java.util.Random;

import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JButton;
import javax.swing.BoxLayout;
import javax.swing.JTextField;
import javax.swing.SwingUtilities;

/**
 * Clase ChristmasGift
 * Esta clase sera el programa que simula movimiento aleatorio del raton
 * Esta clase particularmente modela el JFrame, los controles
 * ademas se manda a llamar a RobotControl
 * @author Santiago Arroyo
 * @date 57/12/2021
 */
public class ChristmasGift {
	/* MAIN */
	public static void main(String args[]) {
		SwingUtilities.invokeLater(new Runnable() {
            @Override
            public void run() {
				final RobotControl robotControl = new RobotControl();
				/* JFrame */
				final JFrame f = new JFrame("Regalo para Laila");
				/* Terminamos el Thread cuando se cierre la ventana */
				f.setPreferredSize(new Dimension(1000, 300));
				f.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		        // f.getContentPane().setLayout(new GridLayout(1,2));
				/* Boton 1 */
		        final JButton startButton = new JButton("Empieza");
				startButton.setFont(new Font("Arial", Font.PLAIN, 60));
		        f.getContentPane().add(startButton);
				/* Boton 2 */
		        final JButton stopButton = new JButton("Termina");
				stopButton.setFont(new Font("Arial", Font.PLAIN, 60));
		        stopButton.setEnabled(false);
		        f.getContentPane().add(stopButton);
				f.setLayout(new GridLayout(1,2));
				// f.setLayout(new BoxLayout(f.getContentPane(),BoxLayout.Y_AXIS));

				/* Config botones*/
				startButton.addActionListener(new ActionListener() {
		            @Override
		            public void actionPerformed(ActionEvent e)
		            {
		                startButton.setEnabled(false);
		                stopButton.setEnabled(true);
		                robotControl.inicia();
		            }
		        });

		        stopButton.addActionListener(new ActionListener() {
		            @Override
		            public void actionPerformed(ActionEvent e)
		            {
		                robotControl.termina();
		                startButton.setEnabled(true);
		                stopButton.setEnabled(false);
		            }
		        });
		        f.pack();
		        f.setLocationRelativeTo(null);
		        f.setVisible(true);
            }
        });
	}
} // Cierre de clase ChristmasGift

/**
 * Clase RobotControl
 * Esta clase es la encargada de simular movimiento de raton
 * @author Santiago Arroyo
 * @date 57/12/2021
 */
class RobotControl {
    private volatile boolean running = false;
	private final Robot r;

	/**
	 * Constructor
	 * Inicializamos el robot
	 */
	public RobotControl() {
        try {
            r = new Robot();
        } catch (AWTException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

	/**
	 * metodo inicia
	 * En este metodo inicamos el thread y el bucle
	 */
	public void inicia() {
		Thread thread = new Thread(new Runnable() {
            @Override
            public void run() {
                running = true;
                bucle();
            }
        });
        thread.start();
	}

	/**
	 * Cambiamos nuestro booleano volatil a falso
	 */
	public void termina() {
		running = false;
	}

	/**
	 * metodo bucle
	 * Mientras el thread este corriendo movemos el mouse
	 */
	private void bucle() {
		try {
			while (running) {
				mueveMouse();
				Thread.sleep(5000); //5 segs
			}
		} catch (InterruptedException ie) {
			System.err.println("Oh no! Algo ha salido mal Lai\n" + ie.getMessage());
		}
	}

	/**
	 * metodo mueveMouse
	 * Este metodo es el encargada de mover el mouse aleatoriamente
	 */
	private void mueveMouse(){
		Random rand = new Random();
		int xi, yi;
		// rand.nextInt((max - min) + 1) + min
		int xi1 = rand.nextInt(1920);
		int yi1 = rand.nextInt(1080);

		// obtenemos info actual del mouse
		Point p = MouseInfo.getPointerInfo().getLocation();
		xi = p.x;
		yi = p.y;
		int i = xi, j = yi;

		// movemos lentamente el mouse
		while (i != xi1 || j != yi1) {
			try {
				r.mouseMove(i, j);
				if (i < xi1)
					i++;
				if (j < yi1)
					j++;
				if (i > xi1)
					i--;
				if (j > yi1)
					j--;
				// esperamos 10ms
				Thread.sleep(10);
			} catch (InterruptedException ie) {
				System.err.println("Oh no! Algo ha salido mal Lai\n" + ie.getMessage());
			}
		}
	}
}
