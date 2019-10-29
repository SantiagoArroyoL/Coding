/**
 * Este programa simula una epidemia y un incendio forestal usando los automatass celulares y la POO
 * Este archivo fue creado sólo para la parte gráfica y no contiene ni las reglas de las células ni de la vecindad, lo que sí contiene es el manejo del arreglo bidimensional con el que se formó la vecindad
 * La clase GUI configura el JFRame, llama a  los objetos requeridos e inicializa el arreglo bidimensional que se encargará de manejar la vecindad
 * Las lineas  119, 132, 134 están comentadas, si quitamos el comentario de estas lineas el programa se imprimirá en la consola para así poder ver la matriz con números y comprobar que todo esté en orden
 * A partir de la linea 176 empieza la segunda clase de este archivo, la clase Board
 * @author: Arroyo Lozano Santiago
 * @version: 12/Sept/19 A
 */
import java.awt.*;
import javax.swing.*;
import java.util.Timer;
import java.util.Random;
import java.util.TimerTask;

public class GUI extends JFrame {

	//Declaración de variables y arreglos
	private int[][] arregloCelular;
	private int nuevaX;
	private int nuevaY;
	private int[] tempCel = new int[9];
	private int[] nuevasCelulas = new int[9];

	public GUI(int tamañoX, int tamañoY, String simulacion) {
		//aqui debemos llamar a todos los métodos que vamos a utilizar
		super("Automatas Celulares en Java");
		super.frameInit();
		crearCelulas(tamañoX,tamañoY,simulacion);
		dibujarCelulas(simulacion);
		setLayout(null);
		setContentPane(new Board(tamañoX, tamañoY,arregloCelular,simulacion));
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		pack();
		setVisible(true);
		setResizable(false);
		setDefaultLookAndFeelDecorated(true); //siempre me dio risa el nombre de este setter
		setSize(tamañoY,tamañoX+22);

		//El tamaño de las variables se debe dividir entre cinco porque cada celula mide 5 pixeles (El valor de X y el valor de y están en pixeles)
		nuevaX = tamañoX/5;
		nuevaY = tamañoY/5;
	}

	/**
	  * En este método crearemos la matriz acorde con las i
	  * @param Simular Cadena que indica la simulación a realizar
	*/
	public void dibujarCelulas(String simular) {
		for (int i = 0; i < nuevaX; i++) {
			for (int j = 0; j < nuevaY; j++) {

				int tempNum = 0;

				//Para cada valor de la variable iX que va de 1 a -1 se realiza por completo la segunda instrucción for que consiste en hacer la misma cuenta
				for (int iX = -1; iX <= 1; iX++) {
					for (int jX = -1; jX <= 1; jX++) {

						//Para no tener que escribir tanto creamos dos variables temporales
						int valorX = i+iX;
						int valorY = j+jX;

						//Por cada valor de iX y jX, ya sea 1 o -1 generaremos los renglones de la matriz
						if (valorX == -1) {
							valorX = nuevaX-1;
						} else if (valorX == nuevaX) {
							valorX = 0;
						}

						if (valorY == -1) {
							valorY = nuevaY-1;
						} else if (valorY == nuevaY) {
							valorY = 0;
						}

						//Guardamos temporalmente el valor de este arreglo bidimensional, que está incompleto, ya que faltan los valores de Y
						tempCel[tempNum] = arregloCelular[valorX][valorY];
						tempNum++;

					}
				}


				for (int iY = -1; iY <= 1; iY++) {
					for (int jY = -1; jY <= 1; jY++) {

						int valorX = i+iY;
						int valorY = j+jY;

						//Por cada valor de iY y jY, ya sea 1 o -1 generaremos las columnas de la matriz
						if (valorX == -1) {
							valorX = nuevaX-1;
						} else if (valorX == nuevaX) {
							valorX = 0;
						}

						if (valorY == -1) {
							valorY = nuevaY-1;
						} else if (valorY == nuevaY) {
							valorY = 0;
						}

						//Comprobamos qué simulación se va a ejecutar y creamos objetos acorde a ella
						String Incendio = new String("Incendio");
						String Epidemia = new String("Epidemia");

						if (Incendio.equals(simular)) {
							CelulasIncendio myCels = new CelulasIncendio(tempCel);
							nuevasCelulas = myCels.returnCelulas();
						}else if (Epidemia.equals(simular)) {
							CelulasEpidemia myCels = new CelulasEpidemia(tempCel);
							nuevasCelulas = myCels.returnCelulas();
						}

						//Se le asigna el valor el arreglo bidimensional creado al arreglo de celulas (La vecindad)
						arregloCelular[valorX][valorY] = nuevasCelulas[(iY+1)*3+(jY+1)];
					}
				}
				//System.out.println();
			}
		}
	} // Cierre del método

	/**
	   * Método para controlar el tiempo (Qué tan rápido avanzará la simulación)
	   * @param tiempo El parámetro tiempo define el intervalo  de tiempo en milisegundos
	   * @param simular El parámetro simular es la cadena que define a qué simulación vamos a acceder
	*/
	public void Reloj(int tiempo, String simular) {
		TimerTask relojito = new TimerTask() {
			public void run() {
				//imprimirCelulas(arregloCelular);
				dibujarCelulas(simular);
				//imprimirCelulas(arregloCelular);
			}
		};//Cierre del constructor de relojito
		Timer crono = new Timer();
		crono.schedule(relojito,0,tiempo);
	} //Cierre del metodo

	/**
	   * Método para crear el arreglo de células
	   * @param arregloX El parámetro es el arreglo que está en x para generar el arreglo bidimensional
	   * @param arregloY El parámetro es el arreglo que está en y para generar el arreglo bidimensional
		* @param simular El parámetro simular es la cadena que define a qué simulación vamos a acceder
	*/
	public void crearCelulas(int arregloX, int arregloY, String simular) {

		Random rand = new Random();
		String Incendio = new String("Incendio");
		String Epidemia = new String("Epidemia");

		int tempX = arregloX/5;
		int tempY = arregloY/5;

		arregloCelular = new int[tempX][tempY];

		//Valor de inicio de la matriz:
		for (int i = 0; i < tempX; i++) {
			for (int j = 0; j < tempY; j++) {
				if (Incendio.equals(simular)) {
					arregloCelular[i][j] = 0;//Incendio, se inicia con tierra y con arboles(porque el estado 0 tiene un 50% de probabilidad de ser generado con arboles, por lo que al crearse hay arboles y tierra, de igual manera varios arboles tienen la probabilidad de incendiarse espontaneamente desde la primera generación)
				}else if (Epidemia.equals(simular)) {
					arregloCelular[i][j] = 1;//Epidemia, todos son infecciosos al empezar la simulación (estado 1)
				}
			}
		}
	} //Cierre del método

	/**
	  * Método para imprimir las celulas en la consola
	  * @param miArreglo Es el arreglo bidimensional (La matriz)
	*/
	public void imprimirCelulas(int[][] miArreglo) {
		for (int[] arreglo1D : miArreglo) {
			System.out.println();
			for (int i : arreglo1D) {
				System.out.print(i + " ");
			}
		}
	}//Cierre del método

} //Cierre de la clase GUI

/************************************************************************************************************************************************/

/**
 * Esta Clase Board es la encargada de configurar el JPanel y manejar los objetos Graphics, que muestra la malla y las células en el JFrame que ya configuramos en la clase GUI
 * @author: Arroyo Lozano Santiago
 * @version: 12/Sept/19 A
 */
class Board extends JPanel {

	//Declaración de variables y arreglos
	private int[][] arregloCelular;
	private int x;
	private int y;
	private String simular;

	/**
	  * Constructor de Board, que será la malla y pintará las células de colores
	  * @param x Son los parámetros que nos dicen donde están las celulas y en qué estado de qué vecindad
	  * @param y Son los parámetros que nos dicen donde están las celulas y en qué estado de qué vecindad
	  * @param arregloCelular Este parámetro es la vecindad
	  * @param simular El parámetro simular es la cadena que define a qué simulación vamos a acceder
	*/
	public Board(int x, int y, int[][] arregloCelular, String simular){

		//Para no confundirme la dejamos con el mismo nombre
		this.arregloCelular = arregloCelular;
		this.x = x/5;
		this.y = y/5;
		this.simular = simular;
		//Tamaño del arreglo porque son 5 pixeles

		JPanel boardPanel = new JPanel();
		boardPanel.setLayout(null);
		//Llamamos al objeto sin nombre de la clase Dimension, que literalmente le da dimensiones al JPanel
		boardPanel.setPreferredSize(new Dimension(x,y));
	}//Cierre del constructor

	/**
	   * Método para pintar de color cada célula dependiendo de su estado
	   * @param g El parámetro g es el objeto de la clase Graphics que ya tiene métodos prediseñados que vamos a utilizar
	*/
	public void paintComponent(Graphics g){
		String Incendio = new String();
		String Epidemia = new String();
		Incendio = "Incendio";
		Epidemia = "Epidemia";
		if (Incendio.equals(simular)) {
			for (int i = 0; i < this.x; i++) {
				for (int j = 0; j < this.y; j++) {

					//Fuego 1
					if (arregloCelular[i][j] == 1) {
						g.setColor(Color.red);
					}

					//Arbol 2
					if (arregloCelular[i][j] == 2) {
						g.setColor(Color.green);
					}

					//Tierra 0
					if (arregloCelular[i][j] == 0) {
						g.setColor(Color.gray);
					}
					g.fill3DRect(j*5, i*5, 5,5, true);
					//Se multiplica por 5 para que se mueva 5 pixeles y no solo 1 y no se sobrelapen
					//Si no se llena la recta en 3D no sale la cuadricula porque entonces hace que cada color sea pixeles bidimensionales sin separación alguna
				}
			}
		}else if (Epidemia.equals(simular)) {
			for (int i = 0; i < this.x; i++) {
				for (int j = 0; j < this.x; j++) {

					//Susceptible 0
					if (arregloCelular[i][j] == 0) {
						g.setColor(Color.yellow);
					}

					//Infecciosos Valores en {1, ..., 7}.
					if (arregloCelular[i][j] > 0 && arregloCelular[i][j] < 8) {
						g.setColor(Color.red);
					}

					//Inmunes Valores en {8, ..., 16}.
					if (arregloCelular[i][j] >= 8) {
						g.setColor(Color.white);
					}
					//fill3DRect nos proporciona la malla negra, 2DRect no la dibuja
					g.fill3DRect(j*5, i*5, 5,5, true);
				}
			}
		}
		repaint();
	} // Cierre del método
} //Cierre de la clase Board
