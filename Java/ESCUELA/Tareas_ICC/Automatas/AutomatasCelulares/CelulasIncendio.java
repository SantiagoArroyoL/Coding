/**
 * Esta clase contiene las reglas de las Células del modelo de Incendio su vecindad y las probabilidades
 * Los bucles for y enhanced for en esta clase revisan los estados de cada celula en la vecindad y acorde a las reglas modifican el estado actual de la célula de [4]
 * @author: Arroyo Lozano Santiago
 * @version: 12/Sept/19 A
 */
import java.util.Random;

public class CelulasIncendio{
	private int[] vecinos = new int[9]; //Usando la vecindad de Moore
	private int estado;

	/**
	  * Constructor de CelulasIncendio, que será el objeto con las reglas de las células de la simulación Incendio
	  * @param vecinos Es el arreglo unidimensional en el que se almacenan los valores de la vecindad
	*/
	public CelulasIncendio(int[] vecinos){
		this.vecinos = vecinos;
		estado = this.vecinos[4]; //El vecino 4 es la celda de en medio

		//El objeto rand sólo será usado para crear una verdadera probabilidad
		Random rand = new Random();

		/*
		 * Estados:
		 * Tierra = 0
		 * Fuego = 1
		 * Arbol = 2
		*/

		switch (estado) {
			//Tierra
			case 0: {
				if (rand.nextInt(2) == 0) { //Probabilidad pa(50%)
					estado = 0;
				}else {
					estado = 2;
				}
				break;
			}

			//Fuego
			case 1:{
				estado = 0;
				break;
			}

			//Arbol
			case 2:{
				for (int i : this.vecinos) {
						if (i == 1 && (rand.nextInt(10)-1 < 8)) {  //probabilidad g(70%)-1
						//Si hay fuego alrededor hay un 70%-1 de probabilidad de que se queme
						estado = 1;
					} else {
						estado = 2;
					}
				}
				// probabilidad f(20%)*(g(70%)-1) = 3/50
				if (rand.nextInt(10) < 3) {
					estado = 1;
				}
				break;
			}

		}//Cierre del switch

		this.vecinos[4] = estado;
	}
	public int[] returnCelulas(){
		return this.vecinos;
	}//Cierre del método
    /**
     * Método que devuelve los estados de la vecindad
     * @return 9 células  almacenadas en un arreglo que ya fue analizado y actualizado para la siguiente generación
     */
}
