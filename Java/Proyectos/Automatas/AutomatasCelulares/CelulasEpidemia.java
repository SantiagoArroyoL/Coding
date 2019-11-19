/**
 * Esta clase contiene las reglas de las Células del modelo de Epidemia, su vecindad y las probabilidades
 * Los bucles for y enhanced for en esta clase revisan los estados de cada celula en la vecindad y acorde a las reglas modifican el estado actual de la célula de [4]
 * @author: Arroyo Lozano Santiago
 * @version: 12/Sept/19 A
 */
import java.util.Random;

public class CelulasEpidemia{
	private int[] vecinos = new int[9];
	private int estado;
	int[] vecindad = new int[5];
	/**
	  * Constructor de CelulasEpidemia, que será el objeto con las reglas de las células de la simulación Epidemia
	  * @param vecinos Es el arreglo unidimensional en el que se almacenan los valores de la vecindad
	*/
	public CelulasEpidemia(int[] vecinos){
		this.vecinos = vecinos;
		estado = this.vecinos[4]; //El vecino 4 es la celda de en medio
		//Las células de la vecindad de Von Neuman son [1,3,4,5,7] por lo que debemos eliminar el resto
		vecindad[0] = this.vecinos[1];
		vecindad[1] = this.vecinos[3];
		vecindad[3] = this.vecinos[5];
		vecindad[4] = this.vecinos[7];



		//El objeto rand sólo será usado para crear una verdadera probabilidad
		Random rand = new Random();

		/*
		 * Estados:
		 * Susceptible: Valor = 0.
		 * Infeccioso: Valores en {1, ..., 7}.
		 * Inmune: Valores en {8, ..., 16}.
		*/

		switch (estado) {

			//Susceptible
			case 0:{
				for (int i : vecindad) {
					if (i < 8) {
							if (rand.nextInt(10) < 8) { //Probabilidad pc
								//80% de probabilidad de que se infecte
								estado = 1;
							}
					}else{
						estado = 0;
					}
				}
				break;
			}

			//Infecciosos
			case 1:{
				if (rand.nextInt(100) < 17) {
					//17% de probabilidad de que se aumente el valor
					estado++;
				}else {
					estado = 1;
				}
				break;
			}

			case 2:{
				if (rand.nextInt(100) < 17) {
					//17% de probabilidad de que se aumente el valor
					estado++;
				}else {
					estado = 2;
				}
				break;
			}

			case 3:{
				if (rand.nextInt(100) < 17) {
					//17% de probabilidad de que se aumente el valor
					estado+= 1;
				}else {
					estado = 3;
				}
				break;
			}

			case 4:{
				if (rand.nextInt(100) < 17) {
					//17% de probabilidad de que se aumente el valor
					estado++;
				}else {
					estado = 4;
				}
				break;
			}

			case 5:{
				if (rand.nextInt(100) < 17) {
					//17% de probabilidad de que se aumente el valor
					estado++;
				}else {
					estado = 5;
				}
				break;
			}

			case 6:{
				if (rand.nextInt(100) < 17) {
					//17% de probabilidad de que se aumente el valor
					estado++;
				}else {
					estado = 6;
				}
				break;
			}

			case 7:{
				if (rand.nextInt(100) < 17) {
					//17% de probabilidad de que se aumente el valor
					estado++;
				}else {
					estado = 7;
				}
				break;
			}

			//Inmunes
			case 8:{
				if (rand.nextInt(100) < 17) {
					//17% de probabilidad de que se aumente el valor
					estado++;
				}else{
					estado = 8;
				}
				break;
			}

			case 9:{
				if (rand.nextInt(100) < 17) {
					//17% de probabilidad de que se aumente el valor
					estado++;
				}else{
					estado = 9;
				}
				break;
			}

			case 10:{
				if (rand.nextInt(100) < 17) {
					//17% de probabilidad de que se aumente el valor
					estado++;
				}else{
					estado = 10;
				}
				break;
			}

			case 11:{
				if (rand.nextInt(100) < 17) {
					//17% de probabilidad de que se aumente el valor
					estado++;
				}else{
					estado = 11;
				}
				break;
			}

			case 12:{
				if (rand.nextInt(100) < 17) {
					//17% de probabilidad de que se aumente el valor
					estado++;
				}else{
					estado = 12;
				}
				break;
			}

			case 13:{
				if (rand.nextInt(100) < 17) {
					//17% de probabilidad de que se aumente el valor
					estado++;
				}else{
					estado = 13;
				}
				break;
			}

			case 14:{
				if (rand.nextInt(100) < 17) {
					//17% de probabilidad de que se aumente el valor
					estado++;
				}else{
					estado = 14;
				}
				break;
			}

			case 15:{
				if (rand.nextInt(100) < 17) {
					//17% de probabilidad de que se aumente el valor
					estado++;
				}else{
					estado = 15;
				}
				break;
			}

			case 16:{
				if (rand.nextInt(10) > 5) {
					//50% de probabilidad de que el virus mute y la célula deje de ser inmune, pasa a ser susceptibile otra vez
					estado = 0;
				}else{
					estado = 16;
				}
				break;
			}


		}//Cierre del Switch
		this.vecinos[4] = estado;
	}
	public int[] returnCelulas(){
		return this.vecinos;
	}//Cierre del método
    /**
     * Método que devuelve los estados de la vecindad
     * @return 9 células  almacenadas en un arreglo que ya fue analizado y actualizado para la siguiente generación
   */

}//Cierre de la clase
