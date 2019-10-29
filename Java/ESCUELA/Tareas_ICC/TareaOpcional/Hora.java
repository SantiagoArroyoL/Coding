/**
 * Esta clase simula el comportamiento de una hora.
 * @author Santiago Arroyo Lozano
 * @version 1.0
 *
 */
public class Hora {

	/*Simula los minutos*/
	private int minutos;
	/*Simula los segundos*/
	private int segundos;
	/*Simula las horas*/
	private int horas;
	/*Confirma si es Formato de 24 horas*/
	private boolean esFormato24;
	/*Da formato a las horas*/
	private String horasF;
	/*Da formato a los minutos*/
	private String minsF;
	/*Da formato a los segundos*/
	private String segsF;

	/**
	 * Constructor por omisión, con formato de 24 horas por default
	 */
	public Hora (){
		this.horas = 0;
		this.minutos = 0;
		this.segundos = 0;
	}

	/**
	 * Constructor que genera una hora a partir de 3 enteros.
	 * Formato de 24 horas por default.
	 * Si la hora, minutos o segundos no son válidos, se inician en 0.
	 * @param horas Las horas definidas por el usuario.
	 * @param minutos Los minutos.
	 * @param segundos Los segundos
	 */
	public Hora (int horas,int minutos, int segundos){
		if(horas >= 0 && horas <24){
			this.horas = horas;
		}else {
			System.out.println("Las horas están mal");
			this.horas = 0;
		}
		if(minutos >= 0 && minutos <60){
			this.minutos = minutos;
		}else {
			System.out.println("Los minutos están mal");
			this.minutos= 0;
		}
		if(segundos >= 0 && segundos <60){
			this.segundos= segundos;
		}else {
			System.out.println("Los segundos están mal");
			this.segundos = 0;
		}

	}

	/**
	 * Constructor de copia
	 * @param horaNueva La hora nueva de la cual se construirá.
	 */
	public Hora (Hora horaNueva){
		this.horas = horaNueva.getHora();
		this.minutos = horaNueva.getMinutos();
		this.segundos = horaNueva.getSegundos();
	}

	/**
	 * Modifica la hora
	 * @param nuevaHora La nueva hora.
	 */
	public void setHoras(int nuevaHora){
		if(nuevaHora >= 0 && nuevaHora <24){
			this.horas = nuevaHora;
		}else {
			System.out.println("Las horas están mal");
			this.horas = 0;
		}
	}

	/**
	 * Modifica los minutos
	 * @param nuevosMinutos Los nuevos minutos.
	 */
	public void setMinutos(int nuevosMinutos){
		if(nuevosMinutos >= 0 && nuevosMinutos <24){
			this.minutos = nuevosMinutos;
		}else {
			System.out.println("Los minutos están mal");
			this.minutos = 0;
		}
	}

	/**
	 * Modifica los segundos
	 * @param nuevosSegundos Los nuevos segundos.
	 */
	public void setSegundos(int nuevosSegundos){
		if(nuevosSegundos >= 0 && nuevosSegundos <24){
			this.segundos = nuevosSegundos;
		}else {
			System.out.println("Los segundos están mal");
			this.segundos = 0;
		}
	}

	/**
	 * Método que devuelve la hora.
	 * @return La hora en formato de 24 horas.
	 */
	public int getHora(){
		return this.horas;
	}

	/**
	 * Regresa los  minutos
	 * @return Los minutos.
	 */
	public int getMinutos(){
		return this.minutos;
	}

	/**
	 * regresa los segundos
	 * @return los segundos.
	 */
	public int getSegundos(){
		return this.segundos;
	}

	/**
	 * Metodo para cambiar el formato a 12 horas
	 * @return Valor booleano -- Si es false entonces el formato es de 12 horas
	 */
	 public boolean formatoDoce(){
		return this.esFormato24 = false;
	 }

	/**
 	* Metodo para cambiar el formato a 24 horas
 	* @return Valor booleano -- Si es true entonces el formato es de 24 horas
 	*/
 	public boolean formatoVeinte(){
 		return this.esFormato24 = true;
 	}

	/**
	 * Devuelve la hora en formato 00:00:00 , ajustando si es formato de 24 o 12 horas
	 * @return Un arreglo con todas las variables en su debido formato
	 */
	 private String[] formatoHora(){
		if (!esFormato24 && this.horas == 0) {
		   this.horas = 12;
	   }
	   if (this.horas < 10) {
		   this.horasF = "0" + this.horas;
	   }else{
		   this.horasF = String.valueOf(this.horas);
	   }
		if (this.minutos < 10) {
		   this.minsF = "0" + this.minutos;
	   }else{
		   this.minsF = String.valueOf(this.minutos);
	   }
		if (this.segundos < 10) {
		   this.segsF = "0" + this.segundos;
	   }else{
		   this.segsF = String.valueOf(this.segundos);
	   }
		return new String[] {this.horasF, this.minsF, this.segsF};
	 }

	 /**
	 * Devuelve una representación en cadena del objeto, con formato 00:00:00
	 * Si el formato es de 12 horas regresará al final con la etiqueta am o pm
	 * @return La hora
	 */
	 public String toString(){
		 if (esFormato24) {
			formatoHora();
			return "La hora es " + this.horasF + ":" + this.minsF +":"+ this.segsF;
		 }else{
			if (this.horas >= 12) {
				this.horas = this.horas - 12;
				formatoHora();
				return "La hora es " + this.horasF + ":" + this.minsF +":"+ this.segsF + " pm";
			}else{
				formatoHora();
				return "La hora es " + this.horasF + ":" + this.minsF +":"+ this.segsF + " am";
			}
		 }
	}


}
