import java.util.Random;

public class Tablero{
		
	private Celda [][] tablero;
	private int n;
	private int m;
	

	/**
	 * Inicia el tablero con nuevas celdas cubiertas.
	 * @param n Las filas
	 * @param m Las columnas
	*/
	public Tablero(int n, int m){
		this.n = (n>=2)? n:2;
		this.m = (m>=2)? m:2;
		tablero = new Celda[this.n][this.m];
		for (int i=0;i<this.n ;i++ ) {
			for (int j = 0;j<this.m ;j++ ) {
				tablero[i][j] = new Celda();
			}
		}
	}

	/**
	 * Recibe las coordenadas y de una celda y verifica si se adivinó el número.
	 */
	public boolean adivinoCelda(int i, int j, int numero){
		if(i>=0 && i < this.n && j >=0 && j<this.m){
			if(tablero[0][0].descubierta){
				System.out.println("Ya abriste esta celda");
				return false;
			}else{
				tablero[i][j].descubierta = true;
				return numero == tablero[i][j].numero;
			}
		}
		System.out.println("Los indices no son validos");
		return false;
	}

	/**
	 * Descubre todas las celdas.
	 *
	 */
	public void descubreCeldas(){
		for (int i=0;i < this.n ;i++ ) {
			for(int j=0; j < this.m;j++ ){
				tablero[i][j].descubierta = true;
			}
		}
	}

	public String toString(){
		String tab = "";
		for (int i=0;i < this.n ;i++ ) {
			for(int j=0; j < this.m;j++ ){
				tab += tablero[i][j];
			}
			tab += "\n";
		}
		return tab;
	}

	private class Celda {

		public boolean descubierta;
		public int numero;

		/**
		 * Crea una celda cubierta y con número entre 0 y 11.
		 */
		public Celda(){
			this.descubierta= false;
			Random r = new Random();
			this.numero = r.nextInt(4);
		}

		public String toString(){
			if(descubierta){
				if(numero == 10 )
					return "|10|";
				return String.format("| %d|",numero);
			}
			return "|  |";
		}
	}
}