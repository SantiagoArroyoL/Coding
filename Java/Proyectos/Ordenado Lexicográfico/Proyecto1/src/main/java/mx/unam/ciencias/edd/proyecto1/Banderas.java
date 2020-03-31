package mx.unam.ciencias.edd.proyecto1;

import mx.unam.ciencias.edd.Lista;

/**
 * Clase encargada de manejar las banderas contenidas en el arreglo de entrada
 * @author Arroyo Lozano Santiago
 * @version 1.0
 * @since 25/03/2020.
 */
public class Banderas {

	/* Esta cadena sólo será inicializada si se usa la bandera especial*/
	private String identificador;

	/**
	 * Método que regresa el identificador
	 * @return String que contiene el valor del identificador
	 */
	public String getIdentificdor() {
		return identificador;
	}

	/**
	 * Método que nos indica si la cadena recibida es una bandera o no
	 * @param temp La cadena a evaluar
	 * @return true en caso de que sea una bandera - false en caso contrario
	 */
	public boolean esBandera(String temp) {
		return temp.equals("-r") || temp.equals("-o");
	}

	/**
	 * Método que revisa si el arreglo contiene la bandera de reversa
	 * @param args el arreglo a revisar
	 * @return true en caso de que contenga la bandera reversa - false en caso contrario
	 */
	public boolean checaReversa(String[] args) {
		final String reversa = "-r";
		for (String str : args)
			if (str.equals(reversa))
				return true;
		return false;
	}

	/**
	 * Método que revisa si el arreglo contiene la bandera de especial
     * @param args el arreglo a revisar
     * @return true en caso de que contenga la bandera especial - false en caso contrario
     */
	public boolean checaEspecial(String[] args) {
		final String especial = "-o";
		for (int i = 0; i < args.length; i++)
			if (especial.equals(args[i])){
				try {
					identificador = args[i+1];
				} catch (ArrayIndexOutOfBoundsException e) {
					System.out.println("No introduciste un identificador");
					System.exit(-1);
				}
				return true;
			}
		return false;
	}

	/**
	 * Método que revisa si el arreglo recibido va a ser de la forma estándar o no
     * @param args el arreglo a revisar
	 * @param esReversa el valor booleano que indica si el arreglo contiene la bandera reversa o no
	 * @param esEspecial el valor booleano que indica si el arreglo contiene la bandera especial o no
     * @return true en caso de que sea una entrada estandar - false en caso contrario
     */
	public boolean checaEstandar(String[] args, boolean esReversa, boolean esEspecial) {
		if (args.length == 0 || (args.length == 1 && esReversa))
			return true;
		if (args.length == 2 && esEspecial)
			return true;
		if (args.length == 3 && (esEspecial && esReversa) )
			return true;
		return false;
	}

	/**
	 * Método que elimina las banderas e identificador si es que existen del arreglo
	 * @param args El arreglo a manipular
	 * @return Una lista que contiene los mismos elementos del arreglo original menos las Banderas
	 */
	public Lista<String> eliminaBanderas(String[] args) {
		Lista<String> lista = new Lista();
		for (String str : args)
			if (!esBandera(str) && !str.equals(identificador))
				lista.agrega(str);
		return lista;
	}

}//Cierre de la clase Banderas
