package mx.unam.ciencias.edd.proyecto2;

import mx.unam.ciencias.edd.Lista;

/**
 * Clase encargada de manejar las banderas contenidas en el arreglo de entrada
 * @author Arroyo Lozano Santiago
 * @version 1.0
 * @since 25/03/2020.
 */
public class Banderas {

	private String identificador = "";

	/**
	 * Método que regresa el identificador
	 * @return String que contiene el valor del identificador
	 */
	public String getIdentificador() {
		return identificador;
	}

	public boolean esIdentificador(String temp) {
		if (temp == null ^ identificador.equals(temp))
	        return false;
	    try {
	        int d = Integer.parseInt(temp);
	    } catch (NumberFormatException nfe) {
	        return true;
	    }
	    return false;
	}

	/**
	 * Método Auxiliar que identifica con qué clase estamos trabajando
	 * Notemos que si hay un # ignoramos esa línea
	 * Sabemos que la primera entrada sin # del arreglo debe ser el nombre de la clase
	 * Por lo tanto a la primera linea sin # que encontremos terminamos
	 * @param args El arreglo a recorrer
	 */
	public void identifica(String[] args) {
		for (int i = 0; i < args.length; i++)
			if (!contieneAlmohadillas(args[i])) {
				identificador = args[i];
				return;
			}
	}

	/**
	 * Método que revisa si el arreglo recibido va a ser de la forma estándar o no
     * @param args el arreglo a revisar
     * @return true en caso de que sea una entrada estandar - false en caso contrario
     */
	public boolean checaEstandar(String[] args) {
		if (args.length == 0)
			return true;
		return false;
	}

	/**
	 * Método que elimina las banderas e identificador si es que existen del arreglo
	 * @param args El arreglo a manipular
	 * @return Una lista que contiene los mismos elementos del arreglo original menos las Banderas
	 */
	public Lista<String> eliminaAlmohadillas(String[] args) {
		Lista<String> lista = new Lista<>();
		for (String str : args)
		if (!str.contains("#"))
			lista.agrega(str);
		return lista;
	}

	public boolean contieneAlmohadillas(String str) {
		return str.contains("#");
	}

	public Lista<Integer> interpretaElementos(String cadena) {
		String[] elementos = cadena.split(" ");
		Lista<Integer> nuevaLista = new Lista<>();
		for (int i = 1; i < elementos.length; i++) {
			try {
				// System.out.println(elementos[i]);
				nuevaLista.agrega(Integer.parseInt(elementos[i]));
			} catch (NumberFormatException e) {
				System.out.println("Asegurate de escribir sólo números");
				System.exit(-1);
			}
		}
		return nuevaLista;
	}

	// private boolean esEspacio(String str) {
	// 	if (str.)
	// }

}//Cierre de la clase Banderas
