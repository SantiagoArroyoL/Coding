package mx.unam.ciencias.edd;

/**
 * Clase para métodos estáticos con dispersores de bytes.
 */
public class Dispersores {

    /* Constructor privado para evitar instanciación. */
    private Dispersores() {}

    /**
     * Función de dispersión XOR.
     * @param llave la llave a dispersar.
     * @return la dispersión de XOR de la llave.
     */
    public static int dispersaXOR(byte[] llave) {
        // Aquí va su código.
		if (llave.length % 4 != 0) {
			int n = llave.length;
			while (n % 4 != 0)
				n++;
			byte[] temp = llave;
			llave = new byte[n];
			for (int i = 0; i < temp.length; i++)
				llave[i] = temp[i];
			for (int i = temp.length; i < n; i++)
				llave[i] = 0;
		}
		int r  = 0;
		for (int i = 0; i < llave.length; i+=4)
			r ^= combinaBigEndian(llave[i],llave[i+1],llave[i+2],llave[i+3]);
		return r;
    }

    /**
     * Función de dispersión de Bob Jenkins.
     * @param llave la llave a dispersar.
     * @return la dispersión de Bob Jenkins de la llave.
     */
    public static int dispersaBJ(byte[] llave) {
        // Aquí va su código.
		int n = llave.length, i = 0;
		int a = 0x9E3779B9, b = 0x9E3779B9, c = 0xFFFFFFFF;
		while (n >= 12) {
			a += combinaLittleEndian(llave[i],llave[i+1],llave[i+2],llave[i+3]);
			b += combinaLittleEndian(llave[i+4],llave[i+5],llave[i+6],llave[i+7]);
			c += combinaLittleEndian(llave[i+8],llave[i+9],llave[i+10],llave[i+11]);
			int[] temp = mezcla(a,b,c);
			a = temp[0]; b = temp[1]; c = temp[2];
			i += 12;
			n -= 12;
		}
		c += llave.length;
		switch (n) {
			/* C */
			case 11: c += (llave[i+10] & 0xFF) << 24;
			case 10: c += (llave[i+9] & 0xFF) << 16;
			case  9: c += (llave[i+8] & 0xFF) <<  8;
			/* B */
			case  8: b += (llave[i+7] & 0xFF) << 24;
			case  7: b += (llave[i+6] & 0xFF) << 16;
			case  6: b += (llave[i+5] & 0xFF) <<  8;
			case  5: b += (llave[i+4] & 0xFF);
			/* A */
			case  4: a += (llave[i+3] & 0xFF) << 24;
			case  3: a += (llave[i+2] & 0xFF) << 16;
			case  2: a += (llave[i+1] & 0xFF) <<  8;
			case  1: a += (llave[i] & 0xFF);
		}
		int[] temp = mezcla(a,b,c);
		return temp[2];
    }

	/**
	 * Método que mezcla 3 enteros entre sí siguiendo el algoritmo de Bob Jenkins
	 * @param a Un entero a mezclar
	 * @param b Un entero a mezclar
	 * @param c Un entero a mezclar
	 * @return Siempre regresa un arreglo que contiene los tres enteros mezclados
	 */
	private static int[] mezcla(int a, int b, int c) {
		/* Inicia primer diagrama */
		a -= b;		a -= c; 	a ^= (c >>> 13);
        b -= c; 	b -= a;		b ^= (a << 8);
        c -= a; 	c -= b;		c ^= (b >>> 13);
		/* Inicia segundo diagrama */
        a -= b;		a -= c;		a ^= (c >>> 12);
        b -= c;		b -= a;		b ^= (a << 16);
        c -= a;		c -= b;		c ^= (b >>> 5);
		/* Inicia tercer diagrama */
        a -= b;		a -= c;		a ^= (c >>> 3);
        b -= c;		b -= a;		b ^= (a << 10);
        c -= a;		c -= b;		c ^= (b >>> 15);
		return new int[]{a,b,c};
	}

    /**
     * Función de dispersión Daniel J. Bernstein.
     * @param llave la llave a dispersar.
     * @return la dispersión de Daniel Bernstein de la llave.
     */
    public static int dispersaDJB(byte[] llave) {
        // Aquí va su código.
		int h = 5381;
		for (int i = 0; i <  llave.length; i++)
			h += (h << 5) + (llave[i] & 0xFF);
		return h;
    }

	/***************************************FuncionesAuxiliares********************************************/

	/**
	 * Método auxiliar que combina cuatro bytes a un entero usando el esquema big-endian
	 * @param a El byte más significativo
	 * @param b El byte que le sigue
	 * @param c El byte que le sigue
	 * @param d El byte menos significativo
	 * @return La cambinación de los cuatro bytes a un entero
	 */
	private static int combinaBigEndian(byte a, byte b, byte c, byte d) {
		return ((a & 0xFF) << 24) | ((b & 0xFF) << 16) | ((c & 0xFF) << 8) | ((d & 0xFF));
	}

	/**
	 * Método auxiliar que combina cuatro bytes a un entero usando el esquema little-endian
	 * @param a El byte menos significativo
	 * @param b El byte que le sigue
	 * @param c El byte que le sigue
	 * @param d El byte más significativo
	 * @return La cambinación de los cuatro bytes a un entero
	 */
	private static int combinaLittleEndian(byte a, byte b, byte c, byte d) {
		return ((a & 0xFF)) | ((b & 0xFF) << 8) | ((c & 0xFF) << 16) | ((d & 0xFF) << 24);
	}
}
