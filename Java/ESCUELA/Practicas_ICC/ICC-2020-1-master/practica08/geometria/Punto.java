package geometria;

/**
 * Representa un punto en el plano cartesiano (una pareja ordenada de dos números).
 * @since 1.0
 */ 
public class Punto {

    private double x;
    private double y;

    /**
     * Crea un punto con coordenadas (0, 0).
     * @since 1.0
     */
    public Punto() {
        x = y = 0;
    }

    /**
     * Crea un punto a partir de las coordenadas dadas.
     * @param x coordenada x
     * @param y coordenada y
     * @since 1.0
     */
    public Punto(double x, double y) {
        this.x = x;
        this.y = y;
    }

    /**
     * Desplaza este punto.
     * @param deltaX desplazamiento en el eje x
     * @param deltaY desplazamiento en el eje y
     * @since 1.0
     */
    public void desplazar(int deltaX, int deltaY) {
        x += deltaX;
        y += deltaY;
    }

    /**
     * Determina si tres puntos están alineados.
     * @param p1 punto que con p2 y <code>this</code> se determina si están alineados
     * @param p2 punto que con p1 y <code>this</code> se determina si están alineados
     * @return <code>true</code> si los puntos están alineados
     * @since 1.0
     */
    public boolean estanAlineados(Punto p1, Punto p2) {
        return (y - p1.y) * (p2.x - p1.x) == (p2.y - p1.y) * (x - p1.x);
    }

    /**
     * Calcula la distancia entre este punto y otro.
     * @param p punto respecto al cual se quiere determinar la distancia
     * @return distancia entre este punto y p
     * @since 1.0
     */
    public double distancia(Punto p) {
        return Math.sqrt((x - p.x) * (x - p.x) + (y - p.y) * (y - p.y));
    }

    /**
     * Obtiene la coordenada x de este punto.
     * @return la coordenada x
     * @since 1.0
     */
    public double getX() {
        return x;
    }

    /**
     * Asigna un valor a la coordenada x de este punto.
     * @param x nuevo valor para la coordenada x
     * @since 1.0
     */
    public void setX(double x) {
        this.x = x;
    }

    /**
     * Obtiene la coordenada y de este punto.
     * @return la coordenada y
     * @since 1.0
     */
    public double getY() {
        return y;
    }

    /**
     * Asigna un valor a la coordenada y de este punto.
     * @param y nuevo valor para la coordenada y
     * @since 1.0
     */
    public void setY(double y) {
        this.y = y;
    }

    /**
     * Asigna nuevos valores a este punto.
     * @param x nuevo valor para la coordenada x
     * @param y nuevo valor para la coordenada y
     * @since 1.0
     */
    public void setPunto(double x, double y) {
        this.x = x;
        this.y = y;
    }

    /**
     * Asigna el valor de un punto a este.
     * @param p punto a asignar
     * @since 1.0
     */
    public void setPunto(Punto p) {
        this.x = p.x;
        this.y = p.y;
    }

    /**
     * Determina si este punto es igual a otro.
     * @return <code>true</code> si son iguales
     * @since 1.0
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        Punto p = (Punto) o;
        return x == p.x && y == p.y;
    }

    /**
     * Convierte este punto a una cadena.
     * @return (x, y)
     * @since 1.0
     */
    @Override
    public String toString() {
        return String.format("(%.2f, %.2f)", x, y);
    }

}