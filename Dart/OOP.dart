void main() {
  var wolverine = Heroe("Pene", "Regeneración", 100);
  // Heroe wolverine = new Heroe();
  // La palabra reservada "new" es opcional. Pero no manche joven, hágalo.
  print(wolverine);
}

/**
 * Nuestra primera clase en dart!
 */
class Heroe {
  /* atributos */
  String nombre;
  String poder;
  int vida;

  /**
   * Constructor
   */
  Heroe(String nombre, String poder, int vida) {
    this.nombre = nombre;
    this.poder = poder;
    this.vida = vida;
  }

  @override
  String toString() {
    // // TODO: implement toString
    // return super.toString();
    return 'nombre: ${this.nombre} - poder: ${this.poder}';
  }
}
