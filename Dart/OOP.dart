void main() {
  var wolverine = Heroe(nombre: "Logan", poder: "Regeneración", vida: 100);
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

  // /**
  //  * Constructor
  //  */
  // Heroe(String nombre, String poder, int vida) {
  //   this.nombre = nombre;
  //   this.poder = poder;
  //   this.vida = vida;
  // }

  Heroe({this.nombre, this.poder, this.vida}); //wow

  @override
  String toString() => 'nombre: ${this.nombre} - poder: ${this.poder}';
}
