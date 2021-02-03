/**
 * Aprendamos Dart!
 * 
 * También jugaremos con cositas varias que nos servirán más adelante
 * Ejemplo: variables, tipos de dato, concatenación, estructuras de datos, etc
 * Ojo piojo, Dart usa punto y coma como Java
 * 
 * */
import 'dart:math';

void main() {
  print("Hola Mundo");

  var s = "concatenar?";
  var sal = "Santiago";

  //***********CONCATENAMOS*******
  print("Sabes como $s");
  // Dos formas válidas de concatenar? WOW
  print("Me llamo " + sal);

  // TIPOS DE DATOS
  // **********NÚMEROS, ENTEROS Y DOUBLE, CÓMO USARLOS EN CADENAS*********
  int empleados = 1234;
  int muertos = 13;
  double pi = 3.141592;
  var numero = 1.0; //double
  int r = 5;

  print(
      "Nos quedan: $empleados-$muertos empleados, osease ${empleados - muertos}");
  print("El área de un circulo con radio $r es ${pi * pow(r, 2)}");
  // Ya hasta usamos exponenciales! Son idénticos a Java

  // **************STRING************
  // Los String funcionan igual que en Python
  String arr = "Arroyo";
  String loz = 'Lozano';
  print(arr[0]);
  print(arr[arr.length -
      1]); // Tienen las mismas propiedades que en Java, pues String es la clase

  // ********BOOLEANOS Y CONDICIONALES*********
  bool activado = true;
  print(activado);

  if (activado) {
    print("Esto es redundante pero funciona");
  } else {
    print("Nunca llegaremos aquí");
  }

  // ********** LISTAS ************
  // List<E>, como en Java, usa genéricos
  List numeros = [
    1,
    2,
    3,
    4
  ]; // No hay arreglos, sólo listas que parecen arreglos
  // Si no defino el genérico, se vuelve una lista dinámica, lo cual no es bueno
  print(numeros);
  numeros.add(5);
  numeros.add("Hola mundo");
  print(numeros);
  List<int> soloNumeros = [1, 2, 3, 4];
//   soloNumeros.add("Hola mundo"); // Manda error

  // TAMAÑO FIJO (Como ai fueran arreglos)
  List masNumeros = List(10); // Khe, sin "new"?
  print(masNumeros);
//   masNumeros.add(1); // Manda error
  // Como la definimos con tamaño 10, no pdemos aumentar su tamaño pero sí modificarlo:
  masNumeros[0] = 1;
  print(masNumeros);

  // ************ MAPS (Diccionarios)*****************
  // Son exactamente como en Java. Map<K,V>
  Map persona = {'nombre': 'Carlos', 'edad': 32, 'soltero': true};

  print(persona['nomre']);

  Map<int, String> personas = {1: 'Santiago', 2: "Roberto"};

  personas.addAll({4: "German"});
  print(personas);
  print(personas[4]);

  // **************** FUNCIONES ****************
  // Funcionan muy similar a Java
  saludar();
  print(despedida());
  print(suma(1, 2));
  // Funciones con tipado especifico (name arguments):
  print(saludo(texto: "asdasdasd", nombre: "Chanchallo"));
  // Función flecha:
  print(saludar2("HOla", "amigo000"));
}

void saludar() {
  print('Hola');
}

String despedida() {
  return "Hola";
}

int suma(int x, int y) {
  return x + y;
}

// Puedes ponerte exigente: (name arguments)
String saludo({String texto, String nombre}) {
  return '$texto $nombre';
}

// Función flecha
String saludar2(String texto, String nombre) => '$texto $nombre';
// Es un return implicito
