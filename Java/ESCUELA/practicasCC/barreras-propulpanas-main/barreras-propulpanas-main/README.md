[![Review Assignment Due Date](https://classroom.github.com/assets/deadline-readme-button-24ddc0f5d75046c5622901739e7c5dd533143b0c8e959d652212380cedb1ea36.svg)](https://classroom.github.com/a/ORQNbOi8)
[![Open in Codespaces](https://classroom.github.com/assets/launch-codespace-7f7980b617ed060a017424585567c406b6ee15c891e84e1186181d67ecf80aa0.svg)](https://classroom.github.com/open-in-codespaces?assignment_repo_id=11178395)
# Computación Concurrente - Barreras

## Equipo de enseñanza

* Ricchy Alaín Pérez Chevanier <alain.chevanier@ciencias.unam.mx>

## Objetivo

El objetivo fundamental de esta práctica es reafirmar los conocimientos adquiridos en clase para sincronizar hilos 
mediante semáforos y barreras. Para ello el estudiante implementará una barrera, asi como también utilizarás 
una barrera para sincronizar hilos en un caso de uso.

## Introducción

Imagina que estás escribiendo el generador de escenas para un juego de computadora. Tu programa prepara una secuencia de
_frames_ que serán mostrados por un paquete gráfico (tal vez un coprocesador). Este tipo de programas algunas veces es
llamado _soft real-time application_: _real-time_ (tiempo real) porque debe de mostrar al menos 35 _frames_ por segundo para ser 
efectiva, y _soft_ (suave) porque fallas intermitentes no son catastróficas. En una computadora _single-threaded_, 
puedes escribir un _loop_ como este: 

```java
  while (true) {
    frame.prepare(); 
    frame.display();
  }
```

Si, en su lugar, tienes `n` _threads_ paralelos disponibles, tiene sentido dividir la generación de un _frame_ en `n`
partes disjuntas, y hacer que cada _thread_ prepare su parte en paralelo con los otros.

```java
  int me = ThreadID.get(); 
  while (true) {
    frame[me].prepare();
    frame[me].display();
  }
```

El problema con esta estrategia es que distintos _threads_ requieren diferentes cantidades de tiempo para preparar y
presentar su porción del _frame_. Algunos _threads_ pueden empezar a mostrar el _i-ésimo frame_ antes de que otros
hayan terminado el _i-ésimo - 1_. Para evitar estos problemas de sincronización, podemos organizar los cálculos como 
una secuencia de fases, en la cual, un _thread_ no puede comenzar la _i-ésima_ fase hasta que los otros hayan terminado
la fase _i-ésima - 1_.

El mecanismo para forzar este tipo de sincronización es llamado _**Barrier**_ (_Barrera_), su interfaz es mostrada 
abajo. Una _barrera_ es una primitiva de sincronización para coordinar _threads_ asíncronos para que se comporten como
si fueran síncronos. Cuando un _thread_ termina la fase `i` llama el método `await()` de la _barrera_, con lo cual
se bloquea hasta todos los _threads_ (los `n` disponibles) hayan también terminado dicha fase.

El código de abajo muestra cómo podemos utilizar una _barrera_ para hacer que el programa de _rendering paralelo_ 
funcione correctamente. Después de preparar el _i-ésimo frame_, todos los _threads_ se sincronizan en la _barrera_
antes de empezar a mostrar dicho _frame_. Esta estructura asegura que todos los _threads_ que concurrentemente
muestran un _frame_, siempre muestran el mismo.

```java
  public interface Barrier {
    void await();
  }

  ...
  
  private Barrier b;

  ...

  while (true){
    frame[my].prepare();
    b.await();
    frame[my].display();
  }
```

Las implementaciones de _barreras_ suponen muchos de los mismos problemas de rendimiento que ya vimos en los 
_spin locks_, así como también algunos problemas nuevos. Claramente, las _barreras_ deben de ser rápidas, en el sentido
 de que queremos minimizar la duración entre el momento en el que el último _thread_ llega a la _barrera_ y el momento
en el que el último _thread_ deja la _barrera_. También es importante que los _threads_ dejen la _barrera_ más o menos
al mismo tiempo. El tiempo de notificación de un _thread_ es el intervalo de tiempo entre el momento en el que un 
_thread_ ha detectado que todos los _threads_ han alcanzado la _barrera_, y el momento cuando ese _thread_ sale de la
_barrera_. Tener tiempos de notificación uniformes es relevante para muchas _soft real-time applications_. Por ejemplo,
la calidad de las imágenes mejora si todas las porciones del _frame_ se actualizan más o menos al mismo tiempo.


### Desarrollo
En esta práctica trabajarás con una base de código construida con Java 11 y Maven Wrapper, también proveemos pruebas unitarias escritas con la biblioteca **Junit 5.7.2** que te darán retrospectiva inmediatamente sobre el correcto funcionamiento de tu implementación.

Para ejecutar las pruebas unitarias necesitas ejecutar el siguiente comando:

```
$ ./mvnw test
```

Para ejecutar las pruebas unitarias contenidas en una única clase de pruebas, utiliza un comando como el siguiente:

```
$ ./mvnw -Dtest=MyClassTest test
```

En el código que recibirás la clase **App** tiene un método __main__ que puedes ejecutar como cualquier programa escrito en __Java__. Para eso primero tienes que empaquetar la aplicación y finalmente ejecutar el jar generado. Utiliza un comando como el que sigue:

```
$ ./mvnw package
... o saltando las pruebas unitarias
$ ./mvnw package -DskipTests
...
...
$ ./mvnw exec:java 
```

### Configuración de los git hooks para formatear el código

Antes de empezar a realizar commits que contenga tu solución tienes cque configurar un módulo de git que te ayudará a formatear tu código.


```
./mvnw git-code-format:install-hooks
```

## Forma de trabajo

Recomendamos ampliamente utilizar el editor [IntelliJ](https://www.jetbrains.com/help/idea/installation-guide.html)
para realizar el desarrollo de la práctica.
También agrega el plugin de IntelliJ [SonarLint](https://www.sonarsource.com/products/sonarlint/features/jetbrains/).


## Entrega

Deja todo el código con tu solución en la rama __main__, pues por omisión es esta
rama la que compara __Github Classroom__ contra la versión inicial del código mediante
el __Pull Request__ llamado __Feedback__, el cual nosotros vamos a revisar
para evaluar tu entrega.

Para verificar que tu código cumple con la especificación,
en tu __Pull Request__ debes de pasar las dos validaciones que
hace __Github Actions__ sobre el código, una de ellas verifica
que pasas las pruebas automatizadas, y la otra que hayas formateado
tu código con el plugin de maven.

Además, no olvides marcar en classroom la tarea como entregada y
en ella incluir el enlace hacia el __Pull Request__ que contiene tu
solución.

La fecha de entrega de tu práctica va a ser el máximo entre la fecha en la que
abriste el __Pull Request__ y la fecha en la que hiciste el último push al repositorio con tu
solución.

## Actividades

### Problema 1: Barrera de Árbol Estático
Implementa la clase `StaticTreeBarrier`, que es similar a las barreras vistas en clase, pero tiene dos mejoras 
importantes con respecto a otras barreras, no sufre de contención de memoria y no tiene que recorrer grandes 
estructuras para funcionar. Es relevante mencionar que el árbol que generarás no necesariamente es completo.

#### Especificación del programa

* La descripción de esta barrera la podrás encontrar en el libro _"The Art of Multiprocesor Programming"_ 
  en el capítulo de _"Barreras"_.
* Para verificar que tu implementación es correcta tendrás que pasar totas las pruebas unitarias contenidas en
  la clase `BarrierTest`.

#### Preguntas

* Explica cómo mejora este algoritmo a `SenseBarrier`.
* Explica cómo mejora este algoritmo a `TreeBarrier`.


### Problema 2: El Mundo de las Pelotas

Encontrarás 3 clases:
* `Ball`, una instancia de esta clase representará una pelota que vive en el `BallWorld`. La clase implementa
  la interfaz `Runnable` y ejecuta un `ciclo` infinito en el método `run` donde la pelota repetidamente
  realiza un movimiento que actualiza su posición. Cada invocación fuerza a repintar el mundo y esperar por un periodo 
  de tiempo de 40ms. La pelota también tiene la habilidad de pintarse a sí misma dado el contexto gráfico. 
  Por lo tanto, una vez que se crea, cada pelota se registra a sí misma en el mundo en donde vive invocando 
  al método `addBall`.
* `BallWorld`, una instancia de esta clase representa el mundo en donde viven las pelotas y puede contener muchas de 
  ellas en una `List`. El mundo es una subclase de un `JPanel`. Por consecuencia, el mundo se dibuja a sí mismo, 
  utilizando el método `paintComponent` que a su vez le indica a cada pelota que debe de dibujarse. 
  Los detalles para pintar un componente no son importantes en este ejercicio.
* `App`, esta clase contiene el método principal, el cual crea un mundo, genera y añade algunas pelotas a él 
  y finalmente arranca la ejecución de la simulación.

Hay que notar que el flujo de control de este ejercicio es un poco sutil. El movimiento de las pelotas y el repintado 
se inicia de forma independiente por cada una de las pelotas, ya que cada una de ellas se ejecuta en un 
hilo independiente. Debido a esto distintas pelotas pueden ejecutar el método `makeMovement` y `world.repaint()`, 
de manera concurrente. Invocar al método `world.repaint` de manera concurrente no crea problemas, porque lo garantiza 
la documentación de `Swing`. Por otro lado, invocar al método `repaint()` también desencadena invocar al método `draw` 
de cada una de las pelotas registradas en el mundo.

Sin embargo, esto también es correcto, ya que ambos métodos `draw` y `makeMovement` son sincronizados, 
que significa que no se ejecutarán de manera concurrente en un objeto dado.

Como se puede ver, este programa sencillo tiene una concurrencia complicada. Es aceptable tener un diseño como este 
para programas sencillos, pero para cosas más grandes el comportamiento concurrente debe ser diseñado de 
una manera estructurada, o de lo contrario será muy complicado.


#### EJERCICIO 1: Matando las pelotas
Tu primera tarea es agregar un nuevo hilo a tu programa que se encarge de matar a las pelotas tanto en tiempos 
y orden aleatorios. Matar una pelota significa que su método `run` debe de terminar. 
Además, la pelota debe de ser retirada del mundo (de una manera segura para los subprocesos). Después de realizar esto, 
el recolector de basura en el sistema eventualmente recuperará el espacio asignado para el objeto pelota.

Modifica la clase `App` para que el hilo que mata a los demás solamente se active cuando la aplicación recibe la opción 
`enableKiller`, con un comando como el que sigue:

```bash
$ ENABLE_KILLER=true;
```

Para resolver el problema tienes que utilizar primitivas de sincronización.

#### EJERCICIO 2: Congelando las pelotas
Ahora debes modificar el programa para que tenga el siguiente comportamiento: Si una pelota que rebota después 
de algunos movimientos se encuentra en la zona diagonal del mundo, es decir, la pelota está a una distancia menor 
a su radio de la recta $y=x$, entonces se `congele`, es decir, deja de moverse. Ten en cuenta que una pelota puede 
saltar por encima de la zona en diagonal en un solo movimiento; no causará que se congele. Cuando todas las bolas 
se han congelado en la diagonal, todas se despiertan y siguen rebotando hasta que se congelan de nuevo en la diagonal. 
Este ciclo de rebotar y congelarse continúa para siempre.
Para resolver este ejercicio deberás de utilizar la barrera que implementaste en el _"PROBLEMA 1"_.