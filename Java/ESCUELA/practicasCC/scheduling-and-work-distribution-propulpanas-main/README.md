[![Review Assignment Due Date](https://classroom.github.com/assets/deadline-readme-button-24ddc0f5d75046c5622901739e7c5dd533143b0c8e959d652212380cedb1ea36.svg)](https://classroom.github.com/a/3liAK-l5)
[![Open in Codespaces](https://classroom.github.com/assets/launch-codespace-7f7980b617ed060a017424585567c406b6ee15c891e84e1186181d67ecf80aa0.svg)](https://classroom.github.com/open-in-codespaces?assignment_repo_id=11216669)
# Computación Concurrente - Calendarización y Distribución de Trabajo

## Equipo de enseñanza
* Manuel Alcántara Juárez <manuelalcantara52@ciencias.unam.mx>
* Ricchy Alaín Pérez Chevanier <alain.chevanier@ciencias.unam.mx>

## Objetivo

El objetivo de esta práctica es ejercitar la resolución de problemas que se pueden
dividir como subtareas que se pueden ejecutar en paralelo. Vamos a usar `ForkJoinPool`s 
y `CompletableFuture`s en Java. 

## Introducción

### Thread Pool, Executor Service, Futures

Un `Thread Pool` es un grupo de hilos que están esperando una tarea y se reutilizan muchas veces. 
El `Thread Pool` extrae un hilo del grupo y le asigna una tarea, después de completarla, el hilo 
vuelve al grupo de hilos disponibles. La ventaja de los `Thread Pools` es que evitan el costo de 
crear y destruir hilos en respuesta a las fluctuaciones a corto plazo de la demanda.

Además de los beneficios de rendimiento, los `Thread Pools` tienen una ventaja menos obvia, pero 
igualmente importante: aíslan a los programadores de aplicaciones de los detalles específicos de la 
plataforma, como la cantidad de hilos simultáneos que se pueden programar de manera eficiente.
Los `Thread Pool`s hacen posible escribir un solo programa que se ejecuta igualmente bien en un 
monoprocesador, un multiprocesador a pequeña escala y un multiprocesador a gran escala.

#### Tipos de Thread Pool

* `newCachedThreadPool`: Crea un grupo de hilos almacenable en caché. Si la longitud del grupo de hilos excede las 
  necesidades de procesamiento, puede reciclar de manera flexible los hilos inactivos, en cambio, si no hay reciclables, 
  genera un nuevo hilo.
* `newFixedThreadPool`: Crea un grupo de hilos de longitud fija para controlar el número máximo de hilos concurrentes, 
  y los hilos excesivos esperarán en la cola.
* `newScheduledThreadPool`: Crea un grupo de hilos de longitud fija para admitir la ejecución de tareas periódicas y regulares.
* `newSingleThreadExecutor`: Crea un grupo de hilos de un solo hilo, que solo usará un hilo de trabajo para ejecutar 
  tareas, asegurando que todas las tareas se ejecuten en el orden especificado (FIFO, LIFO, prioridad).

#### ExecutorService

`ExecutorService` es una API de la JDK que simplifica la ejecución de tareas en modo asíncrono. 
`ExecutorService` proporciona automáticamente un `Thread Pool` y una API para asignarle tareas, cuya documentación 
puedes consultar en [API Java ExecutorService](https://docs.oracle.com/javase/8/docs/api/java/util/concurrent/ExecutorService.html).

Un `ExecutorService` puede ser creado por medio de un método estático de la clase `Executors`, mediante el cual 
indicamos el tipo de `Thread Pool` que queremos que administre este. Por ejemplo:
	
```java
ExecutorService exec = Executors.newCachedThreadPool();
```

Un `ExecutorService` puede ejecutar tareas `Runnable` y `Callable`. Las tareas se pueden asignar al `ExecutorService` 
con métodos como `execute()`, `submit()`, `invokeAny()` e `invokeAll()`.

* `execute()`: El método no brinda ninguna posibilidad de obtener el resultado de la ejecución de una tarea 
  o verificar el estado de la tarea.

```java
executorService.execute(runnableTask);
```

* `submit()`: envía un `Callable` o tarea `Runnable` a un `ExecutorService` y devuelve un resultado de tipo `Future<T>`.

```java
Future<String> future = executorService.submit(callableTask);
```

* `invokeAny()`: asigna una colección de tareas a un `ExecutorService`, haciendo que cada una se ejecute, y devuelve 
  el resultado de una ejecución exitosa de una tarea, en caso de haber sido exitosa.

```java
String result = executorService.invokeAny(callableTasks);
```

* `invokeAll()`: asigna una colección de tareas a un `ExecutorService`, haciendo que cada una se ejecute, y devuelve 
  el resultado de todas las ejecuciones de tareas en forma de una lista de objetos de tipo `Future`.

```java
List<Future<String>> futures = executorService.invokeAll(callableTasks);
```

#### ForkJoin Pool

El framework _fork/join_ se presentó en Java 7, proporcionando herramientas para ayudar a acelerar el procesamiento 
paralelo al intentar usar todos los núcleos disponibles del procesador.

El framework primero aplica un _fork_, dividiendo recursivamente la tarea en subtareas independientes más pequeñas 
hasta que sean lo suficientemente simples como para ejecutarse de forma asíncrona. Después comienza la parte de _join_, 
en la que los resultados de todas las subtareas se unen recursivamente en un solo resultado, o en el caso de una tarea 
que no devuelve un resultado, el programa simplemente espera hasta que se ejecutan todas las subtareas.

Para proporcionar una ejecución paralela eficaz, el framework _fork/join_ utiliza un conjunto de hilos denominado 
`ForkJoinPool`, que administra los hilos de trabajo del tipo `ForkJoinWorkerThread`.

El `ForkJoinPool` es el corazón del framework. Es una implementación de `ExecutorService` que administra los hilos de 
trabajo y nos brinda herramientas para obtener información sobre el estado y el rendimiento del grupo de hilos.

De forma predeterminada, un hilo de trabajo obtiene tareas de la cabeza de su propia cola de trabajo 
(`DEQueue` DoubleEndedQueue); cuando está vacía, el hilo toma una tarea del otro extremo de la cola de trabajo de otro 
hilo ocupado o de la cola de entrada global, ya que aquí es donde es probable que se ubiquen las piezas de trabajo más 
grandes. Este enfoque minimiza la posibilidad de que los hilos compitan por las tareas. También reduce la cantidad de 
veces que el hilo tendrá que buscar trabajo, porque trabaja primero en los fragmentos de trabajo más grandes disponibles.

La forma más conveniente de obtener acceso a la instancia de `ForkJoinPool` es usar su método estático `commonPool()`. 
Esto proporcionará una referencia al `Thread Pool` común, que es un grupo de hilos predeterminado para cada 
`ForkJoinTask` y que es creado de manera estática, este `Thread Pool` tiene la propiedad de que siempre intenta mantener
un número de hilos igual la cantidad de procesadores o núcleos del hardware sobre el que está corriendo. 
De acuerdo con la documentación de Oracle, el uso del grupo común predefinido reduce el consumo de recursos, ya que esto
desalienta la creación de un grupo de hilos separado por tarea. Puede ser utilizado de la siguiente forma:

```java
ForkJoinPool commonPool = ForkJoinPool.commonPool();
```

Por otro lado, `ForkJoinTask` es el tipo base para tareas ejecutadas dentro de `ForkJoinPool`. En la práctica, una de 
sus dos subclases debería extenderse: `RecursiveAction` para tareas que no regresan un valor y `RecursiveTask<V>` para 
tareas que devuelven sí lo hacen. Ambos tienen un método abstracto `compute()` en el que se define la lógica de la tarea.

El uso del framework _fork/join_ puede acelerar el procesamiento de tareas grandes, pero para lograr este resultado, 
se sugiere seguir las siguientes recomendaciones:

* Use la menor cantidad posible de grupos de hilos. En la mayoría de los casos, la mejor decisión es utilizar un grupo 
  de hilos por aplicación o sistema.
* Use el grupo de hilos comunes predeterminado cuando no se necesita un ajuste específico.
* Use un umbral razonable para dividir `ForkJoinTask` en subtareas.
* Evita cualquier bloqueo en tus `ForkJoinTasks`

#### Completable Futures

La interfaz `Future` se agregó en Java 5 para servir como resultado de un cálculo asíncrono, pero no tenía ningún método
para combinar estos cálculos o manejar posibles errores.

Java 8 introdujo la clase `CompletableFuture`. Junto con la interfaz `Future`, también implementó la interfaz 
`CompletionStage`. Esta interfaz define el contrato para un paso de cálculo asíncrono que podemos combinar con 
otros pasos. `CompletableFuture` es al mismo tiempo un bloque de construcción y un framework, con alrededor de 
cincuenta métodos diferentes para componer, combinar y ejecutar pasos de cálculo asincrónico y manejar errores.

La clase `CompletableFuture` implementa la interfaz `Future`, por lo que podemos usarla como una implementación `Future`,
pero con una lógica de finalización adicional.

Se puede crear una instancia de esta clase con un constructor sin argumentos para representar algún resultado `Future`, 
entregárselo a los consumidores y completarlo en algún momento en el futuro usando el método `complete`. 
Los consumidores pueden utilizar el método `get` para bloquear el hilo actual hasta que se proporcione el resultado de este.

Los métodos estáticos `runAsync` y `supplyAsync` nos permiten crear una instancia de `CompletableFuture` a partir de 
los tipos de interfaces funcionales `Runnable` y `Supplier` correspondientemente. 
Tanto `Runnable` como `Supplier` son interfaces funcionales que permiten pasar sus instancias como expresiones lambda 
gracias a la nueva característica de Java 8.

#### Ejemplos de Completable Futures

La mejor parte de la API `CompletableFuture` es la capacidad de combinar instancias de `CompletableFuture` en una cadena 
de pasos de cálculo.

El resultado de este encadenamiento es en sí mismo un `CompletableFuture` que permite un mayor encadenamiento y combinación. 
Este enfoque es omnipresente en los lenguajes funcionales y, a menudo, se lo denomina patrón de diseño monádico.

En el siguiente ejemplo, usamos el método `thenCompose` para encadenar dos Futuros secuencialmente.

Este método toma una función que devuelve una instancia de `CompletableFuture`. El argumento de esta función es el 
resultado del paso de cálculo anterior. Esto nos permite usar este valor dentro de la siguiente lambda de 
`CompletableFuture`:

```java
CompletableFuture<String> completableFuture 
  = CompletableFuture.supplyAsync(() -> "Hello")
    .thenCompose(s -> CompletableFuture.supplyAsync(() -> s + " World"));

assertEquals("Hello World", completableFuture.get());
```

El método `thenCompose()` es similar a `thenApply()` en que ambos devuelven una nueva etapa de finalización. 
Sin embargo, `thenCompose()` usa la etapa anterior como argumento. Se aplanará y devolverá un `Future` con el resultado 
directamente, en lugar de un futuro anidado como observamos en `thenApply()`:

```java
CompletableFuture<Integer> computeAnother(Integer i) {
    return CompletableFuture.supplyAsync(() -> 10 + i);
}
CompletableFuture<Integer> finalResult = compute().thenCompose(this::computeAnother);
```

Para el manejo de errores en una cadena de pasos de cómputo asincrónico, tenemos que adaptar el uso de _throw/catch_ 
de manera similar.

En lugar de capturar una excepción en un bloque sintáctico, la clase `CompletableFuture` nos permite manejarlo en un 
método de manejo especial. Este método recibe dos parámetros: un resultado de un cómputo (si finalizó con éxito) y 
la excepción lanzada (si algún paso del cómputo no se completó normalmente).

En el siguiente ejemplo, usamos el método `handle `para proporcionar un valor predeterminado cuando 
el cálculo asíncrono de un saludo finalizó con un error porque no se proporcionó ningún nombre:

```java
String name = null;

// ...

CompletableFuture<String> completableFuture  
  =  CompletableFuture.supplyAsync(() -> {
      if (name == null) {
          throw new RuntimeException("Computation error!");
      }
      return "Hello, " + name;
  }).handle((s, t) -> s != null ? s : "Hello, Stranger!");

assertEquals("Hello, Stranger!", completableFuture.get());
```

La mayoría de los métodos de la _API_ proporcionada en la clase `CompletableFuture` tienen dos variantes adicionales 
con el sufijo _Async_. Estos métodos generalmente están destinados a ejecutar un paso de ejecución correspondiente 
en otro hilo.

Los métodos sin el sufijo _Async_ ejecutan la siguiente etapa de ejecución utilizando un el mismo hilo. 
Por el contrario, el método `async` sin el argumento `Executor` ejecuta la tarea usando `ForkJoinPool.commonPool()`. 
Finalmente, el método `async` con un argumento `Executor` ejecuta la tarea usando el `Executor` que nosotros indiquemos.

La única diferencia visible es el método `thenApplyAsync`, pero bajo el capó, la aplicación de una función se envuelve 
en una instancia de `ForkJoinTask`.

## Desarrollo
En esta práctica trabajarás con una base de código construida con Java 11 y Maven Wrapper,
también proveemos pruebas unitarias escritas con la biblioteca **Junit 5.7.2** que te
darán retrospectiva inmediatamente sobre el funcionamiento de tu implementación.

Para ejecutar las pruebas necesitas ejecutar el siguiente comando:

```
$ ./mvnw test
```

Para ejecutar las pruebas contenidas en una única clase de pruebas, utiliza
un comando como el siguiente:

```
$ ./mvnw -Dtest=MyClassTest test
```

En el código que recibirás la clase **App** tiene un método __main__ que puedes ejecutar
como cualquier programa escrito en __Java__. Para eso primero tienes que empaquetar
la aplicación y finalmente ejecutar el jar generado. Utiliza un comando como el que
sigue:

```
$ ./mvnw package
... o saltando las pruebas unitarias
$ ./mvnw package -DskipTests
...
...
$ ./mvnw exec:java 
```

## Configuración de los git hooks para formatear el código

Antes de empezar a realizar commits que contenga tu solución
tienes que configurar un módulo de git que te ayudará a
formatear tu código.

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

### [PROBLEMA 1] Merge Sort (3.5 puntos)

Escribe el algoritmo de _merge sort_ de forma paralela, de tal manera que cada llamada recursiva
sea representada por medio de alguna subclase de `ForkJoinTask` y ejecutada utilizando `ForkJoinPool.commonPool()`.
Es importante que consideres un `THRESHOLD` (por ejemplo 500) de tal manera de que si la longitud del arreglo al momento
de hacer la llamada recursiva el menor que dicho número entonces ya no crear más subtareas sino que ejecutas
el algoritmo de manera secuencial.
	
#### Especificación

Implementa la clase `Sorting`. Para verificar que tu implementación funciona debes de pasar las 
pruebas unitarias contenidas en la clase `SortingTest`.

En tu reporte incluye cuál es el trabajo <code>T<sub>1</sub></code> y la longitud de la ruta crítica
de cualquier ejecución de tu algoritmo <code>T<sub>&#x221e;</sub></code>. Para esto te puedes apoyar
en la recurrencia para calcular la complejidad computacional de _Merge Sort_.

### [PROBLEMA 2]  Suma de Polinomios (3.5 puntos)

Sean ![P(x) = \sum_{i=0}^{d} p_i x^i](https://latex.codecogs.com/svg.image?P(x)%20=%20%5Csum_%7Bi=0%7D%5E%7Bd%7D%20p_i%20x%5Ei)
y ![Q(x) = \sum_{i=0}^{d} q_i x^i](https://latex.codecogs.com/svg.image?Q(x)%20=%20%5Csum_%7Bi=0%7D%5E%7Bd%7D%20q_i%20x%5Ei)
polinomios de grado `d`, donde `d` es una potencia de `2`. Podemos expresar:

![P(x) = P_0 (x) + (P_1 (x) x^{d/2})](https://latex.codecogs.com/svg.image?P(x)%20=%20P_0%20(x)%20&plus;%20(P_1%20(x)%20x%5E%7Bd/2%7D))
y
![Q(x) = Q_0 (x) + (Q_1 (x) x^{d/2})](https://latex.codecogs.com/svg.image?Q(x)%20=%20Q_0%20(x)%20&plus;%20(Q_1%20(x)%20x%5E%7Bd/2%7D))

Donde <code>P<sub>0</sub>(x)</code>, <code>P<sub>1</sub>(x)</code>, <code>Q<sub>0</sub>(x)</code> y
<code>Q<sub>1</sub>(x)</code> son polinomios de grado `d/2`.

La clase `Polynomial` provee métodos `put` y `get` para acceder a los coeficientes, y provee un método
`split` que en tiempo constante divide el polinomio `P(x)` en dos polinomios de grado `d/2` como 
explicamos anteriormente; donde los cambios en los subpolinomios generados se reflejan en el 
polinomio original y vice versa.

Tu tarea es escribir un algoritmo paralelo para la operación de suma 
utilizando `RecursiveAction`s y `ForkJoinPool.commonPool()`.
Es importante que consideres un `THRESHOLD` (por ejemplo 1000) de tal manera de que si el grado del polinomio es menor 
que dicho número ya no crear más subtareas, sino que ejecutas el algoritmo de manera secuencial.

La suma puede descomponerse de la siguiente manera:
![P(x)  + Q(x) = (P_0 (x) + Q_0 (x)) + (Q_1 (x)  + P_1 (x)) x^{d/2}](https://latex.codecogs.com/svg.image?%5Cbg_white%20%5Cinline%20P(x)%20%20&plus;%20Q(x)%20=%20(P_0%20(x)%20&plus;%20Q_0%20(x)%20&plus;%20(Q_1%20(x)%20%20&plus;%20P_1%20(x)%20x%5E%7Bd/2%7D)

#### Especificación del programa

Implementa el método `add` de la clase `Polynomial` con la especificación dada en la descripción. 
Para verificar que tu implementación funciona debes de pasar las pruebas unitarias contenidas 
en la clase `PolynomialAdditionTest`.

En tu reporte incluye cuál es el trabajo <code>T<sub>1</sub></code> y la longitud de la ruta crítica
de cualquier ejecución de tu algoritmo <code>T<sub>&#x221e;</sub></code>.

### [PROBLEMA 3] Suma de un Arreglo (3 puntos)

Implementa un algoritmo paralelo que calcule la suma de un arreglo de números utilizando un algoritmo
_divide-y-vencerás_. Usa un valor the `THRESHOLD` suficientemente grande, prueba con
varios valores y verifica con las pruebas unitarias qué valores te dan mejores tiempos
de ejecución. 

Para implementar ese algoritmo tienes que utilizar `CompletableFuture`s.

#### Especificación del programa

Implementa la clase `ArraySum`. Para verificar que tu implementación funciona debes de pasar las
pruebas unitarias contenidas en la clase `ArraySumTest`.

En tu reporte incluye cuál es el trabajo <code>T<sub>1</sub></code> y la longitud de la ruta crítica
de cualquier ejecución de tu algoritmo <code>T<sub>&#x221e;</sub></code>.

### [PROBLEMA EXTRA]  Multiplicación de Polinomios (2 puntos)

Utilizando la definición de _polinomio_ dada en el "Problema 2" implementa un algoritmo paralelo 
para la operación de multiplicación utilizando `RecursiveAction`s y `ForkJoinPool.commonPool()`.
Es importante que consideres un `THRESHOLD` (por ejemplo 30) de tal manera de que si la suma de los 
grados de los polinomios es menor a `THRESHOLD`, entonces se ejecuta el algoritmo de forma secuencial.

La multiplicación puede descomponerse de la siguiente manera:

![P(x)*Q(x) = P_0(x)*Q_0(x) + (P_0(x)*Q_1(x) + P_1(x)*Q_0(x))x^{d/2} + P_1(x)*Q_1(x) x^d](https://latex.codecogs.com/gif.image?%5Cinline%20%5Clarge%20%5Cdpi%7B300%7D%5Cbg%7Bwhite%7DP(x)*Q(x)%20=%20P_0(x)*Q_0(x)%20&plus;%20%5BP_0(x)*Q_1(x)%20&plus;%20P_1(x)*Q_0(x)%5Dx%5E%7Bd/2%7D%20&plus;%20P_1(x)*Q_1(x)%20x%5Ed%20)

Nota: `P(x)*Q(x)` es de grado `2d`.

#### Especificación del programa

Implementa el método `multiply` de la clase `Polynomial` con la especificación dada en la descripción.
Para verificar que tu implementación funciona debes de pasar las pruebas unitarias contenidas
en la clase `PolynomialMultiplicationTest`.

En tu reporte incluye cuál es el trabajo <code>T<sub>1</sub></code> y la longitud de la ruta crítica
de cualquier ejecución de tu algoritmo <code>T<sub>&#x221e;</sub></code>.