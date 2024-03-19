# Reporte
- Santiago Arroyo Lozano <br>
- Rodrigo Liprandi Cortés <br>

## Ruta Crítica problema 2
**Trabajo T₁:**
El trabajo T₁ se refiere a la cantidad total de trabajo realizado por el algoritmo. En este caso, el trabajo T₁ es proporcional al tamaño del arreglo N, ya que cada elemento del arreglo debe sumarse. Por lo tanto, el trabajo T₁ es O(N).

**Tiempo T∞:**
El tiempo T∞ se refiere al tiempo de ejecución más rápido posible para el algoritmo cuando se utiliza una cantidad infinita de recursos. En este caso, el tiempo T∞ depende del tamaño del umbral M y de la capacidad del sistema para ejecutar tareas en paralelo.

- Si el tamaño del problema (N) es menor o igual al umbral (M), se realiza la suma de manera secuencial en un solo hilo, lo que implica que el tiempo T∞ es igual al tiempo de ejecución secuencial, que es proporcional al tamaño del arreglo N.

- Si el tamaño del problema (N) es mayor que el umbral (M), el algoritmo divide el arreglo en dos partes y realiza la suma de forma asíncrona utilizando `CompletableFuture`. Esto permite que las dos partes se sumen en paralelo, lo que puede acelerar la ejecución. Sin embargo, el tiempo T∞ también depende de la capacidad del sistema para manejar tareas en paralelo. Si el sistema tiene recursos suficientes para manejar las tareas en paralelo de manera eficiente, el tiempo T∞ se acerca al tiempo de ejecución secuencial dividido por el número de tareas paralelas. En este caso, el tiempo T∞ sería aproximadamente O(N/M), donde M es el tamaño del umbral.

Es importante tener en cuenta que el tiempo T∞ no se puede determinar con precisión sin conocer las características del sistema y los recursos disponibles. Puede variar según la implementación específica del algoritmo y las condiciones de ejecución.

## Ruta Crítica problema 3
En este caso, el trabajo $T1$ es proporcional al grado del polinomio $N$. En este caso, la longitud de la ruta crítica $(T_infinito)$ es $\log(N/M)$, donde $log$ es el logaritmo en base 2.
## Ruta Crítica problema Extra
En este caso, el trabajo T1 es proporcional al producto de los grados de los polinomios, es decir, $N \times N.$ En este caso, la longitud de la ruta crítica (T_infinito) es log(N/M), donde log es el logaritmo en base 2.
Es importante tener en cuenta que los valores exactos de T1 y T_infinito pueden variar según la implementación y los detalles específicos del hardware y del entorno de ejecución.