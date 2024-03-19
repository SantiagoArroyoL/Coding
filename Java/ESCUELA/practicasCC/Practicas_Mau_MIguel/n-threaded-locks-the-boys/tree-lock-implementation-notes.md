# Notas para implementar PetersonTreeLock

* Número de niveles lo tenemos que calcular a partir de número de hilos.
  Ej. Si tenemos 8 hilos, tenemos 3 niveles, qué relación tienes estos números?

* El número de locks que tenemos que utilizar lo tenemos que calcular.
  Ej. Si tenemos 8 hilos, tenemos 7 locks, qué relación tienes estos números?

* Los `PetersonLock`s están acomodados en un arreglo y están indexados a partir de 1, por facilidad como en la implementación de heapsort/heap

* Los hijos de hilo `X` son `2X` y `2X+1`, es decir el padre del thread `Y` es `Y/2`. Nota división de número enteros se trunca el resultado.

* Cual es el nivel que le corresponde a un `lock `dentro del arreglo de acuerdo a su índice dentro del arreglo de locks?  
  __Respuesta__: `getLevelFromLock (threads, index)` # index in 1…threads
  Ej. Si tenemos 8 hilos, tenemos los siguientes niveles por cada índice
  - index = 1 -> 3
  - index = 2 -> 2
  - index = 3 -> 2
  - index = 4 -> 1
  - …
  - index = 7 -> 1


* Cual es el lock por el que tengo que contender dado mi threadId y el level actual?

  __Respuesta__: `getLockIndex(threadId, level, threads)`
  - threadId = 0, level= 1 -> 4
  - threadId = 0, level= 2 -> 2
  - threadId = 0, level= 3 -> 1
  - threadId = 2, level= 1 -> 4 + 1
  - threadId = 2, level= 2 -> 2
  - threadId = 2, level= 3 -> 1
  - threadId = 4, level= 1 -> 4 + 2
  - threadId = 4, level= 2 -> 2 + 1
  - threadId = 4, level= 3 -> 1

* Dado que ya sé en qué lock tengo que contender, ahora qué rol juego `[0, 1]`?

  __Respuesta__: `getCurrentLockIndex(threadId, level, threads)`
  - threadId = 2, level = 1 -> 0
  - threadId = 2, level = 2 -> 1
  - threadId = 2, level = 3 -> 0

Pseudo código de la implementación de TreeLock:

```
N: int # número de threads
threadId: ThreadID
petersonLocks[N]: Array<PetersonLock>

init:
	for i in 1..N:
		petersonLocks[i] = PeteronLock(…) 
		petersonLocks[I].setThreadId (threadId) 
		# queremos que los petersonLock usen la misma instancia de threadId que TreeLock

lock:
	for level in 1 .. levels:
		petersonLocks[<numero que depende de mi threadId y level>].lock()

unlock:
	for level in levels .. 1:
		petersonLocks[<numero que depende de mi threadId y level>].unlock()
```

