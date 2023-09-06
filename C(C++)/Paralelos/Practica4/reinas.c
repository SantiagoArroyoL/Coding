/** @file reinas.c
 *  @date 10-05-2023
 *  @brief Programa que propone una solución para el problema de las N reinas de forma secuencial y paralelo
 *
 *  Vamos a implementar un algoritmo que colocando una reina ded forma aleatoria resuelva el problema de las N reinas. P
 *  Particularmente resolveremos para 8 reinas.
 *
 *  @author Santiago Arroyo
 */
#include <omp.h>
#include <time.h>
#include <stdio.h>
#include <stdlib.h>


#define N 8
#define num_hilos 4

double start, end;

/**
 * Función que imprime el tablero a traves de la terminal (imprime una matriz de enteros)
 * @param tablero El tablero a mostrar
 */
void imprimirTablero(int tablero[N][N]) {
    int i, j;
    for (i = 0; i < N; i++) {
        for (j = 0; j < N; j++) {
            printf("%2d ", tablero[i][j]);
        }
        printf("\n");
    }
    printf("\n");
}

/**
 * Funcion que revisa que la casilla donde queremos poner la reina sea segura
 * @param tablero El tablero de juego que contiene todas las casillas
 * @param fila La fila donde queremos posicionar la reina
 * @param columna La columna donde queremos posicionar la reina
 * @return Verdadero o falso dependiendo si la posicion es segura o no (1 o 0)
 */
int esPosicionSegura(int tablero[N][N], int fila, int columna) {
    int i, j;
    // Verificar la fila en la izquierda
    for (i = 0; i < columna; i++) {
        if (tablero[fila][i])
            return 0;
    }
    // Verificar la diagonal superior izquierda
    for (i = fila, j = columna; i >= 0 && j >= 0; i--, j--) {
        if (tablero[i][j])
            return 0;
    }
    // Verificar la diagonal inferior izquierda
    for (i = fila, j = columna; j >= 0 && i < N; i++, j--) {
        if (tablero[i][j])
            return 0;
    }
    return 1;
}

/**
 * Resolvemos el problema de las N reinas de forma secuencial usando recursion
 * Tambien usamos la tecnica de backtracking para corregir cuando una reina se encuentre en una posicion insegura
 * Proponemos una fila aleatoria el inicio para poder proponer distintas soluciones cada que se ejecute el programa
 * Es poisble que no encontremos una solucion a la hora de elegir la octava reina y debamos comenzar de nuevo
 * @param tablero El tablero de juego que contiene todas las casillas
 * @param columna La columna en la que vamos
 * @return Verdadero si es una solucion valida del problema de las N reinas, falso en otro caso (1 o 0)
 */
int resolverReinas(int tablero[N][N], int columna) {
    if (columna >= N)
        return 1;
    for (int i = (rand() % 8); i < N; i++) {
        if (esPosicionSegura(tablero, i, columna)) {
            tablero[i][columna] = 1;
            if (resolverReinas(tablero, columna + 1))
                return 1;
            tablero[i][columna] = 0;  // Volver atrás (backtracking)
        }
    }
    return 0;
}

/**
 * Resolver el problema ded las N reinas en pralelo
 * los hilos trabajan de forma concurrente para buscar una solución al problema de las ocho reinas.
 * Esto se logra dividiendo el tablero entre los hilos de manera equitativa,
 * de modo que cada hilo se encarga de explorar un segmento del tablero.
 * Si se encuentra una solución, solo se imprime una vez y se detiene la búsqueda en los demás hilos.
 * @param tablero El tablero de juego que contiene todas las casillas
 * @param columna La columna en la que vamos
 * @param solucionEncontrada apuntador
 */
void resolverReinasParallel(int tablero[N][N], int columna, int* solucionEncontrada) {
    if (*solucionEncontrada) {
        return;
    }
    if (columna >= N) {
        *solucionEncontrada = 1;
#pragma omp critical
        {
            printf("Solución encontrada:\n");
            imprimirTablero(tablero);
        }
        return;
    }
    int localSolucionEncontrada = 0;
    int i;
#pragma omp parallel for private(i) reduction(|:localSolucionEncontrada)
    for (i = omp_get_thread_num(); i < N; i++) {
        if (!localSolucionEncontrada && esPosicionSegura(tablero, i, columna)) {
            tablero[i][columna] = 1;
            resolverReinasParallel(tablero, columna + 1, &localSolucionEncontrada);
            tablero[i][columna] = 0;
        }
    }
    if (localSolucionEncontrada) {
        *solucionEncontrada = 1;
    }
}


int main() {
    time_t t;
    int tablero[N][N] = {0};
    int solucionEncontrada = 0;
    srand((unsigned) time(&t));

    /* SECUENCIAL */
    /* SECUENCIAL */
    /* SECUENCIAL */
    start = omp_get_wtime();
    // Podemos hacer un bucle y obligar al secuencial a que siempre lo resuelva pero dejemoslo fallar
//    while (resolverReinas(tablero, 0) != 1) {
    if (resolverReinas(tablero, 0) != 1) {
        printf("No se encontró solución secuencial.\n");
    }
    else {
        printf("Solución secuencial encontrada:\n");
        imprimirTablero(tablero);
        end = omp_get_wtime();
        printf("Resolver el problema en secuencial tomo %f segundos\n", end - start);
    }


    /* PARALELO */
    /* PARALELO */
    /* PARALELO */
    start = omp_get_wtime();
#pragma omp parallel num_threads(num_hilos)
    {
        resolverReinasParallel(tablero, 0, &solucionEncontrada);
    }
    if (!solucionEncontrada) {
        printf("No se encontró ninguna solución paralela.\n");
    } else {
        end = omp_get_wtime();
        printf("Resolver el problema en paralelo tomo %f segundos\n", end - start);
    }
    return 0;
}
