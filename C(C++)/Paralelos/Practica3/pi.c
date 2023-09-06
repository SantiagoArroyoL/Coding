/** @file pi.c
 *  @date 09-03-2023
 *  @brief Programa que aproxima el valor de pi a partir
 *   de la suma de reimann de un circulo de radio 1
 *
 *  Ademas de la aproximacion lo que haremos es comparar los tiempo en secuencial vs paralelo,
 *   dividiendo la suma de Reimann en varios hilos
 *
 *  @author Santiago Arroyo
 */
#include <math.h>
#include <stdlib.h>
#include <stdio.h>
#include <omp.h>

/* variables varias*/
double start;
double end;
long double pi;

/* prototipos */
long double reimann(float inicio, float fin, int n);
long double reimannParallel(float inicio, float fin, int n);

int main(int argc, char **argv){
    if (argc < 2 ){
        printf("Por favor introduce el numero de rectangulos\n");
        exit(1);
    }
    int n = atoi(argv[1]);
    printf("El numero de rectangulos es %d\n", n);
    start = omp_get_wtime();
    pi = reimann(0,1,n); // suma de reimann [0,1]
    end = omp_get_wtime();
    printf("La aproximacion secuencial tomo %f segundos\n", end - start);
    printf("Valor de pi = %Lf\n",pi);
    start = omp_get_wtime();
    pi = reimannParallel(0,1,n); // suma de reimann [0,1]
    end = omp_get_wtime();
    printf("La aproximacion paralela tomo %f segundos\n", end - start);
    printf("Valor de pi = %Lf\n",pi);
}

/**
 * Suma de Reimann secuencial para un circulo usando rectangulos
 * @param inicio - [a,b]: a
 * @param fin - [a,b]: b
 * @param n - EL n del limite
 * @return - El area bajo la curva
 */
long double reimann(float inicio, float fin, int n) {
    int r = 0;
    float delta = (fin - inicio) / n; //ancho de cada rectangulo
    long double suma = 0;
    for(int i = 1; i <= n ; i++)     // Calcula el área de cada rectángulo
    {
        long double x = inicio + delta * i; // Sumando i vamos cambiando de rectangulo
        long double y = sqrt(1 - (x*x)); // Altura del rectangulo
        long double area = delta * y; // El area del rectangulo
        suma += area;
    }
    return suma * 4.0; // Solo calculamos el area de un cuadrante del circulo.
}

/**
 * Suma de Reimann paralelo para un circulo usando rectangulos
 * @param inicio - [a,b]: a
 * @param fin - [a,b]: b
 * @param n - EL n del limite
 * @return - El area bajo la curva
 */
long double reimannParallel(float inicio, float fin, int n) {
    int r = 0;
    float delta = (fin - inicio) / n; //ancho de cada rectangulo
    long double suma = 0;
#pragma omp parallel for reduction(+:suma)
    for(int i = 1; i <= n ; i++)     // Calcula el área de cada rectángulo
    {
        long double x = inicio + delta * i; // Sumando i vamos cambiando de rectangulo
        long double y = sqrt(1 - (x*x)); // Altura del rectangulo
        long double area = delta * y; // El area del rectangulo
        suma += area;
    }
    return suma * 4.0; // Solo calculamos el area de un cuadrante del circulo.
}