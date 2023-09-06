/** @file vectores.c
 *  @date 02-03-2023
 *  @brief Programa para operaciones elementales en vectores muy grandes
 *
 *  Vamos a implementar las operaciones de la suma de vectores y el producto punto,
 *   comparando sus tiempos en paralelo y en secuencial.
 *
 *  @author Santiago Arroyo
 */
#include <stdlib.h>
#include <stdio.h>
#include <omp.h>
#include <sys/time.h>

int n = 80000000;
int arreglo_a[80000000];
int arreglo_b[80000000];
int arreglo_c[80000000];

int main(int argc, char **argv){
    if (argc < 2 ){
        printf("Por favor usa 2 o mas hilos\n");
        exit(1);
    }
    int numHilos = atoi(argv[1]);
    long int suma = 0, sumaHilo = 0, tiempo = 0;
    struct timeval inicio, fin;
    int idHilo;
    //Definimos el número de hilos en el codigo paralelo
    omp_set_num_threads(numHilos);
    printf("Nuestros arreglos son de tamanio %d\nUsamos %d hilos\n",n, numHilos);
    for (int i = 0;i < n; i++) {
        arreglo_a[i] = 1;
        arreglo_b[i] = 2;
    }
    gettimeofday(&inicio, NULL);

    // <<<<<<<<<<<<<<<<<<<<<<---------------SUMA DE VECTORES----------------->>>>>>>>>>>>>>>>>>>>>>>>>>
    // SUMA SECUENCIAL
    for (int i = 0; i < n; ++i) {
       arreglo_c[i] = arreglo_a[i]+arreglo_b[i];
    }
    gettimeofday(&fin, NULL); //guarda el tiempo al final del programa
    tiempo = (fin.tv_sec - inicio.tv_sec) * 1000000 + (fin.tv_usec - inicio.tv_usec);
    printf("La suma secuencial tarda %ld microsegundos\n", tiempo);

    // SUMA PARALELA
#pragma omp parallel for
        for (int i = 0; i < n; i++) {
            arreglo_c[i] = arreglo_a[i] + arreglo_b[i];
        }
    gettimeofday(&fin, NULL);
    tiempo = (fin.tv_sec - inicio.tv_sec) * 1000000 + (fin.tv_usec - inicio.tv_usec);
    printf("La suma paralela tarda %ld microsegundos\n", tiempo);



    // <<<<<<<<<<<<<<<<<<<<<<---------------PRODUCTO PUNTO----------------->>>>>>>>>>>>>>>>>>>>>>>>>>
    // PRODUCTO PUNTO SECUENCIAL
    gettimeofday(&inicio, NULL); //guarda el tiempo al final del programa
    for (int i = 0; i < n; ++i) {
        suma += arreglo_a[i] * arreglo_b[i];
    }
    gettimeofday(&fin, NULL); //guarda el tiempo al final del programa
    tiempo = (fin.tv_sec - inicio.tv_sec) * 1000000 + (fin.tv_usec - inicio.tv_usec);
    printf("El producto punto secuencial nos da %ld y tarda %ld microsegundos\n",suma, tiempo);

    // PRODUCTO PUNTO PARALELO
    /* metodo 1*/
    // Vamos a dividir el arreglo en partes sin usar directivas extra de omp
    suma = 0;
    int rango = n / numHilos; //truncado
    int residuo = n % numHilos;
    gettimeofday(&inicio, NULL);
#pragma omp parallel private(idHilo, sumaHilo)
    {
        sumaHilo = 0;
        idHilo = omp_get_thread_num();
        int temp = rango * idHilo;
        for(int i = temp; i <= temp+rango-1; i++) {
            sumaHilo += arreglo_a[i] * arreglo_b[i];
        }
        suma += sumaHilo;
    }
    gettimeofday(&fin, NULL); //guarda el tiempo al final del programa
    tiempo = (fin.tv_sec - inicio.tv_sec) * 1000000 + (fin.tv_usec - inicio.tv_usec);
    printf("El producto punto paralelo 1 nos da %ld y tarda %ld microsegundos\n",suma, tiempo);

    /* metodo 2 */
    // metodo de Isra
    suma = 0;
    gettimeofday(&inicio, NULL);
#pragma omp parallel private(idHilo, sumaHilo)
    {
        sumaHilo = 0;
        idHilo = omp_get_thread_num();
        for(int i = idHilo; i < n; i+=numHilos) {
            sumaHilo += arreglo_a[i] * arreglo_b[i];
        }
        suma += sumaHilo;
    }
    gettimeofday(&fin, NULL); //guarda el tiempo al final del programa
    tiempo = (fin.tv_sec - inicio.tv_sec) * 1000000 + (fin.tv_usec - inicio.tv_usec);
    printf("El producto punto paralelo 2 nos da %ld y tarda %ld microsegundos\n",suma, tiempo);

    /* metodo 3 */
    // omp hace _todo el trabajo
    suma = 0;
    gettimeofday(&inicio, NULL);
#pragma omp parallel for reduction(+:suma)
        for(int i = 0; i < n; i++) {
            suma += arreglo_a[i] * arreglo_b[i];
        }
    gettimeofday(&fin, NULL); //guarda el tiempo al final del programa
    tiempo = (fin.tv_sec - inicio.tv_sec) * 1000000 + (fin.tv_usec - inicio.tv_usec);
    printf("El producto punto paralelo 3 nos da %ld y tarda %ld microsegundos\n",suma, tiempo);
}