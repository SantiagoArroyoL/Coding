/** @file suma.c
 *  @date 23-02-2023
 *  @brief Programa que suma del 0 al 1,000,000 (un millon) de forma secuencial y paralela
 *
 *  @author Santiago Arroyo
 */
#include <stdlib.h>
#include <stdio.h>
#include <omp.h>
#include <sys/time.h>

/* prototipos */
long int sumaSecuencial();
long int sumaParalela(int numHilos);

int main(int argc, char **argv){
    if (argc < 2 ) {
        printf("Por favor usa 2 o mas hilos\n");
        exit(1);
    }
    int numHilos = atoi(argv[1]);
    long int tiempo = 0, suma = 0;
    struct timeval inicio, fin;

    /* suma secuencial */
    gettimeofday(&inicio, NULL);
    suma = sumaSecuencial();
    gettimeofday(&fin, NULL); //guarda el tiempo al final del programa
    tiempo = (fin.tv_sec - inicio.tv_sec) * 1000000 + (fin.tv_usec - inicio.tv_usec);
    printf("La suma secuencial nos da %ld y tarda, %ld microsegundos\n",suma, tiempo);

    /* suma paralela */
    gettimeofday(&inicio, NULL);
    suma = sumaParalela(numHilos);
    gettimeofday(&fin, NULL); //guarda el tiempo al final del programa
    tiempo = (fin.tv_sec - inicio.tv_sec) * 1000000 + (fin.tv_usec - inicio.tv_usec);
    printf("La suma paralela nos da %ld y tarda, %ld microsegundos\n",suma, tiempo);
}

/**
 * @brief Suma secuencial de 1 a 1000000
 * @return el valor de la suma
 */
long int sumaSecuencial() {
    long int suma = 0;
    for(int i = 1; i <= 1000000; i++){
        suma += i;
    }
    return suma;
}

/**
 * @brief Suma secuencial de 1 a 1000000
 * @param numHilos - numero de hilos a utilizar en el calculo
 * @return el valor de la suma
 */
long int sumaParalela(int numHilos) {
    int idHilo;
    long int suma = 0, sumaHilo = 0;
    //Definimos el número de hilos en el codigo paralelo
    omp_set_num_threads(numHilos);
    printf("Iniciando calculo con %d hilos\n", numHilos);
    #pragma omp parallel private(idHilo, sumaHilo)
    {
        idHilo = omp_get_thread_num();
        sumaHilo = 0;
        for(int i = idHilo; i <= 1000000; i+=numHilos) {
            sumaHilo += i;
        }
        suma+= sumaHilo;
    }
    return suma;
}