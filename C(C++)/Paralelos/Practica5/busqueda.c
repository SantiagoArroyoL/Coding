#include <omp.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

double end;
int n = 10;
double start;
int elem = 5;
int a[10];

void inicia();
int busquedaBrecursive(int arr[], int e, int left, int right);
int busquedaBparalelo(int arr[], int e, int left, int right, int numHilos);


int main(int argc, char **argv) {
    if (argc < 2 ){
        printf("Por favor introduce el numero de hilos, minimo dos\n");
        exit(1);
    }
    int numHilos = atoi(argv[1]), index = 0;
    int left = 0, right = n-1;
    inicia();

    //secuencial
    start = omp_get_wtime();
    index = busquedaBrecursive(a, elem, left, right); //crashea con valores de n mas grandes a 100
    end = omp_get_wtime();
    printf("La busqueda secuencial tomo %f segundos\n", end - start);
    printf("El indice donde se encuentra elemento es: %d\n",index);

    //paralelo
    start = omp_get_wtime();
    index = busquedaBparalelo(a, elem, left, right, numHilos); //crashea con valores de n mas grandes a 100
    end = omp_get_wtime();
    printf("La busqueda paralela tomo %f segundos\n", end - start);
    printf("El indice donde se encuentra elemento es: %d\n",index);
}

int busquedaBrecursive(int arr[], int e, int left, int right){
    int middle = floor(left+right / 2);
    if (right < left){
        return -1;
    } else if(arr[middle] == e){
        return middle;
    } else if(arr[middle] < e){
        left = middle+1;
    } else {
        right = middle-1;
    }
    return busquedaBrecursive(arr, e, left, right);
}

int busquedaBparalelo(int arr[], int e, int left, int right, int numHilos){
    int i;
    int temp[numHilos];
    omp_set_num_threads(numHilos);
#pragma omp parallel private(i)
    {
        int id = omp_get_thread_num();
        i = busquedaBrecursive(arr, e, left, right);
        temp[id] = i;
    }
    for (int j = 0; j < numHilos; ++i) {
        if (temp[j] != -1) {
            return temp[j];
        }
    }
    return -1;
}

void inicia() {
    for (int i = 0; i < n; i++) {
        a[i] = i+1;
    }
}