/** @file reinas.c
 *  @date 10-05-2023
 *  @brief Programa que ejecuta mergesort en paralelo
 *
 *  Vamos a implementar merge sort en paralelo usando una directiva interesante de OpenMP
 *  La parte secuencial del codigo salio completamente de https://www.geeksforgeeks.org/c-program-for-merge-sort/
 *
 *  De ahi partiremos para hacer merge sort en paralelo
 *
 *  @author Santiago Arroyo
 */
#include <stdio.h>
#include <stdlib.h>
#include <omp.h>

double start,end;

/**
 * Combina dos subarreglos ordenados en uno solo.
 * @param arr El arreglo que contiene los elementos
 * @param left Indice del primer elemento del primer subarreglo.
 * @param mid Indice del ultimo elemento del primer subarreglo.
 * @param right Indice del ultimo elemento del segundo subarreglo.
 */
void mergeP(int arr[], int left, int mid, int right) {
    int i, j, k;
    int n1 = mid - left + 1;
    int n2 = right - mid;
    // Crear arreglos temporales
    int* L = (int*) malloc(n1 * sizeof(int));
    int* R = (int*) malloc(n2 * sizeof(int));
    // Copiar datos a los arreglos temporales L[] y R[]
    for (i = 0; i < n1; i++)
        L[i] = arr[left + i];
    for (j = 0; j < n2; j++)
        R[j] = arr[mid + 1 + j];
    // Combinar los arreglos temporales de nuevo en arr[left..right]
    i = 0;
    j = 0;
    k = left;
    while (i < n1 && j < n2) {
        if (L[i] <= R[j]) {
            arr[k] = L[i];
            i++;
        } else {
            arr[k] = R[j];
            j++;
        }
        k++;
    }
    // Copiar los elementos restantes de L[], si hay alguno
    while (i < n1) {
        arr[k] = L[i];
        i++;
        k++;
    }
    // Copiar los elementos restantes de R[], si hay alguno
    while (j < n2) {
        arr[k] = R[j];
        j++;
        k++;
    }
    // Liberamos memoria
    free(L);
    free(R);
}

/**
 * Ordena un arreglo utilizando el algoritmo Merge Sort con OpenMP.
 * Cuando se encuentra la directiva #pragma omp section,
 * el bloque de código dentro de ella se asigna a uno de los hilos disponibles
 * en el equipo de hilos creado por la directiva #pragma omp parallel sections.
 * Cada sección se ejecuta en paralelo,
 * lo que permite que las dos mitades del arreglo se ordenen simultáneamente en hilos diferentes.
 * @param arr El arreglo que se va a ordenar.
 * @param left Indice del primer elemento del arreglo a ordenar.
 * @param right Indice del ultimo elemento del arreglo a ordenar.
 */
void mergeSortP(int arr[], int left, int right) {
    if (left < right) {
        int mid = left + (right - left) / 2;
#pragma omp parallel sections
        {
#pragma omp section
            {
                // Seccion 1: Ordenar la primera mitad del arreglo
                mergeSortP(arr, left, mid);
            }
#pragma omp section
            {
                // Seccion 2: Ordenar la segunda mitad del arreglo
                mergeSortP(arr, mid + 1, right);
            }
        }
        // Combinar las dos mitades ordenadas
        mergeP(arr, left, mid, right);
    }
}

// Merges two subarrays of arr[].
// First subarray is arr[l..m]
// Second subarray is arr[m+1..r]
void merge(int arr[], int l,
           int m, int r)
{
    int i, j, k;
    int n1 = m - l + 1;
    int n2 = r - m;
    // Create temp arrays
    int L[n1], R[n2];
    // Copy data to temp arrays
    // L[] and R[]
    for (i = 0; i < n1; i++)
        L[i] = arr[l + i];
    for (j = 0; j < n2; j++)
        R[j] = arr[m + 1 + j];
    // Merge the temp arrays back
    // into arr[l..r]
    // Initial index of first subarray
    i = 0;
    // Initial index of second subarray
    j = 0;
    // Initial index of merged subarray
    k = l;
    while (i < n1 && j < n2)
    {
        if (L[i] <= R[j])
        {
            arr[k] = L[i];
            i++;
        }
        else
        {
            arr[k] = R[j];
            j++;
        }
        k++;
    }
    // Copy the remaining elements
    // of L[], if there are any
    while (i < n1) {
        arr[k] = L[i];
        i++;
        k++;
    }
    // Copy the remaining elements of
    // R[], if there are any
    while (j < n2)
    {
        arr[k] = R[j];
        j++;
        k++;
    }
}

// l is for left index and r is
// right index of the sub-array
// of arr to be sorted
void mergeSort(int arr[],
               int l, int r)
{
    if (l < r)
    {
        // Same as (l+r)/2, but avoids
        // overflow for large l and h
        int m = l + (r - l) / 2;

        // Sort first and second halves
        mergeSort(arr, l, m);
        mergeSort(arr, m + 1, r);

        merge(arr, l, m, r);
    }
}

// UTILITY FUNCTIONS
// Function to print an array
void printArray(int A[], int size)
{
    int i;
    for (i = 0; i < size; i++)
        printf("%d ", A[i]);
    printf("\n");
}

int main() {
    int arr[] = { 12, 11, 13, 5, 6, 7 };
    int arrP[] = { 12, 11, 13, 5, 6, 7 };
    int n = sizeof(arr) / sizeof(arr[0]);
    /* Secuencial */
    /* Secuencial */
    /* Secuencial */
    start = omp_get_wtime();
    printf("Given array is \n");
    printArray(arr, n);

    mergeSort(arr, 0, n - 1);

    printf("\nSorted array is \n");
    printArray(arr, n);
    end = omp_get_wtime();
    printf("Ordenar el arreglo en secuencial tomo %f segundos\n", end - start);

    /* Paralelo */
    /* Paralelo */
    /* Paralelo */
    /* Paralelo */
    start = omp_get_wtime();
    printf("Arreglo original:\n");
    printArray(arrP, n);
    mergeSortP(arrP, 0, n - 1);
    printf("\nArreglo ordenado:\n");
    printArray(arrP, n);
    end = omp_get_wtime();
    printf("Ordenar el arreglo en paralelo tomo %f segundos\n", end - start);
    return 0;
}
