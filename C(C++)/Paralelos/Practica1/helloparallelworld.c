//
// Created by sal on 23/02/23.
//
#include <stdio.h>
#include <omp.h>

int main(int argc, char **argv){
    #pragma omp parallel
    {
        printf("Hello Parallel Word!!!\n");
    }
    return 0;
}