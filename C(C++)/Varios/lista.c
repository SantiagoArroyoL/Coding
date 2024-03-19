#include <stdio.h>
#include <stdlib.h>

//estructuras
struct nodo{
    int valor;
    struct nodo *siguiente;
};

struct lista{
    struct nodo *primero;
};

//función declarada al principio, por si se necesita usar antes de definirla
void agregaElementoInicio(struct lista *l, int elem);

//agregar un elemento en una posición dada, si la posición excede el tamaño, se pone al final
void agregaElementoIndice(struct lista *l, int elem, int pos){
    if(pos==0){
        agregaElementoInicio(l,elem);
    }
    else{
        struct nodo *temp;
        temp = l->primero;
        int i = 1;
        while((temp->siguiente != NULL)&&(i<pos)){
            temp = temp->siguiente;
            i++;
        }
        struct nodo *nuevo = malloc(sizeof(struct nodo));
        nuevo->siguiente = temp->siguiente;
        nuevo->valor = elem;
        temp->siguiente = nuevo;
    }
}

//agregar elemento al inicio
void agregaElementoInicio(struct lista *l, int elem){
    struct nodo *tmp = malloc(sizeof(struct nodo));
    tmp->siguiente = l->primero;
    tmp->valor = elem;
    l->primero = tmp;
}

/*
 * Este está mal
void agregaElementoFinal1(struct lista l, int elem){
    if((l.primero)==NULL){
        l.primero = malloc(sizeof(struct nodo)); 
        (l.primero)->valor = elem;
    }
}*/

//agregar elemento al final
void agregaElementoFinal(struct lista *l, int elem){
    if((l->primero) == NULL){
        l->primero = malloc(sizeof(struct nodo)); 
        (l->primero)->valor = elem;
    }
    else{
        struct nodo* tmp = l->primero;
        while((tmp->siguiente)!=NULL){
            tmp = tmp->siguiente;
        }
        tmp->siguiente = malloc(sizeof(struct nodo));
        (tmp->siguiente)->valor = elem;
    }
}

//imprimir los elementos de la lista
void imprimeLista(struct lista l){
    struct nodo *tmp = l.primero;
    while(tmp!=NULL){
        printf("%i\n",(tmp->valor));
        tmp=tmp->siguiente;
    }
}

int main(){
    struct lista li= {NULL};
    agregaElementoInicio(&li,1);
    agregaElementoInicio(&li,2);
    agregaElementoIndice(&li,3,1);
    agregaElementoFinal(&li,99);
    imprimeLista(li);
}