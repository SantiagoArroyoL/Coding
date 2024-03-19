#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct par{
    int a;
    int b;
};


void voltea(int *a,int *b){
    //* significa "lo que está guardado en"
    //si a es apuntador, *a devuelve lo que está guardado en a 
    int tmp = *a;
    //asignar el valor en *b hacia *a
    *a=*b;
    *b=tmp;
}

void funcionDeFuncion(void (*f)(int *,int *), int *i, int *j){
    //suma 1 a cada valor
    *i = *i+1;
    *j = *j+1;
    //llama a la función
    (*f)(i,j);
    
    //imprime
    printf("i=%i,j=%i\n",*i,*j);
    
}

void funcionImprimeGen(void* elem, int tipo){
    switch(tipo){
        case 0: printf("%i\n",*((int*) elem));
            break;
        case 1: printf("%c\n",*((char*) elem));
            break;
        case 2: printf("%s\n",((char*) elem));
            break;
        case 3: printf("%f\n",*((float*) elem));
            break;
        default:;
    }
}

int main(int argc, char *argv[]){
//int main() {
    //pruebas generales
    printf("Hello, World! \n");
	int a,b;
	float c,d;
	a = 15;
	b = a / 2;
	printf("%d\n",b);
	printf("%3d\n",b);
	printf("%03d\n",b);
	c = 15.3;
	d = c / 3;
	printf("%3.2f\n",d);
	
	printf("The color: %s\n", "blue");
	printf("First number: %d\n", 12345);
	printf("Second number: %04d\n", 25);
	printf("Third number: %i\n", 1234);
	printf("Float number: %3.2f\n", 3.14159);
	printf("Hexadecimal: %x\n", 255);
	printf("Octal: %o\n", 255);
	printf("Unsigned value: %u\n", -150);
	printf("Just print the percentage sign %%\n");
    // 7
    //   7
    // 007
    // 5.10 
    // The color: blue
    // First number: 12345
    // Second number: 0025
    // Third number: 1234
    // Float number: 3.14
    // Hexadecimal: ff
    // Octal: 377
    // Unsigned value: 150
    // Just print the percentage sign %

    char e = 'e';
    char* string1 = "asdf";

    printf("%c,%s\n",e,string1);
    char* string2 ="aaaaaaaa";
    char* result;
    
    //exclusiva de gnu
    asprintf(&result, "%s%s", string1, string2);

    printf("%s\n",result);
    
    //parte de string.h
    char string3 [20] = "bbb";
    strcat(string3,string2);
    printf("%s\n",string3);
    
    
    //probando el intercambio de valores
    int x = 1;
    int y = 2;
    
    printf("%i,%i\n",x,y);
    voltea(&x,&y);
    printf("%i,%i\n",x,y);
    
    
    //probando un struct
    struct par par1 = {1,2};
    par1.a = 3;
    par1.b = 4;
    printf("%i,%i\n", par1.a,par1.b);
    
    struct par *par2 = malloc(sizeof(struct par));
    par2->a = 5;
    par2->b = 6;
    printf("%i,%i\n", par2->a,par2->b);
    
    
    //probando apuntador a void
    void* generico;
    generico = malloc(sizeof(int));
    int prueba1 = 99;
    char prueba2 = 'a';
    char* prueba3 = "string";
    float prueba4 = 1.2345;
    
    generico = &prueba1;
    
    printf("%i\n", *((int*) generico));
    
    generico = &prueba2;
    
    printf("%c\n", *((char*) generico));
    
    generico = prueba3;
    
    printf("%s\n", ((char*) generico));
    
    generico = &prueba4;
    
    printf("%f\n", *((float*) generico));
    
    //funcion que recibe un void*
    
    funcionImprimeGen(&prueba1,0);
    funcionImprimeGen(&prueba2,1);
    funcionImprimeGen(prueba3,2);
    funcionImprimeGen(&prueba4,3);
    
    // probando funcion de funciones
    funcionDeFuncion(voltea,&x,&y);
    
    free(par2);
    
    return 0;
}