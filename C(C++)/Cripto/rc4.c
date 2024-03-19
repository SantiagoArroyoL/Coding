#include <stdio.h>
#include <string.h>
#include <stdlib.h>

char llave[] = "secreta"; 

void cifra(char *msg){
  unsigned char *cifrado = malloc(sizeof(unsigned char) * strlen(msg));
  unsigned char *K = malloc(strlen(msg));
  RC4(llave, msg, K);
  encriptar(msg, K, cifrado);
  msg = cifrado;
  free(K);
  free(cifrado);
} 

void descifra(char *msg){
  unsigned char *descifrado = malloc(sizeof(unsigned char) * strlen(msg));
  unsigned char *K = malloc(sizeof(unsigned char) * strlen(msg));
  RC4(llave, msg, K);

  desencriptar(msg, K, descifrado);
  msg = descifrado;
  free(K);
  free(descifrado);
}


void intercambia(unsigned char *a, unsigned char *b) {
    unsigned char temp = *a;
    *a = *b;
    *b = temp;
}

// Genera la cadena pseudoaleatoria K
void RC4(char *llave, char *mensaje, unsigned char *K) {
    /* KSA */
    int i;
    int j = 0;
    int n = strlen(llave);
    unsigned char t[256];
    unsigned char S[256];

    for (i = 0; i < 256; i++) {
        S[i] = i;
        t[i] = llave[i % n];
    }

    for (i = 0; i < 256; i++) {
        j = (j + S[i] + t[i]) % 256;
        intercambia(&S[i], &S[j]);
    }

    /* PRGA */
    i = j = 0;
    // Generación de la cadena pseudoaleatoria
    for (size_t temp = 0; temp < n; temp++) {
        i = (i + 1) % 256;
        j = (j + S[i]) % 256;
        intercambia(&S[i], &S[j]);
        int a = (S[i] + S[j]) % 256;
        K[temp] = a;
    }
}

// Encripta un mensaje con la cadena K
void encriptar(char *mensaje, char *k, unsigned char *cifrado) {
    for (int i = 0; i < strlen(mensaje); i++) {
        cifrado[i] = mensaje[i] ^ k[i];
    }
}

// Desencripta un mensaje con la cadena K
void desencriptar(unsigned char *cifrado, char *k, char *descifrado) {
    for (int i = 0; i < strlen(cifrado); i++) {
        descifrado[i] = cifrado[i] ^ k[i];
    }
}

/*int main() {
    char llave[] = "secreta";
    char msg[] = "Mensaje!";
    unsigned char *cifrado = malloc(sizeof(unsigned char) * strlen(msg));
    char *descifrado = malloc(sizeof(char) * strlen(msg));
    unsigned char K[strlen(msg)];

    RC4(llave, msg, K);
    encriptar(msg, K, cifrado);

    RC4(llave, cifrado, K);
    desencriptar(cifrado, K, descifrado);

    printf("%s", descifrado);

    free(cifrado);
    free(descifrado);

    return 0;
}*/

