#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <netinet/in.h>

void cifra(char *msg);
void descifra(char *msg);
void error(char *mensaje);
void RC4(char *llave, char *mensaje, unsigned char *K);
void desencriptar(char *cifrado, char *k, char *descifrado);
void encriptar(char *mensaje, char *k, unsigned char *cifrado);

int main(int argc, char *argv[]) {
    if (argc < 3) {
        fprintf(stderr, "Uso: %s <direccion IP> <puerto>\n", argv[0]);
        return 1;
    }

    int sockfd;
    struct sockaddr_in host_addr;

    if ((sockfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
        error("Error al crear socket\n");
    memset(&host_addr, 0, sizeof(host_addr));
    host_addr.sin_family = AF_INET;
    host_addr.sin_port = htons(atoi(argv[2]));

    if (inet_pton(AF_INET, argv[1], &host_addr.sin_addr) <= 0)
        error("Error al leer direccion IP de servidor\n");
    if (connect(sockfd, (struct sockaddr *)&host_addr, sizeof(host_addr)) < 0)
        error("Error al conectarse a servidor\n");

    // ------------ Menu -------------

    int numero;
    char *msg = (char *)calloc(4096, sizeof(char));
    size_t msg_len = strlen(msg);
    size_t received_len;
    memset(msg, 0, strlen(msg));    

    printf("Elige una opcion:\n");
    printf("1. Listar archivos\n");
    printf("2. Enviar mensaje secreto\n\n");

    scanf("%d", &numero);

    if (numero == 1) {
        // Enviar la opción al servidor
        msg = "1";
        cifra(msg);
        msg_len = strlen(msg);
        send(sockfd, &msg_len, sizeof(msg_len), 0);
        send(sockfd, msg, msg_len, 0);

        // Recibir y mostrar el listado de archivos 
        recv(sockfd, &received_len, sizeof(received_len), 0);
        recv(sockfd, msg, received_len, MSG_WAITALL);
        // descifra(msg);
        printf("Escoge un mensaje a leer:\n%s\n", msg);
        // memset(msg, 0, strlen(msg));
        
        scanf("%s", msg);
        // cifra(msg);
        msg_len = strlen(msg);
        send(sockfd, &msg_len, sizeof(msg_len), 0);
        send(sockfd, msg, msg_len, 0);
        // memset(msg, 0, strlen(msg));
        
        // Finalizamos
        recv(sockfd, &received_len, sizeof(received_len), 0);
        recv(sockfd, msg, received_len, MSG_WAITALL); 
        // descifra(msg);
        printf("Contenido del mensaje secreto:\n\n%s", msg);
        // memset(msg, 0, strlen(msg));
    } else if (numero == 2) {
        // Enviar la opción al servidor
        msg = "2";
        // cifra(msg);
        msg_len = strlen(msg);
        send(sockfd, &msg_len, sizeof(msg_len), 0);
        send(sockfd, msg, msg_len, 0);
        // memset(msg, 0, 4096);

        printf("Manda el contenido de la nota:\n");
        scanf(" %[^\n]", &msg);
        
        // cifra(msg);
        printf("Mensaje : %s\n", msg);
        msg_len = strlen(msg);
        printf("LEN : %d\n", msg_len);
        send(sockfd, &msg_len, sizeof(msg_len), 0);
        send(sockfd, msg, msg_len, 0);
        // memset(msg, 0, strlen(msg));

        recv(sockfd, &received_len, sizeof(received_len), 0);
        recv(sockfd, msg, received_len, MSG_WAITALL);
        // descifra(msg);
        printf("Archivo creado con el nombre que inicia en: %s\n", msg);
        // memset(msg, 0, strlen(msg));
    } else {
        error("Error al leer el número. Por favor escribe solamente numeros enteros\n");
    }
    close(sockfd);
    free(msg);
    return 0;
}

