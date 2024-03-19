#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <dirent.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <openssl/sha.h>

void cifra(char *msg);
void descifra(char *msg);
void error(char *mensaje);
void RC4(char *llave, char *mensaje, unsigned char *K);
void desencriptar(char *cifrado, char *k, char *descifrado);
void encriptar(char *mensaje, char *k, unsigned char *cifrado);

void calcularSHA256(const char *input, char *output) {
    unsigned char hash[SHA256_DIGEST_LENGTH];
    SHA256_CTX sha256;
    SHA256_Init(&sha256);
    SHA256_Update(&sha256, input, strlen(input));
    SHA256_Final(hash, &sha256);
    int i = 0;
    for(i = 0; i < SHA256_DIGEST_LENGTH; i++)
    {
        sprintf(output + (i * 2), "%02x", hash[i]);
    }
    output[64] = 0;
}

char *mostrarArchivo(const char *nombreArchivo) {
  FILE *archivo = fopen(nombreArchivo, "r");
  if (archivo == NULL) {
    perror("Error al abrir el archivo");
    exit(EXIT_FAILURE);
  }

  // Obtener el tamaño del archivo
  fseek(archivo, 0, SEEK_END);
  long tamano = ftell(archivo);
  fseek(archivo, 0, SEEK_SET);

  // Almacenar el contenido del archivo en una cadena
  char *contenido = malloc(tamano + 1);
  if (contenido == NULL) {
      perror("Error al asignar memoria");
      exit(EXIT_FAILURE);
  }

  fread(contenido, 1, tamano, archivo);
  contenido[tamano] = '\0'; 

  fclose(archivo);

  return contenido;
}

char *listarArchivos(char *directorio) {
    DIR *dir;
    struct dirent *ent;
    dir = opendir(directorio);
    char *listaArchivos = (char *)malloc(4096 * sizeof(char));

    if (dir == NULL) {
      perror("Error al abrir el directorio");
      exit(EXIT_FAILURE);
    }

    int temp = 0;
    // strcpy(listaArchivos, "");  // Limpiar la lista de archivos
    while ((ent = readdir(dir)) != NULL) {
      // Ignorar directorios . y ..
      if (strcmp(ent->d_name, ".") != 0 && strcmp(ent->d_name, "..") != 0) {
        temp = 1;
        sprintf(listaArchivos + strlen(listaArchivos), "\t- %s\n", ent->d_name);
      }
    }
    
    if (temp < 1)
      error("Primero debes crear un archivo!");
    closedir(dir);
    
    return listaArchivos;
}

void crear_archivo(char *msg, char *hash) {
    // Calcular el hash SHA-256
    calcularSHA256(msg, hash);

    // Crear un archivo con el nombre del hash
    char nombreArchivo[75];
    sprintf(nombreArchivo, "notas/%s.txt", hash);

    FILE *archivo = fopen(nombreArchivo, "w");
    if (archivo == NULL) {
        perror("Error al abrir el archivo");
        exit(EXIT_FAILURE);
    }

    fprintf(archivo, "%s", msg);
    fclose(archivo);
}

int main(int argc, char *argv[]) {
    if (argc < 2) {
        fprintf(stderr, "Uso: %s <puerto>\n", argv[0]);
        return 1;
    }
    int sockfd, cliente_sockfd, opt = 1;
    struct sockaddr_in host_addr, cliente_addr;
    socklen_t sin_tam = sizeof(struct sockaddr_in);

    if ((sockfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
        error("Error al crear el socket ");
    if (setsockopt(sockfd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(int)) < 0)
        error("Error en setsockopt \n");

    host_addr.sin_family = AF_INET;
    host_addr.sin_port = htons(atoi(argv[1]));
    host_addr.sin_addr.s_addr = INADDR_ANY;

    if (bind(sockfd, (struct sockaddr *)&host_addr, sizeof(struct sockaddr)) < 0)
        error("Error en bind \n");
    if (listen(sockfd, 5) < 0)
        error("Error en listen \n");

    char *msg = (char *)calloc(4096, sizeof(char));
    size_t msg_len = strlen(msg);
    size_t received_len;
    memset(msg, 0, strlen(msg));

    while (1) { 
        cliente_sockfd = accept(sockfd, (struct sockaddr *)&cliente_addr, &sin_tam);
        if (cliente_sockfd < 0)
            error("Error en accept \n");
        printf("Conexion aceptada desde %s: %d\n",
               inet_ntoa(cliente_addr.sin_addr), ntohs(cliente_addr.sin_port));

        // Recibir opcion   
        recv(cliente_sockfd, &received_len, sizeof(received_len), 0);
        recv(cliente_sockfd, msg, received_len, MSG_WAITALL);
        descifra(msg);

        if (strcmp(msg, "1") == 0) {
            // memset(msg, 0, strlen(msg));
            msg = listarArchivos("notas/");
            // Enviar el listado al cliente
            // cifra(msg);
            printf("PRE!\n");
            msg_len = strlen(msg);
            send(cliente_sockfd, &msg_len, sizeof(msg_len), 0);
            send(cliente_sockfd, msg, msg_len, 0);
            printf("TEMP!\n");
            // memset(msg, 0, strlen(msg));
            
            // Recibimos su respuesta
            recv(cliente_sockfd, &received_len, sizeof(received_len), 0);
            recv(cliente_sockfd, msg, received_len, MSG_WAITALL);
            // descifra(msg);
            printf("Archivo: %s\n", msg);

            char nombreArchivo[75]; 
            sprintf(nombreArchivo, "notas/%s", msg);
            // memset(msg, 0, strlen(msg));
            
            // Terminamos
            msg = mostrarArchivo(nombreArchivo);
            // cifra(mostrarArchivo(nombreArchivo));
            msg_len = strlen(msg);
            send(cliente_sockfd, &msg_len, sizeof(msg_len), 0);
            send(cliente_sockfd, msg, msg_len, 0);
            // memset(msg, 0, strlen(msg));
        } else if (strcmp(msg, "2") == 0) {
            // Recibimos mensaje y creamos archivo
            // memset(msg, 0, strlen(msg));
            recv(cliente_sockfd, &received_len, sizeof(received_len), 0);
            recv(cliente_sockfd, msg, received_len, MSG_WAITALL); 
            // descifra(msg);
            char *hash = malloc(sizeof(char) * 64);
            crear_archivo(msg, hash);
            // memset(msg, 0, strlen(msg));

            // Terminamos
            msg = hash;
            // cifra(msg);
            msg_len = strlen(msg);
            send(cliente_sockfd, &msg_len, sizeof(msg_len), 0);
            send(cliente_sockfd, msg, msg_len, 0);
            // memset(msg, 0, strlen(msg));
            free(hash);
        } else {
            error("Opción no válida");
        }
        // Cerrar la conexion
        close(cliente_sockfd);
    }
    free(msg);
    return 0;
}
// gcc servidor.c rc4.c -o servidor -lssl -lcrypto -w
