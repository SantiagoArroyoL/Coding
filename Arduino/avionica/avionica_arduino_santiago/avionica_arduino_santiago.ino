/*
 * Computadora de Vuelo Arduino Nano
 * Propulsion UNAM
 * 
 * @author Santiago Arroyo
 * 
 * @date 13/03/2022
 * 
 * https://aafi.space/coheteria
 * 
 * Se usa la conexion I2C hecha por Sebastian Polo
 * Este codigo modela el comportamiento de la computadora de Vuelo V2
 * Se spera que despliegue el paracaidas mientras se recopilan datos de acelerometro y barometro
 * El codigo cuenta con 3 estados que definen si se libera la carga explosiva o no.
 * En este archivo ademas se incluyen las direcciones necesarias para las distintas escalas de la IMU
 * REVISAR DIRECCIONES EEPROM Y OFFSET ACELEROMETRO!!!!!!!!!!!!!!!!!!!!!!
 */

#include <Wire.h>
#include <SD.h>
#include <EEPROM.h>
#include <avr/wdt.h>
#include <Adafruit_BMP085.h>

// [--- CONSTANTES ---]
#define MUESTRAS 6           // 6 alturas en el vector para media móvil
#define ALTURA_UMBRAL 30     // 30 [m] de caída para activación 

// [--- PINES ---]
#define LED 6
#define MOSFET 8
#define PIN_SD 10

// [--- DIRECCIONES EPPROM  ---]
#define DIR_ES_VUELO       7     // Estado de vuelo:      0 (Espera), 1 (Vuelo), 2 (Descenso terminado)
#define DIR_ALTURA_MAX     1     // Altura máxima:        0 -> 2000 [m] & 255 -> 4000 [m]
#define DIR_ALTURA_INICIAL 2     // Altura inicial:       0 -> 2000 [m] & 255 -> 4000 [m]
#define DIR_ACEL_INICIAL   3     // Aceleracion inicial:  0 -> 0 [g] & 255 -> 20 [g]
#define DIR_ACEL_MAX       4     // Aceleración máxima:   0 -> 0 [g] & 255 -> 20 [g]
#define DIR_TIEMPO_DET     5     // Tiempo Final:         0 -> 60 [s] & 255 -> 100 [s]
#define DIR_TIEMPO_CERO    6     // Tiempo Inicial:       0 -> 60 [s] & 255 -> 100 [s]

// [--- REGISTROS MPU ---]
#define MPU6050_ADDRESS  0x69   // Dirección del módulo MPU6050 con su pin AD0 en ALTO
#define PWR_MGMT_1       0x6B   // Configuracion del modo de funcionamiento y selección del reloj
#define USER_CTRL        0x6A   // configuracion de FIFO, I2C y reset de los sens ores
#define CONFIG           0x1A   // Configuracion de el ancho de banda y frecuencia de muestreo
#define SMPRT_DIV        0x19   // Divisor de frecuencia de muestreo para el giroscopio y el Sample Rate
#define GYRO_CONFIG      0x1B   // Rango y resolución del giroscopio
#define ACCEL_CONFIG     0x1C   // Rango y resolución del acelerometro
#define INT_ENABLE       0x38   // Activa las interrupciones

// [--- REGISTROS ESCALAS ---]
#define GYRO_250_DPS     0x00  
#define GYRO_500_DPS     0x08
#define GYRO_1000_DPS    0x10
#define GYRO_2000_DPS    0x18
#define ACC_2_G          0x00  
#define ACC_4_G          0x08
#define ACC_8_G          0x10
#define ACC_16_G         0x18

// [--- REGISTROS ACELERACION SALIDA ---]
#define ACEL_X_H         0x3B
#define ACEL_X_L         0x3C
#define ACEL_Y_H         0x3D
#define ACEL_Y_L         0x3E
#define ACEL_Z_H         0x3F
#define ACEL_Z_L         0x40

// [--- REGISTROS GIROSCPIO SALIDA ---]
#define GYRO_X_H         0x43
#define GYRO_X_L         0x44
#define GYRO_Y_H         0x45
#define GYRO_Y_L         0x46
#define GYRO_Z_H         0x47
#define GYRO_Z_L         0x48

// [--- OFFSET SENSORES !!!!!!!!!!!!!!!!!!!!!!!!CAMBIAR POR CADA PCB !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! ---]
#define OFFSET_ACEL_X    -0.03
#define OFFSET_ACEL_Y    -0.03
#define OFFSET_ACEL_Z    0.03
#define OFFSET_GYRO_X    2.93
#define OFFSET_GYRO_Y    -2.38
#define OFFSET_GYRO_Z    0.73

// [------------------------- VARIABLES ---------------------------]

// [--- OBJETOS FILE Y BMP180 ---]
File archivo;
Adafruit_BMP085 bmp;

// [--- VARIABLES BMP ---]
float Temperatura;
float Presion;
float h_actual;
float h_max;              // Altura maxima
float alturas[MUESTRAS];  // Vector de alturas totales

// [--- VARIABLES ACELERACION ---]
float aX;                 // Aceleracion en X
float aY;                 // Aceleracion en Y
float aZ;                 // Aceleracion en Z
float aT;                 // Aceleración total filtrada con media móvil

// [--- VARIABLES GYRO ---]
float gX;                 // Aceleracion en X
float gY;                 // Aceleracion en Y
float gZ;                 // Aceleracion en Z

// [--- VARIABLES VARIAS ---]
float sum;                // Variable temporal
byte RAW[6];              // Datos en los registros del MPU

byte estadoVUELO;         // VARIABLE DEL ESTADO DE VUELO
byte N_archivos;          // numero de archivos en SD
byte seguro = 0;          // Inicializamos el seguro en 0 por seguridad
boolean detonacion = false;

// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]
// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]
// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]
// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]
// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]
// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]

/*
 * wireLectura
 * dispositivo - byte que registra el dispositovo a leer
 * direccion - byte que registra la direccion a leer
 * 
 * Regresa el byte en la direccion dada (Proceso de I2C detallado)
 */
byte wireLectura(byte dispositivo, byte direccion){
    Wire.beginTransmission(dispositivo); //[S][Address]
    Wire.write(direccion); //[W][->Ack][MemAddres] 
    Wire.endTransmission(); //[NACK][P]
    Wire.requestFrom(dispositivo,1); //[S][Addres][R][->Ack]
    return Wire.read(); //[->][Data][Nack][P] 
}

/*
 * wireEscritura
 * dispositivo - byte que registra el dispositovo a escribir
 * direccion - byte que registra la direccion a escribir
 * valor - byte que contiene el valor a escribir
 * 
 */
void wireEscritura(byte dispositivo, byte direccion, byte valor){
    Wire.beginTransmission(dispositivo); // [S][Addres]
    Wire.write(direccion); //[W][->Ack][MemAddres]             
    Wire.write(valor); //[Ack][DATA]
    Wire.endTransmission(); //[Nack][P]
}

/*
 * MPUinit()
 * Inicializamos el MPU como se especifica en cada lÃ­nea
 * Tambien INICIALIZAMOS las aceleraciones
 */
void MPUinit(){
      wireEscritura(MPU6050_ADDRESS,PWR_MGMT_1,0x08);     // Despiera al sensor, la fuente de reloj es el oscilador interno (8Mhz) y se desactiva el sensor de temperatura
      wireEscritura(MPU6050_ADDRESS,USER_CTRL,0x01);      // Desactiva FIFO, desactiva I2C master mode, limpia y resetea sensores y sus registros
      wireEscritura(MPU6050_ADDRESS,0x37,0x00);           // ... INT_PIN_CONFIG
      wireEscritura(MPU6050_ADDRESS,INT_ENABLE,0x00);     // Desactiva todas las interrupciones
      wireEscritura(MPU6050_ADDRESS,CONFIG,0x01);         // Frecuencia de muestreo de Acelerometro y giroscopio de 1[kHz] y delay de 2[ms]
      wireEscritura(MPU6050_ADDRESS,SMPRT_DIV,0x07);      // Sample rate = 1[kHz]/(1+7) = 125 [Hz]
      wireEscritura(MPU6050_ADDRESS,GYRO_CONFIG,GYRO_2000_DPS);    // Rango del giroscopio = 2000 [deg/s] (16.4 [LSB/deg/s])
      wireEscritura(MPU6050_ADDRESS,ACCEL_CONFIG,ACC_16_G);        // Rango del acelerometro = 16 [g] (2048 [LSB/g])
}

/*
 * acelLectura()
 * Leemos los datos del acelerometro y los convertimos a flotantes
 * Debemos normalizar los datos respecto a la escala
 */
void acelLectura(){
      RAW[0] = wireLectura(MPU6050_ADDRESS, ACEL_X_H);
      RAW[1] = wireLectura(MPU6050_ADDRESS, ACEL_X_L);
      RAW[2] = wireLectura(MPU6050_ADDRESS, ACEL_Y_H);
      RAW[3] = wireLectura(MPU6050_ADDRESS, ACEL_Y_L);
      RAW[4] = wireLectura(MPU6050_ADDRESS, ACEL_Z_H);
      RAW[5] = wireLectura(MPU6050_ADDRESS, ACEL_Z_L);
      aX = (float)((RAW[0] << 8) | RAW[1])/2048.0+OFFSET_ACEL_X;
      aY = (float)((RAW[2] << 8) | RAW[3])/2048.0+OFFSET_ACEL_Y;
      aZ = (float)((RAW[4] << 8) | RAW[5])/2048.0+OFFSET_ACEL_Z;
}

/*
 * gyroLectura()
 * Leemos los datos del giroscopio y los convertimos a flotantes
 * Debemos normalizar los datos respecto a la escala
 */
void gyroLectura() {
      RAW[0] = wireLectura(MPU6050_ADDRESS, GYRO_X_H);
      RAW[1] = wireLectura(MPU6050_ADDRESS, GYRO_X_L);
      RAW[2] = wireLectura(MPU6050_ADDRESS, GYRO_Y_H);
      RAW[3] = wireLectura(MPU6050_ADDRESS, GYRO_Y_L);
      RAW[4] = wireLectura(MPU6050_ADDRESS, GYRO_Z_H);
      RAW[5] = wireLectura(MPU6050_ADDRESS, GYRO_Z_L);
      gX = (float)((RAW[0] << 8) | RAW[1])/16.4+OFFSET_GYRO_X;
      gY = (float)((RAW[2] << 8) | RAW[3])/16.4+OFFSET_GYRO_Y;
      gZ = (float)((RAW[4] << 8) | RAW[5])/16.4+OFFSET_GYRO_Z;
}

/*
 * calibracionALtura
 * Medicion de la altura inicial
 * Hacemos la media de 40 alturas medidas por el BMP para calibrar nuestras alturas iniciales
 */
void calibracionAltura() {
    sum = 0;
    for(byte i = 0; i < MUESTRAS; i++)
        alturas[i] = 1;
    for(byte j = 0; j < 40; j++)
        sum += bmp.readAltitude();
    h_max = sum/40.0;
    EEPROM.write(DIR_ALTURA_INICIAL,map((int)(h_max),2000,4000,0,255));
}

/*
 * cuentaChiles
 * Leemos el archivo contador.txt que contiene el número de archivos en la SD
 */
void cuentaChiles() {
    archivo = SD.open("contador.txt", FILE_WRITE);
    if(archivo) {
        archivo.seek(archivo.position()-1);
        N_archivos = ((int) archivo.read())-48;
        archivo.print(N_archivos+1);
        archivo.close();
    } else
        N_archivos = 0;    
}

/*
 * revisaVuelo
 * Calcularemos la altura media y revisaremos si es mayor que la altura maxima
 * Si no lo es revisaremos la condición de caída. 
 * Si estamos cayendo escribimos en la EEPROM la altura maxima y finalmente detonamos
 * Se hacen 3 revisiones particulares
 */
void revisaVuelo(){
    if(detonacion) { // 1. si ya detonamos => nada
        return;
    } else if(h_actual > h_max) { // 2. revisa despegue => cambia estado
        h_max = h_actual;
        if(estadoVUELO == 0) {
            if((h_actual-h_max) > ALTURA_UMBRAL || aT > 5) {
              estadoVUELO = 1;
            }
        }    
    } else if((h_max-h_actual) > ALTURA_UMBRAL || aT == 0){ // 3. revisa caida y paracaidas => despliega
        if(seguro > 0 && estadoVUELO == 1) {
            digitalWrite(MOSFET,HIGH); //CARGA EXPLOSIVA!
            detonacion = true;
            digitalWrite(LED,HIGH);
            estadoVUELO = 2;           
            delay(2000);
            digitalWrite(MOSFET,LOW); //Apagar carga
        }
        EEPROM.write(DIR_ES_VUELO,estadoVUELO);
        EEPROM.write(DIR_ALTURA_MAX,(byte)map(h_max,2000,4000,0,255));
        EEPROM.write(DIR_TIEMPO_DET,(byte)map((millis()),60000,200000,0,255));
    }
}

byte formateaSBD_DET(){
    return 0x000|(0 << 3)|(estadoVUELO << 4); // seguro
}

// [------------------------------------------------------ SET UP y LOOP ------------------------------------------------------]
// [------------------------------------------------------ SET UP y LOOP ------------------------------------------------------]
// [------------------------------------------------------ SET UP y LOOP ------------------------------------------------------]
// [------------------------------------------------------ SET UP y LOOP ------------------------------------------------------]
// [------------------------------------------------------ SET UP y LOOP ------------------------------------------------------]
// [------------------------------------------------------ SET UP y LOOP ------------------------------------------------------]

/*
 * setup()
 * Configuramos todo. Este código se corre solo una vez al prender el Arduino 
 */
void setup() {
    /* Iniciar las salidas */
    pinMode(LED,OUTPUT);
    pinMode(MOSFET,OUTPUT);
    digitalWrite(MOSFET,LOW);
    digitalWrite(LED,LOW);    
    
    // [---  Comunicacion I2C ---]
    Wire.begin();
    
    // [--- BMP180 ---]
    while(!bmp.begin(1)) {
        digitalWrite(LED,HIGH);
        delay(500);
        digitalWrite(LED,LOW);
        delay(500);
    }
    calibracionAltura();
    
    // [--- MPU9250 ---]
    MPUinit();

    // [--- Revisar estado de vuelo anterior ---]
//    estadoVUELO = EEPROM.read(DIR_ES_VUELO);
    estadoVUELO = 0; //Esta linea se usa para debugging, comentar si se quiere usar EEPROM
    seguro = 1; // SOLO PARA DEBUGGING, COMENTAR EN OTRO CASO
    
    if(estadoVUELO == 1) {
        h_actual = bmp.readAltitude();
        revisaVuelo(); // AQUI SE PUEDE LIBERAR CARGA EXPLOSIVA
    }

    // [--- TARJETA SD ---]
    if(!SD.begin(PIN_SD))
      digitalWrite(LED,HIGH);       

    // [--- CSV ---]
    cuentaChiles();
    archivo = SD.open("D"+String(N_archivos)+".csv", FILE_WRITE);//abrimos o creamos el archivo
    if(archivo) {
        archivo.print("t_n,t_A,h_N,h_AT,temp_N,temp_AT,presion,");
        archivo.println("aX,aY,aZ,aT,gX,gY,gZ,SBD_DET");
        archivo.close();
    }
    wdt_enable(WDTO_1S);
    EEPROM.write(DIR_TIEMPO_CERO, map((int)(millis()),60000,200000,0,255));
}//Cierre SETUP


// [--- CICLO ---]
/*
 * loop()
 * El código dentro de esta función se repite indefinidamente
 * Se leen los datos de los sensores y los escribimos a la tarjeta SD
 * Se revisa el seguro del Attiny en cada ciclo
 * El LED se encenderá en caso de error
 */
void loop() { 
    archivo = SD.open("D"+String(N_archivos)+".csv", FILE_WRITE);
    Temperatura = bmp.readTemperature();
    Presion = bmp.readPressure();
    h_actual = bmp.readAltitude();
    revisaVuelo();
    acelLectura();
    gyroLectura();    
    aT = sqrt((aX*aX)+(aY*aY)+(aZ*aZ));
    if(archivo) {
        archivo.print(millis());
        archivo.print(",");
        archivo.print(0);
        archivo.print(",");
        archivo.print(h_actual);
        archivo.print(",");
        archivo.print(0);
        archivo.print(",");
        archivo.print(Temperatura);
        archivo.print(",");
        archivo.print(0);
        archivo.print(",");
        archivo.print(Presion);
        archivo.print(",");  
        archivo.print(gX);
        archivo.print(",");
        archivo.print(gY);
        archivo.print(",");
        archivo.print(gZ);
        archivo.print(",");
        archivo.print(aX);
        archivo.print(",");
        archivo.print(aY);
        archivo.print(",");
        archivo.print(aZ);
        archivo.print(",");
        archivo.println(aT);
        archivo.print(",");
        archivo.println(formateaSBD_DET(), HEX);    
        archivo.close();
    }
    wdt_reset();
}
/*
   *                 *                  *              *
                                                      *             *
                        *            *                             ___
  *               *                                          |     | |
        *              _________##                 *        / \    | |
                      @\\\\\\\\\##    *     |              |--o|===|-|
  *                  @@@\\\\\\\\##\       \|/|/            |---|   |P|
                    @@ @@\\\\\\\\\\\    \|\\|//|/     *   /     \  |r|
             *     @@@@@@@\\\\\\\\\\\    \|\|/|/         |  M    | |o|
                  @@@@@@@@@----------|    \\|//          |  E    |=|p|
       __         @@ @@@ @@__________|     \|/           |  X    | |u|
  ____|_@|_       @@@@@@@@@__________|     \|/           |_______| |_|
=|__ _____ |=     @@@@ .@@@__________|      |             |@| |@|  | |
____0_____0__\|/__@@@@__@@@__________|_\|/__|___\|/__\|/___________|_|_
 */
