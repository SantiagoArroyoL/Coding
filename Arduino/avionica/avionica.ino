// [--- LIBRERIAS ---]
#include <SD.h>
#include <Wire.h>
#include <EEPROM.h>
#include <Adafruit_BMP085.h>

// [--- PINES  ---]
#define PIN_SD 4
#define melodyPin 3
#define red_light_pin 8
#define green_light_pin 7
#define blue_light_pin 9

// [--- DIRECCIONES EPPROM  ---]
#define DIR_ES_VUELO       0     // Estado de vuelo:      0 (Espera), 1 (Vuelo), 2 (Descenso terminado)
#define DIR_ALTURA_MAX     1     // Altura máxima:        0 -> 2000 [m] & 255 -> 4000 [m]
#define DIR_ALTURA_INICIAL 2     // Altura inicial:       0 -> 2000 [m] & 255 -> 4000 [m]
#define DIR_ACEL_INICIAL   3     // Aceleracion inicial:  0 -> 0 [g] & 255 -> 20 [g]
#define DIR_ACEL_MAX       4     // Aceleración máxima:   0 -> 0 [g] & 255 -> 20 [g]
#define DIR_TIEMPO_DETONACION 5  // Tie,po Final:         0 -> 60 [s] & 255 -> 100 [s]

// [--- REGISTROS MPU ---]
#define MPU9250_ADDRESS  0x69   // Dirección del módulo MPU9250 con su pin AD0 en ALTO
#define PWR_MGMT_1       0x6B   // Configuracion del modo de funcionamiento y selección del reloj
#define USER_CTRL        0x6A   // configuracion de FIFO, I2C y reset de los sens ores
#define CONFIG           0x1A   // Configuracion de el ancho de banda y frecuencia de muestreo
#define SMPRT_DIV        0x19   // Divisor de frecuencia de muestreo para el giroscopio y el Sample Rate
#define GYRO_CONFIG      0x1B   // Rango y resolución del giroscopio
#define ACCEL_CONFIG     0x1C   // Rango y resolución del acelerometro
#define INT_ENABLE       0x38   // Activa las interrupciones

// [--- REGISTROS AK ---]
#define AK8963_ADDRESS   0x0C   // Dirección del módulo AK8963
#define AK8963_WHO_AM_I  0x00   // deberia regresar 0x48
#define AK8963_INFO      0x01   // sepa dios
#define AK8963_ST1       0x02   // data ready status bit 0
#define AK8963_ST2       0x09   // Data overflow bit 3 and data read error status bit 2
#define AK8963_CNTL      0x0A   // Power down (0000), single-measurement (0001), self-test (1000) and Fuse ROM (1111) modes on bits 3:0
#define AK8963_ASTC      0x0C   // Self test control
#define AK8963_I2CDIS    0x0F   // I2C disable
#define AK8963_ASAX      0x10   // Fuse ROM x-axis sensitivity adjustment value
#define AK8963_ASAY      0x11   // Fuse ROM y-axis sensitivity adjustment value
#define AK8963_ASAZ      0x12   // Fuse ROM z-axis sensitivity adjustment value

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

// [--- REGISTROS MAGENTOMETRO SALIDA ---]
#define MAGNET_X_L       0x03
#define MAGNET_X_H       0x04
#define MAGNET_Y_L       0x05
#define MAGNET_Y_H       0x06
#define MAGNET_Z_L       0x07
#define MAGNET_Z_H       0x08

// [--- CONSTANTES ---]
#define MUESTRAS 6           // 6 datos en el vector para media móvil
#define ALTURA_UMBRAL 30     // 30 [m] de caída para activación 

// [--- NOTAS BUZZER ---]
#define NOTE_B0  31
#define NOTE_C1  33
#define NOTE_CS1 35
#define NOTE_D1  37
#define NOTE_DS1 39
#define NOTE_E1  41
#define NOTE_F1  44
#define NOTE_FS1 46
#define NOTE_G1  49
#define NOTE_GS1 52
#define NOTE_A1  55
#define NOTE_AS1 58
#define NOTE_B1  62
#define NOTE_C2  65
#define NOTE_CS2 69
#define NOTE_D2  73
#define NOTE_DS2 78
#define NOTE_E2  82
#define NOTE_F2  87
#define NOTE_FS2 93
#define NOTE_G2  98
#define NOTE_GS2 104
#define NOTE_A2  110
#define NOTE_AS2 117
#define NOTE_B2  123
#define NOTE_C3  131
#define NOTE_CS3 139
#define NOTE_D3  147
#define NOTE_DS3 156
#define NOTE_E3  165
#define NOTE_F3  175
#define NOTE_FS3 185
#define NOTE_G3  196
#define NOTE_GS3 208
#define NOTE_A3  220
#define NOTE_AS3 233
#define NOTE_B3  247
#define NOTE_C4  262
#define NOTE_CS4 277
#define NOTE_D4  294
#define NOTE_DS4 311
#define NOTE_E4  330
#define NOTE_F4  349
#define NOTE_FS4 370
#define NOTE_G4  392
#define NOTE_GS4 415
#define NOTE_A4  440
#define NOTE_AS4 466
#define NOTE_B4  494
#define NOTE_C5  523
#define NOTE_CS5 554
#define NOTE_D5  587
#define NOTE_DS5 622
#define NOTE_E5  659
#define NOTE_F5  698
#define NOTE_FS5 740
#define NOTE_G5  784
#define NOTE_GS5 831
#define NOTE_A5  880
#define NOTE_AS5 932
#define NOTE_B5  988
#define NOTE_C6  1047
#define NOTE_CS6 1109
#define NOTE_D6  1175
#define NOTE_DS6 1245
#define NOTE_E6  1319
#define NOTE_F6  1397
#define NOTE_FS6 1480
#define NOTE_G6  1568
#define NOTE_GS6 1661
#define NOTE_A6  1760
#define NOTE_AS6 1865
#define NOTE_B6  1976
#define NOTE_C7  2093
#define NOTE_CS7 2217
#define NOTE_D7  2349
#define NOTE_DS7 2489
#define NOTE_E7  2637
#define NOTE_F7  2794
#define NOTE_FS7 2960
#define NOTE_G7  3136
#define NOTE_GS7 3322
#define NOTE_A7  3520
#define NOTE_AS7 3729
#define NOTE_B7  3951
#define NOTE_C8  4186
#define NOTE_CS8 4435
#define NOTE_D8  4699
#define NOTE_DS8 4978

// [--- OBJETOS FILE Y BMP180 ---]
File archivo;
Adafruit_BMP085 bmp;

// [--- VARIABLES ACELERACION ---]
byte acelRAW[6];        // Datos en los registros del acelerometro
float aX;               // Aceleracion en X
float aY;               // Aceleracion en Y
float aZ;               // Aceleracion en Z
float aT;         // Aceleración total filtrada con media móvil
float aceleraciones[MUESTRAS];  // Vector de aceleraciones totales
float acel_max;

// [--- VARIABLES GYRO ---]
byte gyroRAW[6];      // Datos en los registros del giroscopio
float gX;             // Aceleracion en X
float gY;             // Aceleracion en Y
float gZ;             // Aceleracion en Z

// [--- VARIABLES MAGNET ---]
byte magnetRAW[6];      // Datos en los registros del magnetometro
float mX;             // magnet en X
float mY;             // magnet en Y
float mZ;             // magnet en Z

// [--- VARIABLES BMP ---]
float Temperatura;
float Presion;
float Altitud;
float h_0;          // Altura inicial
float h_media;      // Altura media
float h_max;        // Altura maxima
float alturas[MUESTRAS];  // Vector de alturas totales

// [--- VARIABLES VARIAS ---]
byte estadoVUELO = 0;
boolean detonacion = false;
boolean seguro = false;
int8_t N_archivos; // numero de archivos en SD
float sum; //Variable temporal, que nos ayudará con los calculos
int state;


// [--- CONSTANTES CANCIONES ---]
//Cancion de mario
//const int melody[] PROGMEM = {
const int melody[] = {
  NOTE_E7, NOTE_E7, 0, NOTE_E7,
  0, NOTE_C7, NOTE_E7, 0,
  NOTE_G7, 0, 0,  0,
  NOTE_G6, 0, 0, 0,

  NOTE_C7, 0, 0, NOTE_G6,
  0, 0, NOTE_E6, 0,
  0, NOTE_A6, 0, NOTE_B6,
  0, NOTE_AS6, NOTE_A6, 0,

  NOTE_G6, NOTE_E7, NOTE_G7,
  NOTE_A7, 0, NOTE_F7, NOTE_G7,
  0, NOTE_E7, 0, NOTE_C7,
  NOTE_D7, NOTE_B6, 0, 0,

  NOTE_C7, 0, 0, NOTE_G6,
  0, 0, NOTE_E6, 0,
  0, NOTE_A6, 0, NOTE_B6,
  0, NOTE_AS6, NOTE_A6, 0,

  NOTE_G6, NOTE_E7, NOTE_G7,
  NOTE_A7, 0, NOTE_F7, NOTE_G7,
  0, NOTE_E7, 0, NOTE_C7,
  NOTE_D7, NOTE_B6, 0, 0
};

//Mario main them tempo
//const int tempo[] PROGMEM = {
const int8_t tempo[] = {
  12, 12, 12, 12,
  12, 12, 12, 12,
  12, 12, 12, 12,
  12, 12, 12, 12,

  12, 12, 12, 12,
  12, 12, 12, 12,
  12, 12, 12, 12,
  12, 12, 12, 12,

  9, 9, 9,
  12, 12, 12, 12,
  12, 12, 12, 12,
  12, 12, 12, 12,

  12, 12, 12, 12,
  12, 12, 12, 12,
  12, 12, 12, 12,
  12, 12, 12, 12,

  9, 9, 9,
  12, 12, 12, 12,
  12, 12, 12, 12,
  12, 12, 12, 12,
};

//Tono de error
//const int error_melody[] PROGMEM = {
const int error_melody[] = {
  NOTE_E5, NOTE_E5, NOTE_E5, NOTE_E5,
  NOTE_C7, NOTE_C7, NOTE_C7, NOTE_C7,
  NOTE_E5, NOTE_E5, NOTE_E5, NOTE_E5,
  NOTE_C7, NOTE_C7, NOTE_C7, NOTE_C7,

  NOTE_E5, NOTE_E5, NOTE_E5, NOTE_E5,
  NOTE_C7, NOTE_C7, NOTE_C7, NOTE_C7,
  NOTE_E5, NOTE_E5, NOTE_E5, NOTE_E5,
  NOTE_C7, NOTE_C7, NOTE_C7, NOTE_C7
};

//Error tempo
//const int error_tempo[] PROGMEM = {
const int8_t error_tempo[] = {
  12, 12, 12, 12,
  12, 12, 12, 12,
  12, 12, 12, 12,
  12, 12, 12, 12,

  12, 12, 12, 12,
  12, 12, 12, 12,
  12, 12, 12, 12,
  12, 12, 12, 12
};

//Tono de busqueda
//const int buscar_melody[] PROGMEM = {
const int buscar_melody[] = {
  NOTE_DS8, NOTE_DS8, NOTE_CS8, NOTE_CS8,
  NOTE_DS8, NOTE_DS8, NOTE_CS8, NOTE_CS8,
  NOTE_DS8, NOTE_DS8, NOTE_CS8, NOTE_CS8,
  NOTE_DS8, NOTE_DS8, NOTE_CS8, NOTE_CS8,

  NOTE_C7, NOTE_DS8, NOTE_C7, NOTE_DS8, 
  NOTE_C7, NOTE_DS8, NOTE_C7, NOTE_DS8, 
  NOTE_C7, NOTE_DS8, NOTE_C7, NOTE_DS8, 
  NOTE_C7, NOTE_DS8, NOTE_C7, NOTE_DS8, 
  
};

//Busqueda tempo
//const int buscar_tempo[] PROGMEM = {
const int8_t buscar_tempo[] = {
  8, 8, 8, 8,
  8, 8, 8, 8,
  8, 8, 8, 8,
  8, 8, 8, 8,

  8, 8, 8, 8,
  8, 8, 8, 8,
  8, 8, 8, 8,
  8, 8, 8, 8,
};

// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]
// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]
// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]
// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]
// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]
// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]

void RGB_color(int red_light_value, int green_light_value, int blue_light_value) {
  analogWrite(red_light_pin, red_light_value);
  analogWrite(green_light_pin, green_light_value);
  analogWrite(blue_light_pin, blue_light_value);
  /*
  **************Colores*****************
  RGB_color(255, 0, 0); // Red
  RGB_color(0, 255, 0); // Green
  RGB_color(0, 0, 255); // Blue
  RGB_color(255, 255, 125); // Raspberry
  RGB_color(0, 255, 255); // Cyan
  RGB_color(255, 0, 255); // Magenta
  RGB_color(255, 255, 0); // Yellow
  RGB_color(255, 255, 255); // White
  */
}

void buzzled(int8_t buzzErr, int8_t ledErr){
    switch (buzzErr){
        case 1: 
            RGB_color(0, 255, 0); // Green
            sing(1); //Inicializacion
            RGB_color(0, 0, 0); // Green
            break;
            
        case 2: 
            if (ledErr==1)
                RGB_color(255, 0, 0); // BMP180 RED
            else if (ledErr==2)
                RGB_color(0, 0, 255); // IMU BLUE
            else if (ledErr==3)
                RGB_color(255, 255, 0); // SD Yellow
            while(1) 
                sing(2); //Error
            break;
                
        case 3: //Buscar
            while(true){
                RGB_color(255, 255, 255); // White
                sing(3);
            }
            break;
    }
}

void sing(int8_t song) {
  // iterate over the notes of the melody:
    if (song == 2) { //Melodia de Error
        int size = sizeof(error_melody) / sizeof(int);
        for (int thisNote = 0; thisNote < size; thisNote++) {
            // to calculate the note duration, take one second
            // divided by the note type.
            //e.g. quarter note = 1000 / 4, eighth note = 1000/8, etc.
            buzz(melodyPin, error_melody[thisNote], 1000 / error_tempo[thisNote]);
            // to distinguish the notes, set a minimum time between them.
            // the note's duration + 30% seems to work well:
            delay((1000 / error_tempo[thisNote])* 1.30);
            // stop the tone playing:
            buzz(melodyPin, 0, 1000 / error_tempo[thisNote]);
        }
    } 
    else if (song == 3) { //Melodia de busqueda
        int size = sizeof(buscar_melody) / sizeof(int);
        for (int thisNote = 0; thisNote < size; thisNote++) {
            // to calculate the note duration, take one second
            // divided by the note type.
            //e.g. quarter note = 1000 / 4, eighth note = 1000/8, etc.
            int noteDuration = 1000 / buscar_tempo[thisNote];
            buzz(melodyPin, buscar_melody[thisNote], noteDuration);
            // to distinguish the notes, set a minimum time between them.
            // the note's duration + 30% seems to work well:
            delay(noteDuration * 1.30);
            // stop the tone playing:
            buzz(melodyPin, 0, noteDuration);
        }
    }
    else if (song == 1) {  //Melodia de mario
    int size = sizeof(melody) / sizeof(int);
        for (int thisNote = 0; thisNote < size; thisNote++) {
            // to calculate the note duration, take one second
            // divided by the note type.
            //e.g. quarter note = 1000 / 4, eighth note = 1000/8, etc.
            buzz(melodyPin, melody[thisNote], 1000 / tempo[thisNote]);
            // to distinguish the notes, set a minimum time between them.
            // the note's duration + 30% seems to work well:
            delay(1000 / tempo[thisNote] * 1.30);
            // stop the tone playing:
            buzz(melodyPin, 0, 1000 / tempo[thisNote]);
        }
    }
}

void buzz(int8_t targetPin, long frequency, long length) {
    for (long i = 0; i < (frequency * length / 1000); i++) { // for the calculated length of time...
        digitalWrite(targetPin, HIGH); // write the buzzer pin high to push out the diaphram
        delayMicroseconds(1000000 / frequency / 2); // wait for the calculated delay value
        digitalWrite(targetPin, LOW); // write the buzzer pin low to pull back the diaphram
        delayMicroseconds(1000000 / frequency / 2); // wait again or the calculated delay value
    }
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
    return Wire.read(); //[->][DAta][Nack][P] 
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
 * Inicializamos el MPU como se especifica en cada línea
 * Tambien INICIALIZAMOS las aceleraciones
 */
void MPUinit() {
    wireEscritura(MPU9250_ADDRESS,PWR_MGMT_1,0x08);     // Despiera al sensor, la fuente de reloj es el oscilador interno (8Mhz) y se desactiva el sensor de temperatura
    wireEscritura(MPU9250_ADDRESS,USER_CTRL,0x01);      // Desactiva FIFO, desactiva I2C master mode, limpia y resetea sensores y sus registros
    wireEscritura(MPU9250_ADDRESS,0x37,0x00);           // ... INT_PIN_CONFIG
    wireEscritura(MPU9250_ADDRESS,INT_ENABLE,0x00);     // Desactiva todas las interrupciones
    wireEscritura(MPU9250_ADDRESS,CONFIG,0x01);         // Frecuencia de muestreo de Acelerometro y giroscopio de 1[kHz] y delay de 2[ms]
    wireEscritura(MPU9250_ADDRESS,SMPRT_DIV,0x07);      // Sample rate = 1[kHz]/(1+7) = 125 [Hz]
    wireEscritura(MPU9250_ADDRESS,GYRO_CONFIG,GYRO_2000_DPS);    // Rango del giroscopio = 2000 [deg/s] (16.4 [LSB/deg/s])
    wireEscritura(MPU9250_ADDRESS,ACCEL_CONFIG,ACC_16_G);   // Rango del acelerometro = 16 [g] (2048 [LSB/g]) [16(9.8) = m/2]
}

/*
 * AK8963init()
 * Inicializamos el magnetometro AK8963 que esta integrado en el MPU
 * +/- 4800 uT
 */
void AK8963init() {
    wireEscritura(MPU9250_ADDRESS, 0x37, 0x02);
    wireEscritura(AK8963_ADDRESS, AK8963_CNTL, 0x01);
}

/*
 * acelLectura()
 * Leemos los datos del acelerometro y los convertimos a flotantes
 * Debemos normalizar los datso respecto a la escala
 */
void acelLectura() {
    acelRAW[0] = wireLectura(MPU9250_ADDRESS, ACEL_X_H);
    acelRAW[1] = wireLectura(MPU9250_ADDRESS, ACEL_X_L);
    acelRAW[2] = wireLectura(MPU9250_ADDRESS, ACEL_Y_H);
    acelRAW[3] = wireLectura(MPU9250_ADDRESS, ACEL_Y_L);
    acelRAW[4] = wireLectura(MPU9250_ADDRESS, ACEL_Z_H);
    acelRAW[5] = wireLectura(MPU9250_ADDRESS, ACEL_Z_L);
    aX = (float) ((acelRAW[0] << 8) | acelRAW[1])/2048.0;
    aY = (float) ((acelRAW[2] << 8) | acelRAW[3])/2048.0;
    aZ = (float) ((acelRAW[4] << 8) | acelRAW[5])/2048.0;
}

/*
 * gyroLectura()
 * Leemos los datos del giroscopio y los convertimos a flotantes
 * Debemos normalizar los datso respecto a la escala
 */
void gyroLectura(){
    gyroRAW[0] = wireLectura(MPU9250_ADDRESS, GYRO_X_H);
    gyroRAW[1] = wireLectura(MPU9250_ADDRESS, GYRO_X_L);
    gyroRAW[2] = wireLectura(MPU9250_ADDRESS, GYRO_Y_H);
    gyroRAW[3] = wireLectura(MPU9250_ADDRESS, GYRO_Y_L);
    gyroRAW[4] = wireLectura(MPU9250_ADDRESS, GYRO_Z_H);
    gyroRAW[5] = wireLectura(MPU9250_ADDRESS, GYRO_Z_L);
    gX = (float)((gyroRAW[0] << 8) | gyroRAW[1])/16.4;
    gY = (float)((gyroRAW[2] << 8) | gyroRAW[3])/16.4;
    gZ = (float)((gyroRAW[4] << 8) | gyroRAW[5])/16.4;
}

/*
 * magnetLectura()
 * Leemos los datos del magnetometro y los convertimos a flotantes
 * Debemos normalizar los datos respecto a la escala de cada eje, sumando o restando
 */
void magnetLectura(){
    magnetRAW[0] = wireLectura(MPU9250_ADDRESS, MAGNET_X_H);
    magnetRAW[1] = wireLectura(MPU9250_ADDRESS, MAGNET_X_L);
    magnetRAW[2] = wireLectura(MPU9250_ADDRESS, MAGNET_Y_H);
    magnetRAW[3] = wireLectura(MPU9250_ADDRESS, MAGNET_Y_L);
    magnetRAW[4] = wireLectura(MPU9250_ADDRESS, MAGNET_Z_H);
    magnetRAW[5] = wireLectura(MPU9250_ADDRESS, MAGNET_Z_L);
    mX = (float)((magnetRAW[0] << 8) | magnetRAW[1]);
    mY = (float)((magnetRAW[2] << 8) | magnetRAW[3]);
    mZ = (float)((magnetRAW[4] << 8) | magnetRAW[5]);
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
 * calibracionAceleracion
 * Medicion de la altura inicial
 * Hacemos la media de 10 aceleraciones medidas por el MPU para calibrar 
 */
void calibracionAcel() {
    sum = 0;
    for(byte i = 0; i < MUESTRAS; i++)
        aceleraciones[i] = 1;
    for(byte j = 0; j < 10; j++)
        sum += acelMedia();
    acel_max = sum/10.0;
    if(acel_max < 0)
        buzzled(2,2);
    EEPROM.write(DIR_ACEL_INICIAL,map((int)(aT),0,20,0,255));
}

/*
 * alturaMedia
 * Calculamos un promedio de 6 muestras de altura
 */
float alturaMedia() {   
    sum = 0;
    for(byte i = MUESTRAS-1; i > 0; i--)
        alturas[i] = alturas[i-1];
    alturas[0] = bmp.readAltitude();
    for(byte i = 0; i < MUESTRAS; i++)
        sum += alturas[i];
  
    return sum/MUESTRAS; //media movil
}

/*
 * acelMedia
 * Calculamos un promedio de 6 muestras de acel
 */
float acelMedia(){   
    sum = 0;
    for(byte i = MUESTRAS-1; i > 0; i--)
        aceleraciones[i] = aceleraciones[i-1];
    aceleraciones[0] = sqrt((aX*aX) + (aY*aY) + (aZ*aZ)); 
    for(byte i = 0; i < MUESTRAS; i++)
        sum += aceleraciones[i];
    aT = sum/MUESTRAS; //media movil
    EEPROM.write(DIR_ACEL_MAX,map((int)(aT),0,20,0,255));
}

/*
 * respaldoAltura
 * Calcularemos la altura media y revisaremos si es mayor que la altura maxima
 * Si no lo es revisaremos la condición de caída. 
 * Si estamos cayendo escribimos en la EEPROM la altura maxima y finalmente detonamos
 */
void revisaVuelo(){   
    h_media = alturaMedia();
    if(!detonacion) {
        return;
    } else if(h_media > h_max) {
        h_max = h_media;
    } else if((h_max-h_media) > ALTURA_UMBRAL){
        EEPROM.write(DIR_ALTURA_MAX,map((int)(h_max),2000,4000,0,255));
        if(!seguro) {
//            digitalWrite(MOSFET,HIGH); //CARGA EXPLOSIVA!
            detonacion = true;
            estadoVUELO = 2;
            EEPROM.write(DIR_ES_VUELO,estadoVUELO);
            EEPROM.write(DIR_TIEMPO_DETONACION,map((int)(millis()),60000,200000,0,255));
            delay(2000);
//            digitalWrite(MOSFET,LOW); //Apagar carga
        }
    }
}

// [------------------------------------------------------ SET UP y LOOP ------------------------------------------------------]
// [------------------------------------------------------ SET UP y LOOP ------------------------------------------------------]
// [------------------------------------------------------ SET UP y LOOP ------------------------------------------------------]
// [------------------------------------------------------ SET UP y LOOP ------------------------------------------------------]
// [------------------------------------------------------ SET UP y LOOP ------------------------------------------------------]
// [------------------------------------------------------ SET UP y LOOP ------------------------------------------------------]

/*
 * setup()
 * Configuramos todo. Este código se corre al prender el Arduino 
 */
void setup() {
    Serial.begin(9600);
    Serial.print("SETUP");

    // [--- MPU9250, AK8963 y BMP180 ---]
    Wire.begin();
//    calibracionAltura();
    MPUinit();
    // [--- INICIAMOS MELODIA Y ESCRIBIMOS EEPROM ---]
    estadoVUELO = 1;
}

/*
 * loop()
 * El código dentro de esta función se repite indefinidamente
 * Se leen los datos de los sensores y los escribimos a la tarjeta SD
 * El LED se encenderá en caso de error
 */
void loop() {
  Serial.print("LOOP");
    Temperatura = bmp.readTemperature();
    Presion = bmp.readPressure();
    Altitud = bmp.readAltitude();
    acelLectura();
    gyroLectura();
    acelMedia();
        Serial.print(millis());
        Serial.print(",");
        Serial.print(Temperatura);
        Serial.print(",");
        Serial.print(Presion); 
        Serial.print(",");
        Serial.print(Altitud);
        Serial.print(",");
        Serial.print(mX);
        Serial.print(",");
        Serial.print(mY);
        Serial.print(",");
        Serial.print(mZ);
        Serial.print(",");
        Serial.print(aX);
        Serial.print(",");
        Serial.print(aY);
        Serial.print(",");
        Serial.print(aZ);
        Serial.print(",");
        Serial.println(aT);  
delay(3000);
}
