#include <Wire.h>

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
#define MAGNET_X_L       0x03 // No están al revés. Primero va el registro LOW
#define MAGNET_X_H       0x04
#define MAGNET_Y_L       0x05
#define MAGNET_Y_H       0x06
#define MAGNET_Z_L       0x07
#define MAGNET_Z_H       0x08

// [--- VARIABLES ACELERACION ---]
byte acelRAW[6];        // Datos en los registros del acelerometro
float aX;               // Aceleracion en X
float aY;               // Aceleracion en Y
float aZ;               // Aceleracion en Z
float aT;               // Aceleración total filtrada con media móvil

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
 * Inicializamos el MPU como se especifica en cada lÃ­nea
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
 * NO LO NORMALIZO CON LA ESCALA!!!!! NO SÉ SI SEA CORRECTO
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

void setup() {
    Serial.begin(9600);
    Wire.begin();
    MPUinit();
    AK8963init();
}

void loop() {
    acelLectura();
    gyroLectura();
    magnetLectura();
}
