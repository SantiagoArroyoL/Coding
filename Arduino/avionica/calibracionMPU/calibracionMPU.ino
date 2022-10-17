#include <Wire.h>

// [--- CONSTANTES ---]
#define MUESTRAS 6           // 6 alturas en el vector para media móvil

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
#define GYRO_250_DPS     0x00   // (131 [LSB/deg/s])
#define GYRO_500_DPS     0x08   // (65.5 [LSB/deg/s])
#define GYRO_1000_DPS    0x10   // (32.8 [LSB/deg/s])
#define GYRO_2000_DPS    0x18   // (16.4 [LSB/deg/s])
#define ACC_2_G          0x00   // (16384 [LSB/deg/s])
#define ACC_4_G          0x08   // (8192 [LSB/deg/s])
#define ACC_8_G          0x10   // (4096 [LSB/deg/s])
#define ACC_16_G         0x18   // (2048 [LSB/deg/s])

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


// [------------------------- VARIABLES ---------------------------]

// [--- VARIABLES ACELERACION ---]
float aX;             // Aceleracion en X
float aY;             // Aceleracion en Y
float aZ;             // Aceleracion en Z
float aT;             // Aceleración total filtrada con media móvil
float aceleraciones[MUESTRAS];  // Vector de aceleraciones totales

// [--- VARIABLES GYRO ---]
float gX;             // Aceleracion en X
float gY;             // Aceleracion en Y
float gZ;             // Aceleracion en Z

// [--- VARIABLES VARIAS ---]
float sum;             // Variable temporal
byte RAW[6];           // Datos en los registros del MPU


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
      wireEscritura(MPU6050_ADDRESS,ACCEL_CONFIG,ACC_16_G);        // Rango del acelerometro = 16 [g] (2048 [LSB/deg/s])
}


/*
 * acelLectura()
 * Leemos los datos del acelerometro y los convertimos a flotantes
 * Debemos normalizar los datso respecto a la escala
 */
void acelLectura(){
      RAW[0] = wireLectura(MPU6050_ADDRESS, ACEL_X_H);
      RAW[1] = wireLectura(MPU6050_ADDRESS, ACEL_X_L);
      RAW[2] = wireLectura(MPU6050_ADDRESS, ACEL_Y_H);
      RAW[3] = wireLectura(MPU6050_ADDRESS, ACEL_Y_L);
      RAW[4] = wireLectura(MPU6050_ADDRESS, ACEL_Z_H);
      RAW[5] = wireLectura(MPU6050_ADDRESS, ACEL_Z_L);
      aX = (float)((RAW[0] << 8) | RAW[1])/2048.0;
      aY = (float)((RAW[2] << 8) | RAW[3])/2048.0;
      aZ = (float)((RAW[4] << 8) | RAW[5])/2048.0;
}

/*
 * gyroLectura()
 * Leemos los datos del giroscopio y los convertimos a flotantes
 * Debemos normalizar los datso respecto a la escala
 */
void gyroLectura() {
      RAW[0] = wireLectura(MPU6050_ADDRESS, GYRO_X_H);
      RAW[1] = wireLectura(MPU6050_ADDRESS, GYRO_X_L);
      RAW[2] = wireLectura(MPU6050_ADDRESS, GYRO_Y_H);
      RAW[3] = wireLectura(MPU6050_ADDRESS, GYRO_Y_L);
      RAW[4] = wireLectura(MPU6050_ADDRESS, GYRO_Z_H);
      RAW[5] = wireLectura(MPU6050_ADDRESS, GYRO_Z_L);
      gX = (float)((RAW[0] << 8) | RAW[1])/16.4;
      gY = (float)((RAW[2] << 8) | RAW[3])/16.4;
      gZ = (float)((RAW[4] << 8) | RAW[5])/16.4;
}

/*
 * acelMedia
 * Calculamos un promedio de 6 muestras de acel
 */
void acelMedia(){   
    sum = 0;
    for(byte i = MUESTRAS-1; i > 0; i--)
        aceleraciones[i] = aceleraciones[i-1];
    aT = sqrt((aX*aX) + (aY*aY) + (aZ*aZ)); 
    for(byte i = 0; i < MUESTRAS; i++)
        sum += aceleraciones[i];
    aT = sum/MUESTRAS; //media movil
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
    // [---  Comunicacion I2C ---]
    Wire.begin();
    // [--- MPU9250 ---]
    MPUinit();
}//Cierre SETUP

void revisa(){
    acelLectura();
    gyroLectura();
    aT = sqrt((aX*aX)+(aY*aY)+(aZ*aZ));
    Serial.print(millis());
    Serial.print(",");
    Serial.print(gX);
    Serial.print(",");
    Serial.print(gY);
    Serial.print(",");
    Serial.print(gZ);
    Serial.print(",");
    Serial.print(aX);
    Serial.print(",");
    Serial.print(aY);
    Serial.print(",");
    Serial.print(aZ);
    Serial.print(",");
    Serial.println(aT);  
}

void calibra() {
  
}


// [--- CICLO ---]
/*
 * loop()
 * El código dentro de esta función se repite indefinidamente
 * Se leen los datos de los sensores y los escribimos a la tarjeta SD
 * El LED se encenderá en caso de error
 */
void loop() { 
    revisa();
//    calibra();
    delay(1000);
}
