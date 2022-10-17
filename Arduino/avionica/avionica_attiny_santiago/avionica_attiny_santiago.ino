#include <Wire.h>
#include <megaTinyCore.h>
#include <Adafruit_BMP085.h>

// [--- CONSTANTES ---]
#define MUESTRAS 6           // 6 alturas en el vector para media móvil
#define ALTURA_UMBRAL 30     // 30 [m] de caída para activación 

#define TOPE_TIMER 500     // 1 -> 8.19[ms] | 368 -> 3.014 [s] | 500 -> 4.095 [s]

#define NOTE_C   1046.5
#define NOTE_F   1397
#define NOTE_B7  3951
#define NOTE_BB  1864.7
#define NOTE_E8  5274
#define NOTE_EB  1244.5
#define SILENCE  0
#define NOTE_CS8 4435

#define U_0  0.01382
#define U_1  0.04146
#define U_2  0.04146
#define U_3  0.01382
#define H_1 -1.881593
#define H_2  1.309579
#define H_3 -0.3174255


// [------------------------- VARIABLES y MAS ---------------------------]
volatile byte conexion; 
volatile byte seguro;
byte estadoCRITICO = 0;
// Variable de carga explosiva
byte detonacion = 0;    
// Variable de control de la interrupción timer
volatile unsigned int contador_programa; 
byte estadoVUELO = 0;
byte SBD;

// Datos de altura
Adafruit_BMP085 bmp;
  //Determinación de altura
      float h_0;              // Altura inicial
      float h_max;            // Altura máxima
      float presion;
      float h[3];             // Vector de alturas de salida
      float u[3];             // Vector de alturas de lectura
      float h_media;          // Altura filtrada con ButterWorth
      float temp;             // Temperatura
      
static const int notas[] = {
  NOTE_CS8, SILENCE,  NOTE_CS8, SILENCE,
  NOTE_B7,  NOTE_CS8, SILENCE,  NOTE_E8,
  SILENCE,  NOTE_CS8, SILENCE,  SILENCE
};
