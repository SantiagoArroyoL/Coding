#include <EEPROM.h>

// [--- DIRECCIONES EPPROM  ---]
#define DIR_ES_VUELO       0     // Estado de vuelo:      0 (Espera), 1 (Vuelo), 2 (Descenso terminado)
#define DIR_ALTURA_MAX     1     // Altura máxima:        0 -> 2000 [m] & 255 -> 4000 [m]
#define DIR_ALTURA_INICIAL 2     // Altura inicial:       0 -> 2000 [m] & 255 -> 4000 [m]
#define DIR_ACEL_INICIAL   3     // Aceleracion inicial:  0 -> 0 [g] & 255 -> 20 [g]
#define DIR_ACEL_MAX       4     // Aceleración máxima:   0 -> 0 [g] & 255 -> 20 [g]
#define DIR_TIEMPO_DET     5     // Tiempo Final:         0 -> 60 [s] & 255 -> 100 [s]
#define DIR_TIEMPO_s    6     // Tiempo Inicial:       0 -> 60 [s] & 255 -> 100 [s]
#define DIR_TIEMPO_d    7     // Tiempo Inicial:       0 -> 60 [s] & 255 -> 100 [s]
#define DIR_TIEMPO_sa   8     // Tiempo Inicial:       0 -> 60 [s] & 255 -> 100 [s]
#define DIR_TIEMPO_q   9     // Tiempo Inicial:       0 -> 60 [s] & 255 -> 100 [s]



void setup() {
  Serial.begin(9600);
  EEPROM.write(DIR_ES_VUELO,0); 
  EEPROM.write(DIR_ALTURA_MAX,0); 
  EEPROM.write(DIR_ALTURA_INICIAL,0);
  EEPROM.write(DIR_ACEL_INICIAL,0);
  EEPROM.write(DIR_ACEL_MAX,0);
  EEPROM.write(DIR_TIEMPO_DET,0);
  EEPROM.write(DIR_TIEMPO_CERO,0);
    EEPROM.write(DIR_TIEMPO_s,0);
  EEPROM.write(DIR_TIEMPO_da,0);
  EEPROM.write(DIR_TIEMPO_q
  ,0);

  Serial.println(EEPROM.read(DIR_ES_VUELO));
  Serial.println(EEPROM.read(DIR_ALTURA_MAX));
  Serial.println(EEPROM.read(DIR_ALTURA_INICIAL)); 
  Serial.println(EEPROM.read(DIR_ACEL_INICIAL )); 
  Serial.println(EEPROM.read(DIR_ACEL_MAX)); 
  Serial.println(EEPROM.read(DIR_TIEMPO_DET)); 
  Serial.println(EEPROM.read(DIR_TIEMPO_CERO)); 
}

void loop(  ) {
  // put your main code here, to run repeatedly:
}
