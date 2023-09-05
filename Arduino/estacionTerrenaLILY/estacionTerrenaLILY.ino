/*
 * 
 * Estacion Terrena Propulsion UNAM
 * 
 * Santiago Arroyo
 */

#include <LoRa.h>
#include "utilities.h" // DEBE INCLUIRSE EN EL MISMO DIRECTORIO
#include <Q2HX711.h>

// Galgas
#define HX711_DOUT 21
#define HX711_SCK  22

#define A 7.72797e-05
#define B -646.825

Q2HX711 celda(HX711_DOUT,HX711_SCK); // Galga 1
unsigned long galgaADC;
float galgaKgf;

// SFE_UBLOX_GPS myGPS;

// char nmeaBuffer[100];
// MicroNMEA nmea(nmeaBuffer, sizeof(nmeaBuffer));

void setup() {
    initBoard();
    // Se NECESITA el delay si no se quema dice Sparkfun
    delay(1500);

    Serial.println("Iniciamos LoRa");

    LoRa.setPins(RADIO_CS_PIN, RADIO_RST_PIN, RADIO_DI0_PIN);
    while (!LoRa.begin(915E6)) {
      Serial.println(".");
      delay(500);
    }
    // SF -> 7
    // CR -> $
    LoRa.setSpreadingFactor(10);
    LoRa.setSignalBandwidth(31.25E3);
    LoRa.setSyncWord(0xF3);
    
    // if (myGPS.begin(Serial1) == false) {
    //     Serial.println(F("Ublox GPS no detectado en la direccion I2C . checa tu conexion mano!."));
    //     // while (1);
    // }
}

void loop() {
  readPressure();
  galgaADC = celda.read();
  galgaKgf = A * galgaADC + B;

  LoRa.beginPacket();
  LoRa.print(millis());
  LoRa.print(",");
  LoRa.print(galgaADC);
  LoRa.print(",");
  LoRa.print(galgaKgf);
  LoRa.print(",");
  LoRa.println(presion1);
  LoRa.endPacket();

  Serial.print(millis());
  Serial.print(",");
  Serial.print(galgaADC);
  Serial.print(",");
  Serial.print(galgaKgf);
  Serial.print(",");
  Serial.println(presion1);

}

//Usamos eloperadore de alcance unario para llamar la funcion de SparkFun Ublox Arduino Library
//Podemos   especificar que hacer con cada caracter NMEA
//PAra uso con MicroNMEA. Internet dice que funciona con TinyGPS pero no se logro
// void SFE_UBLOX_GPS::processNMEA(char incoming) {
//     //Agarramos el caracter que nos llegue por I2C y se lo mandamos a MicroNMEA pa que el decida que pex
//     nmea.process(incoming);
// }
