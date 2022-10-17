/*
 * 
 * Estacion Terrena Propulsion UNAM
 * 
 * Santiago Arroyo
 */

#include <LoRa.h>
#include "utilities.h" // DEBE INCLUIRSE EN EL MISMO DIRECTORIO

SFE_UBLOX_GPS myGPS;

char nmeaBuffer[100];
MicroNMEA nmea(nmeaBuffer, sizeof(nmeaBuffer));

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
    LoRa.setSyncWord(0xF3);

    Serial.println("Iniciamos GPS");
    
    if (myGPS.begin(Serial1) == false) {
        Serial.println(F("Ublox GPS no detectado en la direccion I2C . checa tu conexion mano!."));
        while (1);
    }
}

void loop() {
    int packetSize = LoRa.parsePacket();
    if (packetSize) {
        Serial.print("Recibido! '");

        String rec = "";
        // leer
        while (LoRa.available()) {
            rec += (char)LoRa.read();
        }

        Serial.println(rec);

        // print RSSI of packet
        Serial.print("' RSSI ");
        Serial.println(LoRa.packetRssi());
    }
    
    myGPS.checkUblox(); //Debemos actualizar manual lo datos, si hay

    if (nmea.isValid() == true) {
        long latitude_mdeg = nmea.getLatitude();
        long longitude_mdeg = nmea.getLongitude();

        Serial.print("Latitud (deg): ");
        Serial.println(latitude_mdeg / 1000000., 6);
        Serial.print("Longitud (deg): ");
        Serial.println(longitude_mdeg / 1000000., 6);
    } else {
//        Serial.print("No Fix - ");
//        Serial.print("Num. satelites: ");
//        Serial.println(nmea.getNumSatellites());
    }
    delay(250);
}

//Usamos eloperadore de alcance unario para llamar la funcion de SparkFun Ublox Arduino Library
//Podemos especificar que hacer con cada caracter NMEA
//PAra uso con MicroNMEA. Internet dice que funciona con TinyGPS pero no se logro
void SFE_UBLOX_GPS::processNMEA(char incoming) {
    //Agarramos el caracter que nos llegue por I2C y se lo mandamos a MicroNMEA pa que el decida que pex
    nmea.process(incoming);
}
