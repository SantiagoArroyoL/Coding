// I2C Scanner
#include <Wire.h>

void setup() {
    Serial.begin (9600);
    Serial.println ();
    Serial.println ("I2C scanner. Scanning ...");
    byte count = 0;
    
    Wire.begin();
    for (byte i = 8; i < 120; i++) { 
        Wire.beginTransmission (i);
        if (Wire.endTransmission () == 0) {
            Serial.print ("ENCONTRADO: ");
            Serial.print (i, DEC);
            Serial.print (" (0x");
            Serial.print (i, HEX);
            Serial.println (")");
              count++;
              delay (1);
        } else {
            Serial.print("Dirección vacía: ");
            Serial.print (i, DEC);
            Serial.print (" (0x");
            Serial.print (i, HEX);
            Serial.println (")");
        }
    } // end of for loop
    Serial.println ("Done.");
    Serial.print ("Se encontraron ");
    Serial.print (count, DEC);
    Serial.println (" dispositivos.");
}

void loop() {}
