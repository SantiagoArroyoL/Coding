#include <SoftwareSerial.h>

SoftwareSerial BT1(10, 11); // RX | TX
void setup()
   {              // Espera antes de encender el modulo
     Serial.begin(9600);
     Serial.println("Esperando datos");
     BT1.begin(9600); 
     pinMode(3,OUTPUT);
     pinMode(4,OUTPUT);
     pinMode(5,OUTPUT);
     pinMode(6,OUTPUT);
     pinMode(7,OUTPUT);
     pinMode(8,OUTPUT);
     
   }

void loop()
   { 
    char e;
    if (BT1.available())
            Serial.write(BT1.read());
            e=(BT1.read());
      if (Serial.available())
            BT1.write(Serial.read());
      if (e=="A"){
            digitalWrite(3,HIGH);
            digitalWrite(4,HIGH);
            digitalWrite(5,LOW);
            digitalWrite(6,HIGH);
            digitalWrite(7,HIGH);
            digitalWrite(8,LOW);  
      }
      if (e=="a"){
          digitalWrite(13,LOW);
      }
   }
