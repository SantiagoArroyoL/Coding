/*********
  prueba teques
*********/

#include <SPI.h>
#include <LoRa.h>

// Conexiones módulo SD
#define CS_0      5

// Conexiones módulo LoRa
#define CS_1      13
#define RST       14
#define DIO0      27

#define LED       32   

void setup() {
  Serial.begin(115200);

  //setup LoRa transceiver module
  LoRa.setPins(CS_1, RST, DIO0);
  
  //replace the LoRa.begin(---E-) argument with your location's frequency 
  //433E6 for Asia
  //866E6 for Europe
  //915E6 for North America
  while (!LoRa.begin(915E6)) {
    Serial.println("No Lora.");
  }
   // Change sync word (0xF3) to match the receiver
  // The sync word assures you don't get LoRa messages from other LoRa transceivers
  // ranges from 0-0xFF
  //LoRa.setSpreadingFactor(8);   //DEFAULT es 7
  LoRa.setSyncWord(0xF3);
  Serial.println("LoRa Initializing OK!");
}

void loop() {
  // try to parse packet
  int packetSize = LoRa.parsePacket();
  if (packetSize) {
    // received a packet
    Serial.print("Received packet '");

    // read packet
    while (LoRa.available()) {
      String LoRaData = LoRa.readString();
      Serial.print(LoRaData); 
    }

    //Serial.println("RSSI: " + String(LoRa.packetRssi()));
    //Serial.println("SNR: " + String(LoRa.packetSnr()));
  }
}
