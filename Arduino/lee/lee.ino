#include <EEPROM.h>

void setup() {
  Serial.begin(9600);
  Serial.println(leeEEPROM());
}

void loop() {
  
}

int leeEEPROM() {
  byte byte1 = EEPROM.read(0);
  byte byte2 = EEPROM.read(1);
  return (byte1 << 8) + byte2;
}
