#include <EEPROM.h>
int adcMax = 0;
void setup() {
  Serial.begin(9600);
}

void loop() {
  if(adc > adcMax){
    adcMax = adc;
    escribeEEPROM(adcMax);   
  }
}

void escribeEEPROM(int numero) { 
  byte byte1 = numero >> 8;
  byte byte2 = numero & 0xFF;
  EEPROM.write(0, byte1);
  EEPROM.write(1, byte2);
}

int leeEEPROM() {
  byte byte1 = EEPROM.read(0);
  byte byte2 = EEPROM.read(1);
  return (byte1 << 8) + byte2;
}
