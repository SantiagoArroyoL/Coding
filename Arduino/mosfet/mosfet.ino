#define MOSFET 8
void setup() {
    pinMode(MOSFET,OUTPUT);
    digitalWrite(MOSFET,LOW);
}

void loop() {
  digitalWrite(MOSFET, HIGH);
  delay(1500);
  digitalWrite(MOSFET, LOW);
  delay(1500);
  
}
