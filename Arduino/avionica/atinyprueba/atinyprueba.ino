void setup() {
  pinMode(PIN_PA7,OUTPUT);    // Pin conectado a la carga
  pinMode(PIN_PA6,OUTPUT);    // Pin conectado al buzzer
  digitalWrite(PIN_PA7,LOW);
}

void loop() {
  tone(PIN_PA6,880);
  delay(500);
  noTone(PIN_PA6);
  delay(500);
}
