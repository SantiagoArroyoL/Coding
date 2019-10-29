/* Sensores de movimiento*/

const int buzz = 9; // Zumbador | Pin: 9 
const int sensor1 = 8; // Sensor de movimiento 1 PIR | Pin 8 
const int sensor2 = 7; // Sensor de movimiento 1 PIR | Pin 8 
const int led = 13; // Led | Pin 13 

int mov1 = 0; // Variable que guarda el cambio del sensor
int mov2 = 0; // Variable que guarda el cambio del sensor

void setup() {
  Serial.begin(9600);
  pinMode(buzz,OUTPUT);
  pinMode(led,OUTPUT);
  pinMode(sensor1,INPUT);
  pinMode(sensor2,INPUT);
  Serial.println("Sensor de Movimiento");
  Serial.println(" ");
}

void loop() {
  mov1 = digitalRead(sensor1);
  mov2 = digitalRead(sensor2);
  delay(50);
  if (mov1 == HIGH) {
    Serial.print(mov1); Serial.print(" : "); Serial.println("Movimiento detectado por el sensor 1"); 
    digitalWrite(led,HIGH);
    tonos1();
    digitalWrite(led,LOW);
    mov1 = 0;
    delay(100);
  }
  else if (mov2 == HIGH) {
    Serial.print(mov2); Serial.print(" : "); Serial.println("Movimiento detectado por el sensor 2"); 
    digitalWrite(led,HIGH);
    tonos2();
    digitalWrite(led,LOW);
    mov2 = 0;
    delay(100);
  }else {
    Serial.print(mov1); Serial.print(" : "); Serial.println("No se detecta movimiento por el sensor 1");
    Serial.print(mov2); Serial.print(" : "); Serial.println("No se detecta movimiento por el sensor 2");
    delay(100);
    }
}

void tonos1(){
  tone(buzz,8.18); // C | octava - 2;
  delay(150);
  tone(buzz,9.72); // D# | octava - 2;
  delay(150);
  tone(buzz,14.57); // A# | octava - 2;
  delay(150);
  noTone(buzz);
  delay(100);
  
  tone(buzz,13.75); // A | octava - 2;
  delay(150);
  tone(buzz,9.72); // D# | octava - 2;
  delay(150);
  tone(buzz,8.18); // C | octava - 2;
  delay(150);
  noTone(buzz);
  delay(100);     
}



void tonos2(){
  tone(buzz,13.75); // A | octava - 2;
  delay(150);
  tone(buzz,9.72); // D# | octava - 2;
  delay(150);
  tone(buzz,8.18); // C | octava - 2;
  delay(150);
  noTone(buzz);
  delay(100); 
  
  tone(buzz,9.72); // D# | octava - 2;
  delay(150);
  tone(buzz,9.72); // D# | octava - 2;
  delay(150);
  tone(buzz,9.72); // D# | octava - 2;
  delay(150);
  noTone(buzz);
  delay(100);
     
}
