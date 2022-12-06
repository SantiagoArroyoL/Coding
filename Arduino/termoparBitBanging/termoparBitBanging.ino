#define MAX6675_SO 23
#define MAX6675_CS 22
#define MAX6675_SCK 18
float temperatura;
uint16_t v;

void setup() {
  pinMode(MAX6675_CS, OUTPUT);
  pinMode(MAX6675_SO, INPUT);
  pinMode(MAX6675_SCK, OUTPUT);
  Serial.begin(115200);
}

void loop() {
  termopar();
  Serial.print(millis()/1000.0,3);
  Serial.print(", ");
  Serial.print("Temperatura: ");
  Serial.println(temperatura);
  delay(500);
}

void termopar() { 
    digitalWrite(MAX6675_CS, LOW);
    delay(5); //No sabemos cuanto dura un digitalWrite, 
    // asi que un delay no hace daño
    
    // Lee 16 bits,
    //  15    = 0 siempre
    //  14..2 = 0.25 grado cuenta MSB Primero
    //  2     = 1 si el termopar es de circuito abierto (?)
    //  1..0  = status
    // shiftIn(dataPin, clockPin, bitOrder)
    v = shiftIn(MAX6675_SO, MAX6675_SCK, MSBFIRST); // shiftIn: Desplaza un byte de datos un bit cada vez. Segundo parametro es donde comienza
    v <<= 8;
    v |= shiftIn(MAX6675_SO, MAX6675_SCK, MSBFIRST);
    digitalWrite(MAX6675_CS, HIGH);
    if (v & 0x4) {
        // Bit 4 indica si el termopar esta desconectado
        temperatura = NAN;
    }
    
    // los 3 bits menos signifcaivos (0,1,2) son status
    v >>= 3;
    // Los bits restantes son lecturas en 0.25[Celsius]
    temperatura = v * 0.25;
}
