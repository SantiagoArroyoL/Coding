// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]
// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]
// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]
// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]
// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]
// [------------------------------------------------------ FUNCIONES ------------------------------------------------------]

void tonoOK() {
    digitalWrite(PIN_PA3,HIGH);//LED Verde
    digitalWrite(PIN_PA2,LOW);//LED Rojo
    digitalWrite(PIN_PA1,LOW);//LED Azul
    tone(PIN_PA6,NOTE_F);
    delay(500);
    digitalWrite(PIN_PA3,LOW);//LED Verde
    digitalWrite(PIN_PA2,HIGH);//LED Rojo
    tone(PIN_PA6,NOTE_C);
    delay(500);
    noTone(PIN_PA6);
}

void powerRangers(){
    for (int i=0; i<12; i+=1) {
        if (notas[i] != SILENCE) {
          tone(PIN_PA6, notas[i], 102);
        }
    delay(150);
    }
}

float alturaFiltrada() {   
      float hf;
      float u0;
      u0 = bmp.readAltitude();
      hf = U_0*u0+U_1*u[0]+U_2*u[1]+U_3*u[2];
      hf = hf -H_1*h[0]-H_2*h[1]-H_3*h[2];
      u[2] = u[1]; u[1] = u[0]; u[0] = u0;
      h[2] = h[1]; h[1] = h[0]; h[0] = hf;
      return hf;
}

void calibracionAltura() {
    float sum = 0;
    for(byte j = 0; j<10; j++)
      sum += bmp.readAltitude();
    h_0 = sum/10.0;
    h_max = h_0;
}

void tonoUART() {
    for(byte i=0; i < 2; i++) {
        tone(PIN_PA6,NOTE_EB/2);
        delay(166);
        tone(PIN_PA6,NOTE_BB);
        delay(166);
        tone(PIN_PA6,NOTE_EB);
        delay(166);
        noTone(PIN_PA6);
        if(i==0)
        delay(500);
    }
}

void tonoERROR(int t) {
    tone(PIN_PA6,NOTE_F);
    delay(300);
    tone(PIN_PA6,NOTE_BB/2);
    delay(300);
    tone(PIN_PA6,988);
    delay(300);
    for(byte i=0; i<t; i++) {
        tone(PIN_PA6,NOTE_BB/2);
        delay(150);
        tone(PIN_PA6,988);
        delay(150);
        tone(PIN_PA6,NOTE_C);
        delay(150);
    }
    noTone(PIN_PA6);
}

void updateNano() {
    SBD = seguro | (conexion<<1) | (detonacion<<2);
    Serial.print(millis());
    Serial.print(",");
    Serial.print(h_media);
    Serial.print(",");
    Serial.print(temp);
    Serial.print(",");
    Serial.println(SBD);
}

/*
 * revisaVuelo
 * Calcularemos la altura media y revisaremos si es mayor que la altura maxima
 * Si no lo es revisaremos la condición de caída. 
 * Si estamos cayendo escribimos en la EEPROM la altura maxima y finalmente detonamos
 * Se hacen 3 revisiones particulares
 */
void revisaVuelo(){
    if(h_media > h_max) { // 2. revisa despegue => cambia estado
        estadoVUELO = 1;
        h_max = h_media;    
    } else if((h_max-h_media) > ALTURA_UMBRAL){ // 3. revisa caida y paracaidas => despliega
        if(seguro > 0) {
            digitalWrite(PIN_PA7,HIGH);     //Salida MOSFET!!!!!
            float t_MOSFET = millis();
            detonacion = 1;
            estadoVUELO = 2;           
            // Revision de la carga
            if((millis()-t_MOSFET) > 1500L ) {
                digitalWrite(PIN_PA7,LOW);     //Salida MOSFET
                // Combinación para indicar que la carga se detonó
                digitalWrite(PIN_PA3,LOW);    //LED Verde
                digitalWrite(PIN_PA2,LOW);    //LED Rojo
                digitalWrite(PIN_PA1,HIGH);   //LED Azul
            }
          }
      }
  }

void SerialEvent() {
  //detonacion = Serial.read();
}
