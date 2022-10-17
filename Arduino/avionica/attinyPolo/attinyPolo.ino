#include <megaTinyCore.h>
#include <Wire.h>
#include <Adafruit_BMP085.h>

#define MUESTRAS 5         // 5 alturas en el vector para media móvil
#define ALTURA_UMBRAL 20   // 20 [m] de caída para activación
#define ASCENSO_MINIMO 80  // 80 [m] de ascenso mínimo sobre la altura inicial
#define TOPE_TIMER 500     // 1 -> 8.19[ms] | 368 -> 3.014 [s] | 500 -> 4.095 [s]

#define s 0
#define C 1046.5
#define D 1174.7
#define Eb 1244.5
#define E 1318.5
#define F 1397
#define G 1568
#define A 1760
#define Bb 1864.7
#define MULT 38


// --- VARIABLES ---
  // Estado crítico
      byte estadoCRITICO = 0;
  
  // Sensor de presión
      Adafruit_BMP085 bmp;

  // Variable de control de la interrupción seguro
      volatile byte conexion; 
      volatile byte seguro;
      
  // Variable de carga explosiva
      byte detonacion = 0;

  // Variable de control de la interrupción timer
      volatile unsigned int contador_programa; 

  // Datos de altura
      float h_0;                // Altura inicial
      float h_max;              // Altura máxima
      float alturas[MUESTRAS];  // Vector de alturas
      float h_media;            // Altura filtrada con media móvil

  //Notas
      float china_notes[37] ={Bb/2,C,D,Eb,F,G,A,Bb,A,G,F,G,F,G,F,E,F,G,s,F,Eb,F/2,Bb/2,Bb,C,C*2,A/2,A,F/2,F, C,C*2,D,D*2,Bb/2,Bb,F/2};
      byte china_dur[37] = {2,2,2,2,2,2,2,8,4,4,8,2,2,2,2,1,1,2,4,12,2,2,4,4,4,4,4,4,4,4,4,4,4,4,4,4,8};


// --- FUNCIONES ---

void tonoOK()
{
    tone(PIN_PA6,F);
    delay(500);
    tone(PIN_PA6,C);
    delay(500);
    noTone(PIN_PA6);
}

void tonoUART()
{
    for(byte i=0; i<2; i++)
    {
      tone(PIN_PA6,Eb/2);
      delay(166);
      tone(PIN_PA6,Bb);
      delay(166);
      tone(PIN_PA6,Eb);
      delay(166);
      noTone(PIN_PA6);
      if(i==0)
        delay(500);
    }
}

void tonoERROR(int t)
{
    tone(PIN_PA6,E);
    delay(300);
    tone(PIN_PA6,Bb/2);
    delay(300);
    tone(PIN_PA6,988);
    delay(300);
    for(byte i=0; i<t; i++)
    {
      tone(PIN_PA6,Bb/2);
      delay(150);
      tone(PIN_PA6,988);
      delay(150);
      tone(PIN_PA6,C);
      delay(150);
    }
    noTone(PIN_PA6);
}

float alturaMedia()
{   float sum = 0;
    for(byte i = MUESTRAS-1; i>0; i--)
      alturas[i] = alturas[i-1];

    alturas[0] = bmp.readAltitude();

    for(byte i = 0; i<MUESTRAS; i++)
      sum += alturas[i];

    return sum/MUESTRAS;
}

void calibracionAltura()
{
    float sum = 0;
    for(byte j = 0; j<40; j++)
      sum += bmp.readAltitude();
    h_0 = sum/40.0;
    h_max = (h_max+h_0)/2.0;
}

void updateNano()
{
    Serial.print(h_media);
    Serial.print(",");
    Serial.print(h_0);
    Serial.print(",");  
    Serial.print(h_max);
    Serial.print(",");
    Serial.print(conexion);
    Serial.print(",");
    Serial.print(seguro);
    Serial.print(",");
    Serial.println(detonacion);
}

void delay_update(int T)
{
  int top = T/60;
  for(int i=0; i<top; i++)
  {
    h_media = alturaMedia();
    updateNano();
    delay(40);
  }
}


// --- SETUP ---
void setup()
{
    // Salidas
      pinMode(PIN_PA7,OUTPUT);        //Carga de liberación
      digitalWrite(PIN_PA7,LOW);
      
      pinMode(PIN_PA3,OUTPUT);        //LED Rojo
      pinMode(PIN_PA2,OUTPUT);        //LED Verde
      pinMode(PIN_PA1,OUTPUT);        //LED Azul

      pinMode(PIN_PA6,OUTPUT);        //Buzzer
      digitalWrite(PIN_PA6,LOW);


    // Iniciar comunicacion UART
      Serial.begin(115200);
      delay(5);

    /* ---- ATmega328P informa si es estado crítico ---- */
      
      if(Serial.available() > 0)
      {
        byte ack = Serial.read();
        if(ack == 1)
          estadoCRITICO = 1;          //Posblemente estamos en vuelo
      }
       

    // Comunicación I2C
      Wire.begin();

      
    // Inicializar sensor BMP180
      while( !bmp.begin() )
      {
        digitalWrite(PIN_PA3,HIGH);
        digitalWrite(PIN_PA2,LOW);
        digitalWrite(PIN_PA1,HIGH);
        delay(250);
        digitalWrite(PIN_PA3,LOW);
        digitalWrite(PIN_PA2,LOW);
        digitalWrite(PIN_PA1,LOW);
        delay(246);
      }
      
    // Inicialización del vector de alturas y calibración de la altura inicial
      for(byte i = 0; i<MUESTRAS; i++)
        alturas[i] = bmp.readAltitude();
      h_max = alturaMedia();

      
    if(!estadoCRITICO)
    { 
      calibracionAltura();
      for(int i=0; i<37; i++)   //Tocar la melodía
      {
          if(china_notes[i]==0)
          {
            noTone(PIN_PA6);
            delay(china_dur[i]*MULT);
          }
          else
          {
            tone(PIN_PA6,china_notes[i]);
            delay(china_dur[i]*MULT);   
          }
      }noTone(PIN_PA6);         //Detener la melodía
      delay(100);
    
    // Verifica el byte de estado del ATmega328P
      if(Serial.available()>0)
      {
        byte ack = Serial.read();
        byte ack_mod = ack & 0x03;
        
        if(ack == 0)
          tonoOK();
        else if(ack_mod == 1)
        {
          estadoCRITICO = 1;          //Posblemente estamos en vuelo
        }
        else if(ack > 3)
        {
          tonoERROR(((ack & (1<<2))>>2) + ((ack & (1<<3))>>3) + ((ack & (1<<4))>>4)); // Hace el tono la cantidad de veces como errores
        }
      }
      else
      {
        tonoUART();
      }
    // Se verificó el byte de estado del ATmega328P.
    
    }
    else
    {
      h_0 = h_max - 300.0;
      // Espera de configuración completa del ATmega328P
         delay(700);
    }

      
    // Interrupción del seguro
      //  Pin PA5 con interrupción al cambio y sin resistencia pullUp:
        PORTA.PIN5CTRL = 0b00000001; // PULLUPEN = 0; ISC = 001 en el cambio

    // Interrupción del timer
        TCB1.CTRLA = 0x0;   // Desactiva el periférico completamente
        TCB1.CTRLB = 0x0;   // <Periodic Interrupt mode>
        TCB1.INTCTRL = 0x1; // Activa la interrupción del timer
        TCB1.CCMP = 0xFFFF; // Valor TOP para reiniciar la cuenta y disparar la interrupción
        // TCB1.CTRLA = 0x03;   // Inicia el timer a la frecuencia de reloj/2 <8 [MHz]>
        
    // Revisar estado del seguro pre-lanzamiento
      if (VPORTA.IN&(1<<5))
      {
          // Combinación para indicar que está bloqueda la carga
          digitalWrite(PIN_PA3,HIGH);//LED Rojo
          digitalWrite(PIN_PA2,LOW);//LED Verde
          digitalWrite(PIN_PA1,LOW);//LED Azul
          conexion = 1;
          seguro = 1;
          TCB1.CNT = 0x0;         // Valor del contador. Lo iniciamos en 0
          contador_programa = 0;  // Contador a 0
      }
      else
      {
          // Combinación para indicar que está en transición
          digitalWrite(PIN_PA3,LOW);//LED Rojo
          digitalWrite(PIN_PA2,HIGH);//LED Verde
          digitalWrite(PIN_PA1,HIGH);//LED Azul
          conexion = 0;
          seguro = 1;
          TCB1.CNT = 0x0;         // Valor del contador. Lo iniciamos en 0
          contador_programa = 0;  // Contador a 0
          TCB1.CTRLA = 0x03;      // Inicia el timer a la frecuencia de reloj/2 <8 [MHz]>
      }
}




// --- LOOP ---
void loop() {
    // Registrar altura
      h_media = alturaMedia();
      updateNano();
      delay(30);    /* CAMBIE EL DELAY PARA CORREGIR ERRORES DE ATRASO EN ATMEGA328P*/

    if( h_media > h_max)
    {
      h_max = h_media;
    }
    else if( (h_max-h_media)>ALTURA_UMBRAL )
    {
      if(!conexion)
      {
          if( (!seguro && ((h_max - h_0) > ASCENSO_MINIMO) && !estadoCRITICO) || estadoCRITICO )
          {
          // Activación de la carga explosiva
            digitalWrite(PIN_PA7,HIGH);
            detonacion = 1;
          // Combinación para indicar que la carga se detonó
            digitalWrite(PIN_PA3,LOW);//LED Rojo
            digitalWrite(PIN_PA2,LOW);//LED Verde
            digitalWrite(PIN_PA1,HIGH);//LED Azul
          // Dejar 2 [s] la carga
          for(int i=0; i<56; i++)
          {
            h_media = alturaMedia();
            updateNano();
            delay(30);    /* CAMBIE EL DELAY PARA CORREGIR ERRORES DE ATRASO EN ATMEGA328P*/
          }
            digitalWrite(PIN_PA7,LOW);
            
          // --- FIN ---
            while(1)
            {
              tone(PIN_PA6,C*2);
                delay_update(250);
              tone(PIN_PA6,E*2);
                delay_update(250);
              tone(PIN_PA6,G*2);
                delay_update(500);
              noTone(PIN_PA6);
                delay_update(250);
              tone(PIN_PA6,G);
                delay_update(250);
              noTone(PIN_PA6);
                delay_update(250);
              tone(PIN_PA6,G);
                delay_update(250);
              noTone(PIN_PA6);
              // Dejar 1 [s] de datos
              delay_update(1200);
            }
          // --- FIN ---
        } 
        updateNano();
        delay(20);
      } 
      else
      {
        // Calibración de la altura inicial
          calibracionAltura();
      }
    }
}




// --- INTERRUPCIONES ---
  // Servicio de interrupcio del Seguro
  ISR(PORTA_PORT_vect) 
  {
    byte flags = PORTA.INTFLAGS;
    PORTA.INTFLAGS = flags; //clear flags
    
    // Revisar estado del seguro pre-lanzamiento
      if (VPORTA.IN&(1<<5))
      {
          TCB1.CTRLA = 0x0;   // Detiene el Timer
          // Combinación para indicar que está bloqueda la carga
          digitalWrite(PIN_PA3,HIGH);//LED Rojo
          digitalWrite(PIN_PA2,LOW);//LED Verde
          digitalWrite(PIN_PA1,LOW);//LED Azul
          conexion = 1;
          seguro = 1;
          TCB1.CNT = 0x0;         // Valor del contador. Lo iniciamos en 0
          contador_programa = 0;  // Contador a 0
      }
      else
      {
          // Combinación para indicar que está en transición
          digitalWrite(PIN_PA3,LOW);  //LED Rojo
          digitalWrite(PIN_PA2,HIGH); //LED Verde
          digitalWrite(PIN_PA1,HIGH); //LED Azul
          conexion = 0;
          seguro = 1;
          TCB1.CNT = 0x0;         // Valor del contador. Lo iniciamos en 0
          contador_programa = 0;  // Contador a 0
          TCB1.CTRLA = 0x03;      // Inicia el timer a la frecuencia de reloj/2 <8 [MHz]>
      }
  }


  // Servicio de interrupcio del Timer
  ISR(TCB1_INT_vect) 
  {
    TCB1.INTFLAGS = 0x01;   // Reset de la interrupcion (obligatorio)
    if( contador_programa>=TOPE_TIMER )
    {
        TCB1.CTRLA = 0x0;         // Detiene el Timer
        TCB1.CNT = 0x0;           // Valor del contador. Lo iniciamos en 0
        contador_programa = 0;    // Contador a 0
        seguro = 0;
        // Combinación para indicar que está desbloqueda la carga
        digitalWrite(PIN_PA3,LOW);
        digitalWrite(PIN_PA2,HIGH);
        digitalWrite(PIN_PA1,LOW);
    }
    else
    {
      contador_programa++;
    }
  }
