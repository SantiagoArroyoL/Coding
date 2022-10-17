#include <Wire.h>
#include <SPI.h>
#include <SD.h>
#include <EEPROM.h>
#include <Adafruit_BMP085.h>

#define MUESTRAS 6           // 6 alturas en el vector para media móvil
#define ALTURA_UMBRAL_K 30   // 30 [m] de caída para activación 

#define LED 6
#define MOSFET 8
#define CS 10
#define BATT A6

#define MPU6050_ADDRESS  0x69   // Dirección del módulo MPU6050 con su pin AD0 en ALTO
#define PWR_MGMT_1       0x6B   // Configuracion del modo de funcionamiento y selección del reloj
#define USER_CTRL        0x6A   // configuracion de FIFO, I2C y reset de los sens ores
#define CONFIG           0x1A   // Configuracion de el ancho de banda y frecuencia de muestreo
#define SMPRT_DIV        0x19   // Divisor de frecuencia de muestreo para el giroscopio y el Sample Rate
#define GYRO_CONFIG      0x1B   // Rango y resolución del giroscopio
#define ACCEL_CONFIG     0x1C   // Rango y resolución del acelerometro
#define INT_ENABLE       0x38   // Activa las interrupciones

#define ACEL_X_H    0x3B
#define ACEL_X_L    0x3C
#define ACEL_Y_H    0x3D
#define ACEL_Y_L    0x3E
#define ACEL_Z_H    0x3F
#define ACEL_Z_L    0x40

#define GYRO_X_H    0x43
#define GYRO_X_L    0x44
#define GYRO_Y_H    0x45
#define GYRO_Y_L    0x46
#define GYRO_Z_H    0x47
#define GYRO_Z_L    0x48

// [--- DIRECCIONES DE LA EEPROM ---]

  // Estado de vuelo:     |> 0 (Espera), 1 (Vuelo), 2 (Descenso terminado)
  #define DIR_ES_VUELO 0

  // Estado de la IMU:    |> 0 (Funcionamiento correcto), 1 (ERROR)
  #define DIR_ES_IMU   1

  // Estado del BMP180 2: |> 0 (Funcionamiento correcto), 1 (ERROR)
  #define DIR_ES_BMP   2
  
  // Estado de microSD:   |> 0 (Funcionamiento correcto), 1 (ERROR)
  #define DIR_ES_SD    3

  // Altura inicial:      |> 0 -> 2000 [m] & 255 -> 4000 [m]
  #define DIR_ALTURA_0   4

  // Altura máxima:       |> 0 -> 2000 [m] & 255 -> 4000 [m]
  #define DIR_ALTURA_MAX 5

  // Aceleración máxima:  |> 0 -> 0 [g] & 255 -> 20 [g]
  #define DIR_ACEL_TOTAL_MAX 6

  

// [--- VARIABLES ---]

  // Estados de vuelo
      byte estadoVUELO;
      byte contador_impulso;
      byte conexion = 1;

  // Estados de los sensores
      byte estadoIMU = 0;
      byte estadoBMP = 0;
      byte estadoSD = 0;
      
  // Sensor de presión
      Adafruit_BMP085 bmp;

  // Archivo de SD
      File archivo;
      byte N_archivo;
  
  // Datos
      unsigned long t_millis;   // Tiempo desde encendido
      int V_batt;               // Nivel de batería
      unsigned long T0;         // Variable de tiempo inicial
      unsigned long Tf;         // Variable de tiempo final
      byte detonacion = 0;      // Variable de detonacion ATmega328P
      byte detonacionTiny = 0;  // Variable de detonacion ATtiny1614
      
    // Determinación de altura
      float h_0;                // Altura inicial
      float h_max;              // Altura máxima
      float alturas[MUESTRAS];  // Vector de alturas
      float h_media;            // Altura filtrada con media móvil

    // Instrumentación general
      float temp;              // Temperatura
      int presion;             // Presión
      
      byte acelRAW[6];        // Datos en los registros del acelerometro
      float aX;               // Aceleracion en X
      float aY;               // Aceleracion en Y
      float aZ;               // Aceleracion en Z
      float aceleraciones[MUESTRAS];  // Vector de aceleraciones totales
      float aT_media;         // Aceleración total filtrada con media móvil
      
      byte gyroRAW[6];      // Datos en los registros del giroscopio
      float gX;             // Aceleracion en X
      float gY;             // Aceleracion en Y
      float gZ;             // Aceleracion en Z


// [--- FUNCIONES ---]

  // --> wireLectura <--
  byte wireLectura(byte dispositivo, byte direccion)
  {
      Wire.beginTransmission(dispositivo);
      Wire.write(direccion);
      Wire.endTransmission();
      Wire.requestFrom(dispositivo,1);
      byte lectura = Wire.read();
      return lectura;
  }


  // --> wireEscritura <--
  void wireEscritura(byte dispositivo, byte direccion, byte valor)
  {
      Wire.beginTransmission(dispositivo);
      Wire.write(direccion);              
      Wire.write(valor); 
      Wire.endTransmission();
  }


  // --> Inicializacion del MPU6050 <--
  void MPUinit()
  {
      wireEscritura(MPU6050_ADDRESS,PWR_MGMT_1,0x08);     // Despiera al sensor, la fuente de reloj es el oscilador interno (8Mhz) y se desactiva el sensor de temperatura
      wireEscritura(MPU6050_ADDRESS,USER_CTRL,0x01);      // Desactiva FIFO, desactiva I2C master mode, limpia y resetea sensores y sus registros
      wireEscritura(MPU6050_ADDRESS,0x37,0x00);           // ... INT_PIN_CONFIG
      wireEscritura(MPU6050_ADDRESS,INT_ENABLE,0x00);     // Desactiva todas las interrupciones
      wireEscritura(MPU6050_ADDRESS,CONFIG,0x01);         // Frecuencia de muestreo de Acelerometro y giroscopio de 1[kHz] y delay de 2[ms]
      wireEscritura(MPU6050_ADDRESS,SMPRT_DIV,0x07);      // Sample rate = 1[kHz]/(1+7) = 125 [Hz]
      wireEscritura(MPU6050_ADDRESS,GYRO_CONFIG,0x18);    // Rango del giroscopio = 2000 [deg/s] (16.4 [LSB/deg/s])
      wireEscritura(MPU6050_ADDRESS,ACCEL_CONFIG,0x18);   // Rango del acelerometro = 16 [g] (2048 [LSB/g])
  }


  // --> Lectura del acelerometro <--
  void acelLectura()
  {
      acelRAW[0] = wireLectura(MPU6050_ADDRESS, ACEL_X_H);
      acelRAW[1] = wireLectura(MPU6050_ADDRESS, ACEL_X_L);
      acelRAW[2] = wireLectura(MPU6050_ADDRESS, ACEL_Y_H);
      acelRAW[3] = wireLectura(MPU6050_ADDRESS, ACEL_Y_L);
      acelRAW[4] = wireLectura(MPU6050_ADDRESS, ACEL_Z_H);
      acelRAW[5] = wireLectura(MPU6050_ADDRESS, ACEL_Z_L);
      aX = (float)((acelRAW[0] << 8) | acelRAW[1])/2048.0;
      aY = (float)((acelRAW[2] << 8) | acelRAW[3])/2048.0;
      aZ = (float)((acelRAW[4] << 8) | acelRAW[5])/2048.0;
  }


  // --> Lectura del giroscopio <--
  void gyroLectura()
  {
      gyroRAW[0] = wireLectura(MPU6050_ADDRESS, GYRO_X_H);
      gyroRAW[1] = wireLectura(MPU6050_ADDRESS, GYRO_X_L);
      gyroRAW[2] = wireLectura(MPU6050_ADDRESS, GYRO_Y_H);
      gyroRAW[3] = wireLectura(MPU6050_ADDRESS, GYRO_Y_L);
      gyroRAW[4] = wireLectura(MPU6050_ADDRESS, GYRO_Z_H);
      gyroRAW[5] = wireLectura(MPU6050_ADDRESS, GYRO_Z_L);
      gX = (float)((gyroRAW[0] << 8) | gyroRAW[1])/16.4;
      gY = (float)((gyroRAW[2] << 8) | gyroRAW[3])/16.4;
      gZ = (float)((gyroRAW[4] << 8) | gyroRAW[5])/16.4;
  }


  // --> Lectura de la altura con media móvil <--
  float alturaMedia()
  {   
      float sum = 0;
      for(byte i = MUESTRAS-1; i>0; i--)
        alturas[i] = alturas[i-1];
  
      alturas[0] = bmp.readAltitude();
  
      for(byte i = 0; i<MUESTRAS; i++)
        sum += alturas[i];
  
      return sum/MUESTRAS;
  }


  // --> Medición de la altura inicial <--
  void calibracionAltura()
  {
      float sum = 0;
      for(byte j = 0; j<40; j++)
        sum += bmp.readAltitude();
      h_0 = sum/40.0;
      h_max = h_0;
  }


  // --> Medir aceleración total con media móvil <--
  float acelMedia()
  {   
      float sum = 0;
      for(byte i = MUESTRAS-1; i>0; i--)
        aceleraciones[i] = aceleraciones[i-1];
  
      aceleraciones[0] = sqrt( (aX*aX) + (aY*aY) + (aZ*aZ) );
  
      for(byte i = 0; i<MUESTRAS; i++)
        sum += aceleraciones[i];
  
      return sum/MUESTRAS;
  }

  // --> Revisar condición de caída <--
  float respadoAltura()
  {   
      h_media = alturaMedia();
      if( h_media > h_max)
      {
        h_max = h_media;
      }
      else if( (h_max-h_media)>ALTURA_UMBRAL_K )
      {
        EEPROM.write(DIR_ALTURA_MAX,map((int)(h_max),2000,4000,0,255));
        if(!detonacion)
        {
          Tf = millis();
          detonacion = 1;
        }
        digitalWrite(MOSFET,HIGH);
        if( detonacion && ((millis()-Tf)>1200L) )
          digitalWrite(MOSFET,LOW);
      }
  }

  
/*
    // Mode 8: PWM phase and frequency correct. TOP = ICR1
  TCCR1A = 0x80;    //Clear OC1A on compare match when up-counting. Set OC1A on compare match when down counting.
  //TCCR1B = 0x13;  //clkI/O/64 (from prescaler)
  TCCR1B = 0x12;    //clkI/O/8 (from prescaler)
  ICR1 = 0x4E20;    //TOP = 20000 --> 50 [Hz]
  OCR1A = 1000;     //5% Duty cycle --> Velocidad 0

  */

// [--- CONFIGURACION ---]

void setup()
{
  // Iniciar las salidas
    pinMode(LED,OUTPUT);
    pinMode(MOSFET,OUTPUT);
    digitalWrite(MOSFET,LOW);
    digitalWrite(LED,LOW);

      
  // Iniciar las entradas
    pinMode(BATT,INPUT);

    
  // Iniciar comunicaciรณn UART
    Serial.begin(115200);
    delay(2);
    
  // Revisar estado de vuelo anterior
    estadoVUELO = EEPROM.read(DIR_ES_VUELO);
    if(estadoVUELO == 1)
      Serial.write(estadoVUELO);
    
  /* ---- ATtiny lee y decide el incio rรกpido o normal ---- */
    
  // Comunicaciรณn I2C
      Wire.begin();


  // Inicializar sensor BMP180
      byte cont_error = 0;
      while( !bmp.begin(1) )
      {
        if(cont_error>1)
        {
          estadoBMP = 1;     // Levanta bandera de error en BMP
          //-- Activar LED de error //--
          break;
        }
        cont_error++;
      }
  
  
  // Inicializar sensor MPU6050
      MPUinit();
      for(byte i = 0; i<MUESTRAS; i++)
        aceleraciones[i] = 1;
 

  // Inicializaciรณn del vector de alturas y calibraciรณn de la altura inicial
      if(!estadoBMP)
      {
        for(byte i = 0; i<MUESTRAS; i++)
          alturas[i] = bmp.readAltitude();
        calibracionAltura();
      }

  // Iniciar la micro SD
    cont_error = 0;
    while( !SD.begin(CS) )
    {
      if(cont_error>1)
      {
        estadoSD = 1;     // Levanta bandera de error en la microSD
        //-- Activar LED de error //--
        break;
      }
      cont_error++;
    }
  

  // Llevar cuenta de archivos
    if(!estadoSD)
    {
      archivo = SD.open("N_file.txt", FILE_WRITE);
      if(archivo)
      {
        archivo.seek(archivo.position()-1);
        N_archivo = archivo.read();
        archivo.write(N_archivo+1);
        archivo.close();
      }
      else 
        N_archivo = 160;
    }
  


  // Abrir archivo
    if(!estadoSD)
    {
      archivo = SD.open("D"+String(N_archivo-47)+".csv", FILE_WRITE);
      if(archivo)
      {
        archivo.print("Millis,Batt,Altura,Altura_inicial,Altura_max,Conexion_Seguro,Bloqueo_Carga,Detonacion_Carga");
        archivo.println(",Presion,Temperatura,aX,aY,aZ,gX,gY,gZ");
        archivo.flush();
      }
      else 
      {
        estadoSD = 1;     // Levanta bandera de error en la microSD
        //-- Activar LED de error //--
      }
    }

    EEPROM.write(DIR_ES_IMU,estadoIMU);
    EEPROM.write(DIR_ES_BMP,estadoBMP);
    EEPROM.write(DIR_ES_SD,estadoSD);
    EEPROM.write(DIR_ALTURA_0,map((int)(h_0),2000,4000,0,255));
    
    byte estado = estadoVUELO | (estadoIMU << 2) | (estadoBMP << 3) | (estadoSD << 4);
    Serial.write(estado);
    T0 = millis();
} 



// [--- CICLO ---]

void loop()
{ 

  if( millis()-T0 > 1000L )
  {
    digitalWrite(LED,HIGH);
    respadoAltura();
    acelLectura();
    gyroLectura();
    aT_media = acelMedia();
    if(aT_media>3.0)
      contador_impulso += 1;
    else
      contador_impulso = 0;
    presion = bmp.readPressure();
    temp = bmp.readTemperature();
    V_batt = analogRead(BATT);
    t_millis = millis();
    if(!estadoSD)
    {
      archivo.print(t_millis);
        archivo.print(',');
        archivo.print(V_batt);
        archivo.print(',');
        archivo.print(h_media);
        archivo.print(",");
        archivo.print(h_0);
        archivo.print(",");  
        archivo.print(h_max);
        archivo.print(",-1,-1,-1,");
        archivo.print(presion);
        archivo.print(',');
        archivo.print(temp);
        archivo.print(',');
        archivo.print(aX);
        archivo.print(',');
        archivo.print(aY);
        archivo.print(',');
        archivo.print(aZ);
        archivo.print(',');
        archivo.print(gX);
        archivo.print(',');
        archivo.print(gY);
        archivo.print(',');
        archivo.println(gZ);
      archivo.flush();
    }
  }
  
  
    if(Serial.available()>0)
    {
      T0 = millis();
      digitalWrite(LED,LOW);
      acelLectura();
      gyroLectura();
      aT_media = acelMedia();
      if(aT_media>3.0)
        contador_impulso += 1;
      else
        contador_impulso = 0;
      presion = bmp.readPressure();
      temp = bmp.readTemperature();
      V_batt = analogRead(BATT);
      t_millis = millis();
      String info = Serial.readStringUntil('\n');
      if(!estadoSD)
      {
        info = info.substring(0,info.length()-1);
        conexion = info.charAt(info.length()-5) - 48;
        detonacionTiny = info.charAt(info.length()-1) - 48;
          archivo.print(t_millis);
          archivo.print(',');
          archivo.print(V_batt);
          archivo.print(',');
          archivo.print(info);
          archivo.print(',');
          archivo.print(presion);
          archivo.print(',');
          archivo.print(temp);
          archivo.print(',');
          archivo.print(aX);
          archivo.print(',');
          archivo.print(aY);
          archivo.print(',');
          archivo.print(aZ);
          archivo.print(',');
          archivo.print(gX);
          archivo.print(',');
          archivo.print(gY);
          archivo.print(',');
          archivo.println(gZ);
        archivo.flush();
      }
      
      if( estadoVUELO == 2 && conexion )
        respadoAltura();
    }

    if(contador_impulso > 11 && contador_impulso < 14)
    {
      estadoVUELO = 2;
      EEPROM.write(DIR_ES_VUELO,estadoVUELO);
      EEPROM.write(DIR_ACEL_TOTAL_MAX,map((int)(aT_media),0,20,0,255));
    }

    if(detonacionTiny)
      detonacion = 1;
    
}
