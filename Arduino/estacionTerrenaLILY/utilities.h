/*
 * utilities.h pa los propulnenes
 * 
 * La base de este utilities.h, con las direcciones salio de
 * https://github.com/Xinyuan-LilyGO/LilyGo-LoRa-Series 
 */
#pragma once //Corre exactamente una vez

#include <SPI.h>
#include <Wire.h>
#include <axp20x.h> //https://github.com/lewisxhe/AXP202X_Library //AXP192
#include <Arduino.h> 
#include "SparkFun_Ublox_Arduino_Library.h" // https://github.com/sparkfun/SparkFun_Ublox_Arduino_Library //Ublox Neo-6M
#include <MicroNMEA.h> //https://github.com/stevemarple/MicroNMEA

/*
* arduinoLoRa solo funciona con SX1276/SX1278, NO SX1262
* */
#define LILYGO_TBeam_V1_0

/*
* Frecuencias posibles:
*  433E6,470E6,868E6,915E6
* */
#define LoRa_frequency      915E6

#define UNUSE_PIN                   (0)

#define GPS_RX_PIN                  34
#define GPS_TX_PIN                  12
#define BUTTON_PIN                  38  

#define BUTTON_PIN_MASK             GPIO_SEL_38
#define I2C_SDA                     21
#define I2C_SCL                     22
#define PMU_IRQ                     35

#define RADIO_SCLK_PIN               5
#define RADIO_MISO_PIN              19
#define RADIO_MOSI_PIN              27
#define RADIO_CS_PIN                18
#define RADIO_DI0_PIN               26
#define RADIO_RST_PIN               23
#define RADIO_DIO1_PIN              33
#define RADIO_BUSY_PIN              32

#define BOARD_LED                   4
#define LED_ON                      LOW
#define LED_OFF                     HIGH

#define GPS_BAUD_RATE               115200
#define HAS_GPS

// Inicializamos el AXP192
AXP20X_Class PMU;

bool initPMU() {
    // if (PMU.begin(Wire, AXP192_SLAVE_ADDRESS) == AXP_FAIL) {
    //     return false;
    // }
    /*
     * Tiene un LED de carga pero no funciona
     * * * */
    // PMU.setChgLEDMode(LED_BLINK_4HZ);

// IMPORTANTE!!!!!!!!! LA REPO DE LILIYGO DICE:

    /*
    * The default ESP32 power supply has been turned on,
    * no need to set, please do not set it, if it is turned off,
    * it will not be able to program. (2~6V)
    *
    *   PMU.setDCDC3Voltage(3300);
    *   PMU.setPowerOutPut(AXP192_DCDC3, AXP202_ON);
    *
    * * * */

    /*
     *   Apagamos todo lo que no estemos usando.
     */
    PMU.setPowerOutPut(AXP192_DCDC1, AXP202_OFF);
    PMU.setPowerOutPut(AXP192_DCDC2, AXP202_OFF);
    PMU.setPowerOutPut(AXP192_LDO2, AXP202_OFF);
    PMU.setPowerOutPut(AXP192_LDO3, AXP202_OFF);
    PMU.setPowerOutPut(AXP192_EXTEN, AXP202_OFF);

    /*
     * Seteamos los pines de Lora y GPS a 3.3V
     **/
    PMU.setLDO2Voltage(3300);   //LoRa VDD
    PMU.setLDO3Voltage(3300);   //GPS  VDD
    PMU.setDCDC1Voltage(3300);  //3.3V Pin al lado de 21 and 22 es controlado por DCDC1

    PMU.setPowerOutPut(AXP192_DCDC1, AXP202_ON);
    PMU.setPowerOutPut(AXP192_LDO2, AXP202_ON);
    PMU.setPowerOutPut(AXP192_LDO3, AXP202_ON);

    pinMode(PMU_IRQ, INPUT_PULLUP);
    attachInterrupt(PMU_IRQ, [] {
        //pmu_irq = true;
    }, FALLING);

  // Se deben configurar los ADC y checar la bateria (Se puede medir voltaje)
    PMU.adc1Enable(AXP202_VBUS_VOL_ADC1 |
                   AXP202_VBUS_CUR_ADC1 |
                   AXP202_BATT_CUR_ADC1 |
                   AXP202_BATT_VOL_ADC1,
                   AXP202_ON);

    PMU.enableIRQ(AXP202_VBUS_REMOVED_IRQ |
                  AXP202_VBUS_CONNECT_IRQ |
                  AXP202_BATT_REMOVED_IRQ |
                  AXP202_BATT_CONNECT_IRQ,
                  AXP202_ON);
    PMU.clearIRQ();

    return true;
}

/*
 * Apagamos todo lo que no estemos usando
 */
void disablePeripherals(){
    PMU.setPowerOutPut(AXP192_DCDC1, AXP202_OFF);
    PMU.setPowerOutPut(AXP192_LDO2, AXP202_OFF);
    PMU.setPowerOutPut(AXP192_LDO3, AXP202_OFF);
}

/*
 * Seteamos SPI
 */
SPIClass SDSPI(HSPI);

/*
 * Lo llamaremos al inicio del programa
 */
void initBoard() {
    Serial.begin(115200);
    SPI.begin(RADIO_SCLK_PIN, RADIO_MISO_PIN, RADIO_MOSI_PIN);
    // Wire.begin(I2C_SDA, I2C_SCL);
    // Es un serial para el monitor y otro para el GPS
    Serial1.begin(GPS_BAUD_RATE, SERIAL_8N1, GPS_RX_PIN, GPS_TX_PIN);
    initPMU();
}

/**
 * mapeo
 * Dado una voltaje de entrada y un rango, deducimos la presion
 * @param x Voltaje a mapear
 * @param in_main valor minimo de voltaje de entrada [V]
 * @param in_max valor maximo de voltaje de entrada  [V]
 * @param out_min valor minimo de presion de salida  [MPa]
 * @param out_max valor maximo de presion de salida  [MPa]
 * @return Valor de presion en MPa
 */
float mapeo(float X, float in_min, float in_max, float out_min, float out_max)
{
  return out_min + ((X - in_min)*(out_max-out_min)/(in_max-in_min));
}

/**
 * read_pressure
 * Funcion para leer la presion en las entradas analogicas
 */
#define presionPin1  25
unsigned long ADC_Presion_1;
float presion1;

void readPressure() {
  ADC_Presion_1 = analogRead(presionPin1);
  float voltage = (float) ADC_Presion_1 * (5.0/1023.0);
  presion1 =  mapeo(voltage,0.5,4.5,0,6.8948);
}
