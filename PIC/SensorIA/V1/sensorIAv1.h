#include <18F4550.h>
#device ADC=10

#FUSES NOWDT                    //No Watch Dog Timer

#use delay(crystal=20000kHz)

#define LED PIN_A0
#define DELAY 500


#define USB_CABLE_IS_ATTACHED()  input(PIN_A1)
#define USB_CONFIG_BUS_POWER 500
#define USB_STRINGS_OVERWRITTEN

char USB_STRING_DESC_OFFSET[]={0,4,22};

char const USB_STRING_DESC[]={
   //string 0 - language
      4,  //length of string index
      0x03,  //descriptor type (STRING)
      0x09,0x04,  //Microsoft Defined for US-English
   //string 1 - manufacturer
      18,  //length of string index
      0x03,  //descriptor type (STRING)
      'S',0,
      'e',0,
      'n',0,
      's',0,
      'o',0,
      'r',0,
      'I',0,
      'A',0,
   //string 2 - product
      24,  //length of string index
      0x03,  //descriptor type (STRING)
      'S',0,
      'e',0,
      'n',0,
      's',0,
      'o',0,
      'r',0,
      'T',0,
      'r',0,
      'a',0,
      'c',0,
      'k',0
};

#include <usb_cdc.h>
