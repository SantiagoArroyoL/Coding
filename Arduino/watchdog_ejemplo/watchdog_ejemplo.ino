#include <avr/wdt.h>
// WDT = WatchDog Timer

void setup(){
  Serial.begin(9600);
  Serial.println("Setup started :");
  // el delay antes de iniciar el WDT ayuda a completar las tareas iniciales del setup
  delay(2000);
  wdt_enable(WDTO_4S); 
  // WDTO_4S es una constante de la librería, indica el intervalo de 4 segundos
  // Si pasan 4 segundos sin resetear el WDT, reiniciamos
}

void loop(){
  Serial.println("Estamos en el For ! ");
  // El for toma 4 segundos pero no hace interrupcion pues hacemos reset
  for(int i=0; i<=5; i++){
    Serial.print("For : ");
    Serial.println(i);
    delay(1000);
    wdt_reset();
  }
  //loop infinito
  while(1){Serial.println("LOOP");}
}
