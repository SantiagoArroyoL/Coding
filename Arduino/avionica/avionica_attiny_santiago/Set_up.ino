// [------------------------------------------------------ SETUP Y LOOP ------------------------------------------------------]
// [------------------------------------------------------ SETUP Y LOOP ------------------------------------------------------]
// [------------------------------------------------------ SETUP Y LOOP ------------------------------------------------------]
// [------------------------------------------------------ SETUP Y LOOP ------------------------------------------------------]
// [------------------------------------------------------ SETUP Y LOOP ------------------------------------------------------]
// [------------------------------------------------------ SETUP Y LOOP ------------------------------------------------------]

void setup() {      
    // Salidas
    pinMode(PIN_PA7,OUTPUT);        //Carga de liberación
    digitalWrite(PIN_PA7,LOW);      //Desactivar MOSFET
      
    pinMode(PIN_PA3,OUTPUT);        //LED Azul
    pinMode(PIN_PA2,OUTPUT);        //LED Rojo
    pinMode(PIN_PA1,OUTPUT);        //LED Verde

    pinMode(PIN_PA6,OUTPUT);        //Buzzer
    digitalWrite(PIN_PA6,LOW);

    // Iniciar comunicacion UART
    Serial.begin(115200);
    powerRangers();
    delay(100);

    while(!bmp.begin()) {
        tonoERROR(5);
    }
    calibracionAltura();

    tonoOK();
    // Interrupción del seguro
    // Pin PA5 con interrupción al cambio y sin resistencia pullUp:
    PORTA.PIN5CTRL = 0b00000001; // PULLUPEN = 0; ISC = 001 en el cambio

    // Interrupción del timer
    TCB1.CTRLA = 0x0;   // Desactiva el periférico completamente
    TCB1.CTRLB = 0x0;   // <Periodic Interrupt mode>
    TCB1.INTCTRL = 0x1; // Activa la interrupción del timer
    TCB1.CCMP = 0xFFFF; // Valor TOP para reiniciar la cuenta y disparar la interrupción
    //TCB1.CTRLA = 0x03;  // Inicia el timer a la frecuencia de reloj/2 <8 [MHz]>
        
    // Revisar estado del seguro pre-lanzamiento
    if (VPORTA.IN&(1<<5)){
        // Combinación para indicar que está bloqueda la carga
        digitalWrite(PIN_PA3,LOW);//LED Azul
        digitalWrite(PIN_PA2,HIGH);//LED Rojo
        digitalWrite(PIN_PA1,LOW);//LED VERDE
        conexion = 1;
        seguro = 1;
        TCB1.CNT = 0x0;         // Valor del contador. Lo iniciamos en 0
        contador_programa = 0;  // Contador a 0
    } else {
        // Combinación para indicar que está en transición
        digitalWrite(PIN_PA3,HIGH);//LED Azul
        digitalWrite(PIN_PA2,LOW);//LED Rojo
        digitalWrite(PIN_PA1,LOW);//LED Verde
        conexion = 0;
        seguro = 0;
        TCB1.CNT = 0x0;         // Valor del contador. Lo iniciamos en 0
        contador_programa = 0;  // Contador a 0
        TCB1.CTRLA = 0x03;      // Inicia el timer a la frecuencia de reloj/2 <8 [MHz]>
    }
}
