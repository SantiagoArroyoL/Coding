// --- LOOP ---
void loop() {
    h_media = alturaFiltrada();
    presion = bmp.readPressure();   // Presión barométrica
    temp = bmp.readTemperature();   // Temperatura ambiente
    updateNano();
    //revisaVuelo();
    if(detonacion > 0) {
      tonoOK();
    }
}

// [------------------------------------------------------ INTERRUPCIONES ------------------------------------------------------]
// [------------------------------------------------------ INTERRUPCIONES ------------------------------------------------------]
//Servicio de interrupcion del Seguro
ISR(PORTA_PORT_vect) {
    byte flags = PORTA.INTFLAGS;
    PORTA.INTFLAGS = flags; //clear flags
    // Revisar estado del seguro pre-lanzamiento
    if (VPORTA.IN&(1<<5)) {
        TCB1.CTRLA = 0x0;   // Detiene el Timer
        // Combinación para indicar que está bloqueda la carga
        digitalWrite(PIN_PA3,LOW);//LED Azul
        digitalWrite(PIN_PA2,HIGH);//LED Rojo
        digitalWrite(PIN_PA1,LOW);//LED Verde
        conexion = 1;
        seguro = 0;
        TCB1.CNT = 0x0;         // Valor del contador. Lo iniciamos en 0
        contador_programa = 0;  // Contador a 0
    } else {
        // Combinación para indicar que está en transición
        digitalWrite(PIN_PA3,HIGH);//LED Azul
        digitalWrite(PIN_PA2,LOW);//LED Rojo
        digitalWrite(PIN_PA1,LOW);//LED Verde
        conexion = 0;
        seguro = 1;
        TCB1.CNT = 0x0;         // Valor del contador. Lo iniciamos en 0
        TCB1.CTRLA = 0x03;      // Inicia el timer a la frecuencia de reloj/2 <8 [MHz]>
    }
}

// Servicio de interrupcion del Timer
ISR(TCB1_INT_vect) {
    TCB1.INTFLAGS = 0x01;   // Reset de la interrupcion (obligatorio)
    if( contador_programa>=TOPE_TIMER) {
        TCB1.CTRLA = 0x0;         // Detiene el Timer
        TCB1.CNT = 0x0;           // Valor del contador. Lo iniciamos en 0
        contador_programa = 0;    // Contador a 0
        seguro = 1;
        // Combinación para indicar que está desbloqueda la carga
        digitalWrite(PIN_PA3,LOW);//LED Azul
        digitalWrite(PIN_PA2,LOW);//LED Rojo
        digitalWrite(PIN_PA1,HIGH);//LED Verde
    } else {
        contador_programa++;
    }
}

  /*
   *                 *                  *              *
                                                      *             *
                        *            *                             ___
  *               *                                          |     | |
        *              _________##                 *        / \    | |
                      @\\\\\\\\\##    *     |              |--o|===|-|
  *                  @@@\\\\\\\\##\       \|/|/            |---|   |P|
                    @@ @@\\\\\\\\\\\    \|\\|//|/     *   /     \  |r|
             *     @@@@@@@\\\\\\\\\\\    \|\|/|/         |  M    | |o|
                  @@@@@@@@@----------|    \\|//          |  E    |=|p|
       __         @@ @@@ @@__________|     \|/           |  X    | |u|
  ____|_@|_       @@@@@@@@@__________|     \|/           |_______| |_|
=|__ _____ |=     @@@@ .@@@__________|      |             |@| |@|  | |
____0_____0__\|/__@@@@__@@@__________|_\|/__|___\|/__\|/___________|_|_
 */
