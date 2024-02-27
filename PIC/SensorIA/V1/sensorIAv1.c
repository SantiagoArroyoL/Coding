#include <sensorIAv1.h>

/* TODO: Use usb_cdc_putc() to transmit data to the USB
virtual COM port. Use usb_cdc_kbhit() and usb_cdc_getc() to
receive data from the USB virtual COM port. usb_enumerated()
can be used to see if connected to a host and ready to
communicate. */

void main()
{
	setup_adc_ports(NO_ANALOGS, VSS_VDD);
	usb_init();

	while(TRUE)
	{

		//Example blinking LED program
		output_low(LED);
		delay_ms(DELAY);
		output_high(LED);
		delay_ms(DELAY);

		//TODO: User Code
	}

}
