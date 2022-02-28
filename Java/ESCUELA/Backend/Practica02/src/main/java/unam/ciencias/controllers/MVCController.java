package unam.ciencias.controllers;

import java.util.Scanner;

import unam.ciencias.entities.*;
import unam.ciencias.service.Servicio;
 
/**
 * @author Santiago Arroyo
 * Clase encargada de implementar los metodos requeridos en la Practica02
 */
public class MVCController {

    public static void run() {
		Servicio servicio = new Servicio();
		Scanner scan = new Scanner(System.in);
		System.out.println("Por favor selecciona una opcion:");
		System.out.println("[1] Metodo getCostumers");
		System.out.println("[2] Metodo createCostumer(Costumer)");
		System.out.println("[3] Metodo deleteCostumer(costumer_id)");
		int temp = scan.nextInt();
		switch (temp) {
			case 1: Servicio.getCustomers();break;
			case 2: {
				System.out.print("Por favor escribe el id del Costumer: ");
				int id = scan.nextInt();
				System.out.print("Por favor escribe el name del Costumer: ");
				String nulleada = scan.nextLine();
				String name = scan.nextLine();
				System.out.print("Por favor escribe el surname del Costumer: ");
				String surname = scan.nextLine();
				System.out.print("Por favor escribe el rfc del Costumer: ");
				String rfc = scan.nextLine();
				System.out.print("Por favor escribe el mail del Costumer: ");
				String mail = scan.nextLine();
				System.out.print("Por favor escribe el region_id del Costumer: ");
				int region_id = scan.nextInt();
				Region r = Servicio.getRegion(region_id);
				Servicio.createCustomer(new Customer(id, name, surname, rfc, mail, r));
				break;
			}
			case 3: {
				System.out.print("Por favor escribe el nombre del Costumer: ");
				int customer_id = scan.nextInt();
				Servicio.deleteCustomer(customer_id);
				break;
			}
			default: {
				System.out.println("Por favor introduce una opcion valida!");
				System.exit(-1);
				break;
			}
		}
	}//Cierre main
}
