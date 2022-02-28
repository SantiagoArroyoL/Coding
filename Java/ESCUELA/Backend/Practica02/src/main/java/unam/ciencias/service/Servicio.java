package unam.ciencias.service;

import unam.ciencias.repositories.*;
import unam.ciencias.entities.*;

/**
 * @Service
 * @Autowired
 * La clase estáa conectada automaticamente al repositorio
 */
public class Servicio {

    /**
     * Inicializamos la conexión con la Repo
     */
    public Servicio() {
        Repo.conecta();
    }

    /**
     * Método getCustomers()
     * Imprime en consola todos los customers de la abse de datos
     * @Transactional lee
     */
    public static void getCustomers() {
        Repo.getAllCustomers();
    }

    /**
     * Metodo create Customer()
     * Metodo encargado de crear nuevos customers
     * @param c el customer a ser añadido en la base de datos
     * @Transactional crea
     */
    public static void createCustomer(Customer c) {
        Repo.createCostumer(c.getCustomer_id(), c.getName(), c.getSurname(), c.getRfc(), c.getMail(), c.getRegion().getRegion_id());
    }

    /**
     * Metodo deleteCustomer()
     * Metodo encargado de borrar un customer
     * @param customer_id el id del customer a eliminar
     * @Transactional borra
     */
    public static void deleteCustomer(int customer_id) {
        Repo.deleteCustomer(customer_id);
    }

    /**
     * 
     * @param region_id el numero entero del id de la region 
     * @return Objeto Region que correponde al region_id
     * @Transactional lee
     */
    public static Region getRegion(int region_id) {
        return new Region(region_id, Repo.getRegionName(region_id));
    }
}