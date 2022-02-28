package unam.ciencias;

import java.sql.*;
import java.util.Scanner;

/**
 * @author Santiago Arroyo
 * Clase encargada de implementar los metodos requeridos en la Practica01
 * Esta clase se conecta a la base de datos MySQL con JDBC a traves de un conector que debe ser incluido en el classpath a la hora de ejecutarse
 * EL nombre de la base de datos y URL se puede editar en el metodo main
 */
public class Main {
	private static String jdbcURL;
	private static String username;
	private static String password;
	private static Connection connection;

    public static void main(String[] args) {
		try {
			jdbcURL = "jdbc:mysql://localhost:3306/backend?";
			username = "root";
			password = "317150700Ciencias";

			Class.forName("com.mysql.jdbc.Driver");
			connection = DriverManager.getConnection(jdbcURL, username, password);

			Scanner s = new Scanner(System.in);
			System.out.println("Por favor selecciona una opcion:");
			System.out.println("[1] Metodo getCostumers");
			System.out.println("[2] Metodo createCostumer(Costumer)");
			System.out.println("[3] Metodo deleteCostumer(costumer_id)");
			int temp = s.nextInt();
			switch (temp) {
				case 1: getCustomers();break;
				case 2: {
					System.out.print("Por favor escribe el id del Costumer: ");
					int id = s.nextInt();
					System.out.print("Por favor escribe el name del Costumer: ");
					String nulleada = s.nextLine();
					String name = s.nextLine();
					System.out.print("Por favor escribe el surname del Costumer: ");
					String surname = s.nextLine();
					System.out.print("Por favor escribe el rfc del Costumer: ");
					String rfc = s.nextLine();
					System.out.print("Por favor escribe el mail del Costumer: ");
					String mail = s.nextLine();
					System.out.print("Por favor escribe el region_id del Costumer: ");
					int region_id = s.nextInt();
					createCustomer(new Customer(id, name, surname, rfc, mail, new Region(region_id)));
					break;
				}
				case 3: {
					System.out.print("Por favor escribe el nombre del Costumer: ");
					int customer_id = s.nextInt();
					deleteCustomer(customer_id);
					break;
				}
				default: {
					System.out.println("Por favor introduce una opcion valida!");
					System.exit(-1);
					break;
				}
			}
		} catch (ClassNotFoundException e) {
			System.out.println("No se pudo conectar con la BD");
			e.printStackTrace();
		} catch (SQLException sqle) {
			sqle.printStackTrace();
		}
	}//Cierre main

	/**
	 * Método getCustomers()
	 * Imprime en consola todos los customers de la abse de datos
	 */
	public static void getCustomers() {
		try {
			String query = "SELECT * FROM customers";
			Statement st = connection.createStatement();
			ResultSet rs = st.executeQuery(query);
			while (rs.next()) {
				int customer_id = rs.getInt("customer_id");
				String name = rs.getString("name");
				String surname = rs.getString("surname");
				String rfc = rs.getString("rfc");
				String mail = rs.getString("mail");
				int region_id = rs.getInt("region_id");

				// Imprimimos los resultados
				System.out.format("%s, %s, %s, %s, %s, %s\n", customer_id, name, surname, rfc, mail, region_id);
			}
			st.close();
		} catch (SQLException sqle) {
			sqle.printStackTrace();
		}
	}

	/**
	 * Metodo create Customer()
	 * Metodo encargado de crear nuevos customers y añadirlos la base de datos
	 * @param c el customer a ser añadido en la base de datos
	 */
	public static void createCustomer(Customer c) {
		try {
			String sql = "INSERT INTO customers (customer_id, name, surname, rfc, mail, region_id)\n";
			String query = sql+"VALUES ("+c.getCustomer_id()+", \""+c.getName()+"\", \""+c.getSurname()+"\", \""+c.getRfc()+"\", \""+c.getMail()+"\", "+c.getRegion().getRegion_id()+")";
			Statement st = connection.createStatement();
			System.out.println(query);
			st.executeUpdate(query);
		} catch (SQLException sqle) {
			sqle.printStackTrace();
		} catch (NullPointerException npe) {
			System.out.println("Por favor introduce un Customer!");
			System.exit(-1);
		}

	}

	/**
	 * Metodo deleteCustomer()
	 * Metodo encargado de borrar un customer de la abse de datos
	 * @param customer_id el id del customer a eliminar
	 */
	public static void deleteCustomer(int customer_id) {
		try {
			String query = "DELETE FROM customers WHERE customer_id="+customer_id;
			Statement st = connection.createStatement();
			st.executeUpdate(query);
		} catch (SQLException sqle) {
			sqle.printStackTrace();
		}
	}
}
