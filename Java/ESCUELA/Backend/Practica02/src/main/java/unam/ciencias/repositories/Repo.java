package unam.ciencias.repositories;

import java.sql.*;

/**
 * Repositorio
 * Esta clase se conecta a la base de datos MySQL con JDBC a traves de un conector que 
 *   debe ser incluido en el classpath a la hora de ejecutarse
 */
public class Repo {
    private static String jdbcURL;
    private static String username;
    private static String password;
    private static Connection connection;

    /**
     * Con este método conectamos a la BD
     */
    public static void conecta() {
        try {
            jdbcURL = "jdbc:mysql://localhost:3306/backend?";
            username = "root";
            password = "317150700Ciencias";

            Class.forName("com.mysql.jdbc.Driver");
            connection = DriverManager.getConnection(jdbcURL, username, password);
        } catch (ClassNotFoundException e) {
            System.out.println("No se pudo conectar con la BD");
            e.printStackTrace();
        } catch (SQLException sqle) {
            sqle.printStackTrace();
        }
    }

    /**
     * Método getCustomers()
     * Imprime en consola todos los customers de la abse de datos
     * @Query lee
     */
    public static void getAllCustomers() {
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
     * Metodo encargado de crear nuevos customers
     * @Query crea
     * @param id enter con el customer_id
     * @param name cadena con el nombre
     * @param surname cadena con el surname
     * @param rfc cadena con el rfc
     * @param mail cadena con el mail 
     * @param region_id entero con region_id
     */
    public static void createCostumer(int id, String name, String surname, String rfc, String mail, int region_id) {
        try {
            String sql = "INSERT INTO customers (customer_id, name, surname, rfc, mail, region_id)\n";
            String query = sql+"VALUES ("+id+", \""+name+"\", \""+surname+"\", \""+rfc+"\", \""+mail+"\", "+region_id+")";
            Statement st = connection.createStatement();
            st.executeUpdate(query);
        } catch (SQLException sqle) {
            sqle.printStackTrace();
        } catch (NullPointerException npe) {
            System.out.println("Por favor introduce un Customer!");
            System.exit(-1);
        }
    }

    /**
     * 
     * @param customer_id entero con el customer_id
     * @Query borra
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

    /**
     * 
     * @param region_id entero 
     * @return LA cadena con el nombre de la region
     * @Query lee
     */
    public static String getRegionName(int region_id){
        try {
            String query = "SELECT region FROM regions WHERE region_id="+region_id;
            Statement st = connection.createStatement();
            ResultSet rs = st.executeQuery(query);
            rs.next();
            return rs.getString("region");
        } catch (SQLException sqle) {
            sqle.printStackTrace();
        }
        return null;
    }
}
