package unam.ciencias;

import java.sql.*;

/**
 * Clase Region
 * @author Santiago Arroyo
 */
public class Region {
    
    private int region_id;
    private String region;

    public Region(int region_id) {
        try {
            String jdbcURL = "jdbc:mysql://localhost:3306/backend?";
            String username = "root";
            String password = "317150700Ciencias";

            Class.forName("com.mysql.jdbc.Driver");
            Connection connection = DriverManager.getConnection(jdbcURL, username, password);

            String query = "SELECT region FROM regions WHERE region_id="+region_id;
            Statement st = connection.createStatement();
            ResultSet rs = st.executeQuery(query);
            rs.next();
            this.region = rs.getString("region");
            this.region_id = region_id;
        } catch (ClassNotFoundException e) {
            System.out.println("No se pudo conectar con la BD");
            e.printStackTrace();
        } catch (SQLException sqle) {
            sqle.printStackTrace();
        }
    }

    public int getRegion_id() {
        return region_id;
    }
    public String getRegion() {
        return region;
    }
}