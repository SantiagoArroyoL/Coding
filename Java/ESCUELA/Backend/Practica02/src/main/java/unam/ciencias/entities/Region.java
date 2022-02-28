package unam.ciencias.entities;
 
/**
 * Clase Region
 * @Entity
 */
public class Region {
    
    private int region_id;
    private String region;

    public Region(int region_id, String region) {
        this.region_id = region_id;
        this.region = region;
    }

    public int getRegion_id() {
        return region_id;
    }
    public String getRegion() {
        return region;
    }
}