package unam.ciencias.entities;

/**
 * @Entity
 */
public class Customer {

    private int customer_id;
    private String name;
    private String surname;
    private String rfc;
    private String mail;
    private Region region;
 
    public Customer(int customer_id, String name, String surname, String rfc, String mail, Region region) {
        this.customer_id = customer_id;
        this.name = name;
        this.surname = surname;
        this.rfc = rfc;
        this.mail = mail;
        this.region = region;
    }

    public int getCustomer_id() {
        return customer_id;
    }

    public void setCustomer_id(int customer_id) {
        this.customer_id = customer_id;
    }

    public String getRfc() {
        return rfc;
    }

    public void setRfc(String rfc) {
        this.rfc = rfc;
    }

    public String getMail() {
        return mail;
    }

    public void setMail(String mail) {
        this.mail = mail;
    }

    public Region getRegion() {
        return region;
    }

    public void setRegion(Region region) {
        this.region = region;
    }

    public String getSurname() {
        return surname;
    }

    public void setSurname(String surname) {
        this.surname = surname;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }
    
}