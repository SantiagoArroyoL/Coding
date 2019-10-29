/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package Modelo;

/**
 *
 * @author ROOT
 */
public class Datos {
    public String nombre,artista,albúm,duracion,año,genero;

    public Datos() {
    }

    public Datos(String nombre, String artisra, String albúm, String duracion, String año, String genero) {
        this.nombre = nombre;
        this.artista = artista;
        this.albúm = albúm;
        this.duracion = duracion;
        this.año = año;
        this.genero = genero;
    }

    public String getNombre() {
        return nombre;
    }

    public void setNombre(String nombre) {
        this.nombre = nombre;
    }

    public String getArtista() {
        return artista;
    }

    public void setArtista(String artista) {
        this.artista = artista;
    }

    public String getAlbúm() {
        return albúm;
    }

    public void setAlbúm(String albúm) {
        this.albúm = albúm;
    }

    public String getDuracion() {
        return duracion;
    }

    public void setDuracion(String duracion) {
        this.duracion = duracion;
    }

    public String getAño() {
        return año;
    }

    public void setAño(String año) {
        this.año = año;
    }

    public String getGenero() {
        return genero;
    }

    public void setGenero(String genero) {
        this.genero = genero;
    }
    
}
