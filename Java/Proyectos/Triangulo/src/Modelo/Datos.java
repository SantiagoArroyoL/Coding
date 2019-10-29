package Modelo;

/**
 *
 * @author Santiago Arroyo
 */
public class Datos {

    private double a, b, c, area, s, Salvacion;
    
    
    public double getA() {
        return a;
    }

    public void setA(double a) {
        this.a = a;
    }

    public double getB() {
        return b;
    }

    public void setB(double b) {
        this.b = b;
    }

    public double getC() {
        return c;
    }

    public void setC(double c) {
        this.c = c;
    }

    public double getArea() {
        return area;
    }

    public void setArea(double area) {
        this.area = area;
    }

    public double getS() {
        return s;
    }

    public void setS(double s) {
        this.s = s;
    }

    public double getSalvacion() {
        return Salvacion;
    }

    public void setSalvacion(double Salvacion) {
        this.Salvacion = Salvacion;
    }

   public double SemiP(){
        this.s = (a+b+c)/2;
  
        return this.s;
   }
    public double Calcular(){
        SemiP();
        this.Salvacion = s*(s-a)*(s-b)*(s-c);
        this.area = Math.sqrt(Salvacion);
        return this.area;
    }
}
