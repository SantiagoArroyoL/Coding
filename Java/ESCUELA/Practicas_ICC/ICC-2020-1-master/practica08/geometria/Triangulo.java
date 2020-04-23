package geometria;
import java.lang.Math;
/**
 *Representa un polígono de tres lados. Está definido por
 *tres puntos en el plano cartesiano.
 *@author Edgar Montiel Ledesma
 *@version 1.0
 */
public class Triangulo{
	private Punto a;
	private Punto b;
	private Punto c;
	private double x1;
   private double x2;
   private double x3;
   private double y1;
   private double y2;
   private double y3;


 public Triangulo(){
     Punto a = new Punto(0,0);
     Punto b = new Punto(1,0);
     Punto c = new Punto(0.5,(Math.sin(3.1416/3)));
   }
   	/*
   	 *Crea un triángulo con los tres puntos dados.
   	 */
 public Triangulo(Punto a, Punto b, Punto c){
     this.a = new Punto(a.getX() ,  a.getY());
     this.b = new Punto(b.getX() ,  b.getY());
     this.c = new Punto(c.getX() ,  c.getY());

	  this.x1 = a.getX();
	  this.x2 = b.getX();
	  this.x3 = c.getX();
	  this.y1 = a.getY();
	  this.y2 = b.getY();
	  this.y3 = c.getY();
     }
     /*
      *Determina si los vértices de este triángulo están alineados.
      */
 public boolean tieneVerticesAlineados(){

  double v1 = (this.y2 - this.y1) / (this.y3 - this.y2);
  double v2 = (this.x2 - this.x1) / (this.x3 - this.x2);

  return v1 == v2;
 }
	/*
	 *Regresa el tipo de este triángulo según la longitud de sus
	 *lados; puede ser equilátero, isósceles o escaleno.
	 */
 public int tipo(){

  double ab = a.distancia(b);
  double bc = b.distancia(c);
  double ca = c.distancia(a);

 	if ((ab == bc) && (bc == ca)){

 	 return EQUILATERO;

  }else if ((ab != bc ) && (bc != ca)){
     return ESCALENO;
  }else {
     return ISOSCELES;
	 }

  }

 public static final int EQUILATERO;
 static {
 	EQUILATERO = 0;
 }

 public static final int ESCALENO;
 static {
 	ESCALENO = 2;
 }

 public static final int ISOSCELES;
 static {
 	ISOSCELES = 1;
 }

}
