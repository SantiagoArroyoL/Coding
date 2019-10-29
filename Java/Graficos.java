import javax.swing.JFrame;//clase_de_la_que se hereda;
import java.awt.*;
public class Graficos extends JFrame{
  public static void main (String[]args){
    Graficos v=new Graficos();

  }
  public Graficos(){//BOBconstructor.
    configuraVentana("Hola Mundo");

  }
  public void configuraVentana (String titulo){
    this.setTitle(titulo);//hace titulo
    this.setVisible(true);// lo hace visible
    this.setSize(400,200);//tamaño de PrimerVentana
    this.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);//Cerrar hasta cmd y como cierra en lo que recibe
                                    //HIDE_ON_CLOSE DO_NOTHING

  }
  public void paint(Graphics h){
    super.paint(h);
    h.setColor(Color.blue);
    h.drawLine(120, 180, 200, 260);
    h.setColor(Color.RED);
    h.drawLine(200, 180, 120, 260);
    h.setColor(Color.pink);
    h.drawLine(120, 180, 120, 260);
    h.setColor(Color.cyan);
    h.drawLine(120, 180, 200, 180);
    h.setColor(Color.magenta);
    h.drawLine(200, 180, 200, 260);
    h.setColor(Color.BLACK);
    h.drawLine(200, 260, 120, 260);
    h.setColor(Color.red);
    h.drawRect(260, 200, 80, 80);
    h.drawRect(350, 200, 80, 80);
    h.drawOval(120, 300, 80, 80);
    h.setColor(Color.cyan);
    h.fillOval(210, 300, 80, 80);
    h.fillRect(260, 200, 80, 80);
  }
}
