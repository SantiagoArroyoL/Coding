/*Programador: Santiago Arroyo
 Objetivo: Programa que te da la formula general
 Fecha: 14/noviembre/2018
 */
//librerias necesarias
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JTextField;

public class Formulario implements ActionListener{//implementando el listener de eventos

    JButton bt1;//creando variables globales de los botones
    JLabel jl1, jl2, jl3, jl4, jl5;//creando variables globales para las etiquetas
    JTextField jt1, jt2, jt3, jt4, jt5;//creando variables globales para los campos de texto
    JFrame jf = new JFrame("Formulario Basico Java");//creacion de ventana con el titulo

    public Formulario(){//constructor de la clase

        jf.setLayout(new FlowLayout());//Configurar como se dispondra el espacio del jframe
        Dimension d = new Dimension();//objeto para obtener el ancho de la pantalla

        //Instanciando etiquetas
        jl1 = new JLabel("Dame el valor de a");
        jl2 = new JLabel("Dame el valor de b");
        jl3 = new JLabel("Dame el valor de c");
        jl4 = new JLabel("Resultado 1: ");
        jl5 = new JLabel("Resultado 2: ");

        //Instanciando cuadros de texto
        jt1 = new JTextField(2);
        jt2 = new JTextField(2);
        jt3 = new JTextField(2);
        jt4 = new JTextField(5);
        jt5 = new JTextField(5);

        //Instanciando boton con texto
        bt1 = new JButton("Saquemos la Formula general!");

        //añadiendo objetos a la ventana
        jf.add(jl1);
        jf.add(jt1);
        jf.add(jl2);
        jf.add(jt2);
        jf.add(jl3);
        jf.add(jt3);
        jf.add(bt1);
        jf.add(jl4);
        jf.add(jt4);
        jf.add(jl5);
        jf.add(jt5);


        //margenes para texto en el boton
        bt1.setMargin(new Insets(10, 10, 10, 10));

        //añadiendo el listener a los botones para manipular los eventos del click
        bt1.addActionListener(this);

        jf.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);//finaliza el programa cuando se da click en la X
        jf.setResizable(false);//para configurar si se redimensiona la ventana
        jf.setLocation((int) ((d.getWidth()/2)+290), 50);//para ubicar inicialmente donde se muestra la ventana (x, y)
        jf.setSize(500, 350);//configurando tamaño de la ventana (ancho, alto)
        jf.setVisible(true);//configurando visualización de la venta
    }

    public static void main(String[] args) {
        Formulario gj = new Formulario();//uso de constructor para la ventana
    }

    @Override
    public void actionPerformed(ActionEvent e) {//sobreescribimos el metodo del listener

        double a, b, c, r1, r2;//variables que almacenaran los numeros de los campos de texto

        if(e.getSource()==bt1){//podemos comparar por el contenido del boton

            //Los campos de texto son de tipo string, asi que tomamos la cadena con el metodo .getText()
            //y lo almacenamos en la variable.
            a = Double.parseDouble(jt1.getText());
            b = Double.parseDouble(jt2.getText());
            c = Double.parseDouble(jt3.getText());

            r1 = (-b + Math.sqrt(Math.pow(b, 2)-4*a*c))/(2*a); //realizamos la operacion
            r2 = (-b - Math.sqrt(Math.pow(b, 2)-4*a*c))/(2*a);

            jt4.setText(""+r1);//mostramos el valor mediante el metodo .setText() como muestra cadenas anteponemos una cadena vacia y concatenamos el resultado
            jt5.setText(""+r2);

            //Esta parte se va a la consola, al cmd o a la terminal sóo para llevar control de los datos
             System.out.println("El contenido de a es: " + a);
             System.out.println("El contenido de b es: " + b);
             System.out.println("El contenido de c es: " + c);
             System.out.println("El contenido de r1 es: " + r1);
             System.out.println("El contenido de r2 es: " + r2);

             /*Si el resultado es imaginario (NO FUNCIONA TODAVÍA)
             if (double.isNan(r1) || double.isNAn(r2)) {
               System.out.println("EL resultado es imaginario");
             }*/
        }
    }
}
