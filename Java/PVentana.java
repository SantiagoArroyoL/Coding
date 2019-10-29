import javax.swing.JFrame;
import javax.swing.JLabel;
public class PVentana extends JFrame{
  public static void main(String[] args) {
    PVentana v = new PVentana();
  }
  public PVentana(){
    configuraVentana("Hola");
    agregaElementos();
  }

  public void configuraVentana(String titulo){
    this.setVisible(true);
    this.setSize(800,600);
    this.setTitle(titulo);
    this.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
	this.setLayout(null);
  }
  public void agregaElementos(){
    JLabel lblSaludo1 = new JLabel();
    lblSaludo1.setBounds(0, 0, 120, 40);
    lblSaludo1.setText("Hola mundo, guapos wink wink");
    add(lblSaludo1);

    JLabel lblSaludo2 = new JLabel();
    lblSaludo2.setBounds(200, 200, 100, 100);
    lblSaludo2.setText("Hola mundo, guapos wink wink");
    add(lblSaludo2);

    JLabel lblSaludo3 = new JLabel();
    lblSaludo3.setBounds(250, 100, 90, 80);
    lblSaludo3.setText("Hola mundo, guapos wink wink");
    add(lblSaludo3);

  }
}
