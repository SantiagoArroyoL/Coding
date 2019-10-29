package Controlador;
import Modelo.Datos;
import Vista.VentanaPrincipal;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import Modelo.Datos;



/**
 *
 * @author ROOT
 */
public class Metodos implements ActionListener{
    
    private VentanaPrincipal view;
    private Datos model;
        
    public Metodos(VentanaPrincipal view, Datos model) {
        this.view = view;
        this.model = model;
        this.view.btnCalcular.addActionListener(this);
    }
    
    public void iniciar(){
        view.setTitle("MVC Calcular");
        view.setLocationRelativeTo(null);
    }
    
    public void actionPerformed(ActionEvent e){
        model.setA(Double.parseDouble(view.txtL1.getText()));
        model.setB(Double.parseDouble(view.txtL2.getText()));
        model.setC(Double.parseDouble(view.txtL3.getText()));
        model.SemiP();
        model.Calcular();
        view.txtpPerimetro.setText(String.valueOf(model.getS()));
    }   
  
}