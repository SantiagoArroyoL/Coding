
import java.awt.Color;
import javax.swing.JOptionPane;


public class ArreglosPrincipales extends javax.swing.JFrame {

    /**
     * Creates new form ArreglosPrincipales
     */
    public ArreglosPrincipales() {
        initComponents();
        this.getContentPane().setBackground(Color.cyan);
    }

    /**
     * This method is called from within the constructor to initialize the form.
     * Do NOT modify this code. The content of this method is always
     * regenerated by the Form Editor.
     */
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        btnEntero = new javax.swing.JButton();
        btnDecimal = new javax.swing.JButton();
        btnCaracter = new javax.swing.JButton();
        btnCadena = new javax.swing.JButton();
        jLabel1 = new javax.swing.JLabel();

        setDefaultCloseOperation(javax.swing.WindowConstants.EXIT_ON_CLOSE);

        btnEntero.setText("Entero");
        btnEntero.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                btnEnteroActionPerformed(evt);
            }
        });

        btnDecimal.setText("Decimal");
        btnDecimal.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                btnDecimalActionPerformed(evt);
            }
        });

        btnCaracter.setText("Caracter");
        btnCaracter.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                btnCaracterActionPerformed(evt);
            }
        });

        btnCadena.setText("Cadena");
        btnCadena.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                btnCadenaActionPerformed(evt);
            }
        });

        jLabel1.setText("Arreglos en Java");

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(getContentPane());
        getContentPane().setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addGap(49, 49, 49)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING, false)
                    .addComponent(btnEntero, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                    .addComponent(btnCaracter, javax.swing.GroupLayout.DEFAULT_SIZE, 84, Short.MAX_VALUE))
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED, 139, Short.MAX_VALUE)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(btnCadena, javax.swing.GroupLayout.Alignment.TRAILING, javax.swing.GroupLayout.PREFERRED_SIZE, 79, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(btnDecimal, javax.swing.GroupLayout.Alignment.TRAILING, javax.swing.GroupLayout.PREFERRED_SIZE, 79, javax.swing.GroupLayout.PREFERRED_SIZE))
                .addGap(49, 49, 49))
            .addGroup(layout.createSequentialGroup()
                .addGap(155, 155, 155)
                .addComponent(jLabel1)
                .addContainerGap(javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addGap(38, 38, 38)
                .addComponent(jLabel1)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.UNRELATED)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
                    .addComponent(btnEntero)
                    .addComponent(btnDecimal))
                .addGap(57, 57, 57)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
                    .addComponent(btnCaracter)
                    .addComponent(btnCadena))
                .addContainerGap(134, Short.MAX_VALUE))
        );

        pack();
    }// </editor-fold>//GEN-END:initComponents

    private void btnEnteroActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_btnEnteroActionPerformed
        // TODO add your handling code here:
        int cont;
        int[] arregloEntero = new int[7];
        for(cont=0;cont<7;cont++){
            arregloEntero[cont]= Integer.parseInt(JOptionPane.showInputDialog(this,"Escribe un número"));
            System.out.println(arregloEntero[cont]);
        }
    }//GEN-LAST:event_btnEnteroActionPerformed

    private void btnCadenaActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_btnCadenaActionPerformed
        int cont;
        String[] arregloCadena = new String[7];
        for(cont=0;cont<7;cont++){
            arregloCadena[cont]= JOptionPane.showInputDialog(this,"Escribe un número");
            System.out.println(arregloCadena[cont]);
        }
    }//GEN-LAST:event_btnCadenaActionPerformed

    private void btnCaracterActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_btnCaracterActionPerformed

        }
    }//GEN-LAST:event_btnCaracterActionPerformed

    private void btnDecimalActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_btnDecimalActionPerformed
        // TODO add your handling code here:
        int cont;
        float[] arregloDecimal = new float[7];
        for(cont=0;cont<7;cont++){
            arregloDecimal[cont]= Float.parseFloat(JOptionPane.showInputDialog(this,"Escribe un número"));
            System.out.println(arregloDecimal[cont]);
        }
    }//GEN-LAST:event_btnDecimalActionPerformed

    /**
     * @param args the command line arguments
     */
    public static void main(String args[]) {
        /* Set the Nimbus look and feel */
        //<editor-fold defaultstate="collapsed" desc=" Look and feel setting code (optional) ">
        /* If Nimbus (introduced in Java SE 6) is not available, stay with the default look and feel.
         * For details see http://download.oracle.com/javase/tutorial/uiswing/lookandfeel/plaf.html
         */
        try {
            for (javax.swing.UIManager.LookAndFeelInfo info : javax.swing.UIManager.getInstalledLookAndFeels()) {
                if ("Nimbus".equals(info.getName())) {
                    javax.swing.UIManager.setLookAndFeel(info.getClassName());
                    break;
                }
            }
        } catch (ClassNotFoundException ex) {
            java.util.logging.Logger.getLogger(ArreglosPrincipales.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (InstantiationException ex) {
            java.util.logging.Logger.getLogger(ArreglosPrincipales.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (IllegalAccessException ex) {
            java.util.logging.Logger.getLogger(ArreglosPrincipales.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (javax.swing.UnsupportedLookAndFeelException ex) {
            java.util.logging.Logger.getLogger(ArreglosPrincipales.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        }
        //</editor-fold>

        /* Create and display the form */
        java.awt.EventQueue.invokeLater(new Runnable() {
            public void run() {
                new ArreglosPrincipales().setVisible(true);
            }
        });
    }

    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JButton btnCadena;
    private javax.swing.JButton btnCaracter;
    private javax.swing.JButton btnDecimal;
    private javax.swing.JButton btnEntero;
    private javax.swing.JLabel jLabel1;
    // End of variables declaration//GEN-END:variables
}
