package gato;

public class Ventana extends javax.swing.JFrame {

    private String[][] matriz = new String[3][3];
    private boolean t = true; //turno
	private String ganador = "";

    public Ventana() {//Inicializa variables
        initComponents();
        for(int i = 0; i < matriz.length; i++){
            for(int j = 0; j < matriz[i].length; j++){
                matriz[i][j] = "";
            }
        }
    }

	private void checaTablero() {
		if ((checaDiagonales() || checaColumnas()) || checaFilas()) {
			System.out.println("****************");
			System.out.println("Ganó el jugador" + ganador);
			System.out.println("****************");
			System.exit(0);
		}
		for(int i = 0; i < matriz.length; i++){
            for(int j = 0; j < matriz[i].length; j++){
                if (matriz[i][j].equals(""))
					return;
            }
        }
		System.out.println("****************");
		System.out.println("Es un empate");
		System.out.println("****************");
		System.exit(0);
	}

	private boolean checaFilas() {
		int contO = 0,  contX = 0;
		for(int i = 0; i < matriz.length; i++) {
			contO = contX = 0;
            for(int j = 0; j < matriz[i].length; j++) {
                if (matriz[i][j].equals("X"))
					contX++;
				else if (matriz[i][j].equals("O"))
					contO++;
            }
			if (contO == 3 || contX == 3)
				break;
        }
		if (contO == 3) {
			ganador = "O";
			return true;
		} else if (contX == 3){
			ganador = "X";
			return true;
		}
		return false;
	}

	private boolean checaDiagonales() {
		if (matriz[0][0].equals("X") && (matriz[1][1].equals("X") && matriz[2][2].equals("X"))) {
			ganador = "X";
			return true;
		} else if (matriz[0][0].equals("O") && (matriz[1][1].equals("O") && matriz[2][2].equals("O"))) {
			ganador = "O";
			return true;
		} else if (matriz[0][2].equals("X") && (matriz[1][1].equals("X") && matriz[2][0].equals("X"))) {
			ganador = "X";
			return true;
		} else if (matriz[0][2].equals("O") && (matriz[1][1].equals("O") && matriz[2][0].equals("O"))) {
			ganador = "O";
			return true;
		}
		return false;
	}

	private boolean checaColumnas() {
		int contO = 0,  contX = 0;
		for(int j = 0; j < matriz.length; j++) {
			contO = contX = 0;
            for(int i = 0; i < matriz[j].length; i++) {
                if (matriz[i][j].equals("X"))
					contX++;
				else if (matriz[i][j].equals("O"))
					contO++;
            }
			if (contO == 3 || contX == 3)
				break;
        }
		if (contO == 3) {
			ganador = "O";
			return true;
		} else if (contX == 3){
			ganador = "X";
			return true;
		}
		return false;
	}

    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        boton2 = new javax.swing.JButton();
        boton3 = new javax.swing.JButton();
        boton4 = new javax.swing.JButton();
        boton5 = new javax.swing.JButton();
        boton6 = new javax.swing.JButton();
        boton7 = new javax.swing.JButton();
        boton8 = new javax.swing.JButton();
        boton9 = new javax.swing.JButton();
        boton1 = new javax.swing.JButton();

        setDefaultCloseOperation(javax.swing.WindowConstants.EXIT_ON_CLOSE);

        boton2.setFont(new java.awt.Font("Cambria", 1, 36)); // NOI18N
        boton2.addMouseListener(new java.awt.event.MouseAdapter() {
            public void mouseClicked(java.awt.event.MouseEvent evt) {
                boton2MouseClicked(evt);
            }
        });

        boton3.setFont(new java.awt.Font("Cambria", 1, 36)); // NOI18N
        boton3.addMouseListener(new java.awt.event.MouseAdapter() {
            public void mouseClicked(java.awt.event.MouseEvent evt) {
                boton3MouseClicked(evt);
            }
        });

        boton4.setFont(new java.awt.Font("Cambria", 1, 36)); // NOI18N
        boton4.addMouseListener(new java.awt.event.MouseAdapter() {
            public void mouseClicked(java.awt.event.MouseEvent evt) {
                boton4MouseClicked(evt);
            }
        });

        boton5.setFont(new java.awt.Font("Cambria", 1, 36)); // NOI18N
        boton5.addMouseListener(new java.awt.event.MouseAdapter() {
            public void mouseClicked(java.awt.event.MouseEvent evt) {
                boton5MouseClicked(evt);
            }
        });

        boton6.setFont(new java.awt.Font("Cambria", 1, 36)); // NOI18N
        boton6.addMouseListener(new java.awt.event.MouseAdapter() {
            public void mouseClicked(java.awt.event.MouseEvent evt) {
                boton6MouseClicked(evt);
            }
        });

        boton7.setFont(new java.awt.Font("Cambria", 1, 36)); // NOI18N
        boton7.addMouseListener(new java.awt.event.MouseAdapter() {
            public void mouseClicked(java.awt.event.MouseEvent evt) {
                boton7MouseClicked(evt);
            }
        });

        boton8.setFont(new java.awt.Font("Calibri", 1, 36)); // NOI18N
        boton8.addMouseListener(new java.awt.event.MouseAdapter() {
            public void mouseClicked(java.awt.event.MouseEvent evt) {
                boton8MouseClicked(evt);
            }
        });

        boton9.setFont(new java.awt.Font("Calibri", 1, 36)); // NOI18N
        boton9.addMouseListener(new java.awt.event.MouseAdapter() {
            public void mouseClicked(java.awt.event.MouseEvent evt) {
                boton9MouseClicked(evt);
            }
        });

        boton1.setFont(new java.awt.Font("Cambria", 1, 36)); // NOI18N
        boton1.addMouseListener(new java.awt.event.MouseAdapter() {
            public void mouseClicked(java.awt.event.MouseEvent evt) {
                boton1MouseClicked(evt);
            }
        });

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(getContentPane());
        getContentPane().setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addGap(104, 104, 104)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING, false)
                    .addGroup(layout.createSequentialGroup()
                        .addComponent(boton7, javax.swing.GroupLayout.PREFERRED_SIZE, 125, javax.swing.GroupLayout.PREFERRED_SIZE)
                        .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                        .addComponent(boton8, javax.swing.GroupLayout.PREFERRED_SIZE, 125, javax.swing.GroupLayout.PREFERRED_SIZE))
                    .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING, false)
                        .addGroup(layout.createSequentialGroup()
                            .addComponent(boton4, javax.swing.GroupLayout.PREFERRED_SIZE, 125, javax.swing.GroupLayout.PREFERRED_SIZE)
                            .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                            .addComponent(boton5, javax.swing.GroupLayout.PREFERRED_SIZE, 125, javax.swing.GroupLayout.PREFERRED_SIZE))
                        .addGroup(layout.createSequentialGroup()
                            .addComponent(boton1, javax.swing.GroupLayout.PREFERRED_SIZE, 125, javax.swing.GroupLayout.PREFERRED_SIZE)
                            .addGap(45, 45, 45)
                            .addComponent(boton2, javax.swing.GroupLayout.PREFERRED_SIZE, 125, javax.swing.GroupLayout.PREFERRED_SIZE))))
                .addGap(47, 47, 47)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(boton6, javax.swing.GroupLayout.PREFERRED_SIZE, 125, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(boton3, javax.swing.GroupLayout.PREFERRED_SIZE, 125, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(boton9, javax.swing.GroupLayout.PREFERRED_SIZE, 125, javax.swing.GroupLayout.PREFERRED_SIZE))
                .addContainerGap(130, Short.MAX_VALUE))
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addGap(70, 70, 70)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(boton3, javax.swing.GroupLayout.PREFERRED_SIZE, 118, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(boton2, javax.swing.GroupLayout.PREFERRED_SIZE, 118, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(boton1, javax.swing.GroupLayout.PREFERRED_SIZE, 118, javax.swing.GroupLayout.PREFERRED_SIZE))
                .addGap(36, 36, 36)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(boton5, javax.swing.GroupLayout.PREFERRED_SIZE, 118, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(boton4, javax.swing.GroupLayout.PREFERRED_SIZE, 118, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(boton6, javax.swing.GroupLayout.PREFERRED_SIZE, 118, javax.swing.GroupLayout.PREFERRED_SIZE))
                .addGap(27, 27, 27)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(boton7, javax.swing.GroupLayout.PREFERRED_SIZE, 118, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(boton8, javax.swing.GroupLayout.PREFERRED_SIZE, 118, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(boton9, javax.swing.GroupLayout.PREFERRED_SIZE, 118, javax.swing.GroupLayout.PREFERRED_SIZE))
                .addContainerGap(45, Short.MAX_VALUE))
        );

        pack();
    }// </editor-fold>//GEN-END:initComponents

    private void boton1MouseClicked(java.awt.event.MouseEvent evt) {//GEN-FIRST:event_boton1MouseClicked
        String jugador;
        int fila = 0, columna = 0;
        if(t){
            jugador = "X";
            t = turno(jugador);
        }
        else{
            jugador = "O";
            t = turno(jugador);
        }
        tablero(jugador, fila, columna);
        boton1.setText(jugador);
		checaTablero();
    }//GEN-LAST:event_boton1MouseClicked

    private void boton2MouseClicked(java.awt.event.MouseEvent evt) {//GEN-FIRST:event_boton2MouseClicked
        String jugador;
        int fila = 0, columna = 1;
        if(t){
            jugador = "X";
            t = turno(jugador);
        }
        else{
            jugador = "O";
            t = turno(jugador);
        }
        tablero(jugador, fila, columna);
        boton2.setText(jugador);
		checaTablero();
    }//GEN-LAST:event_boton2MouseClicked

    private void boton3MouseClicked(java.awt.event.MouseEvent evt) {//GEN-FIRST:event_boton3MouseClicked
        String jugador;
        int fila = 0, columna = 2;
        if(t){
            jugador = "X";
            t = turno(jugador);
        }
        else{
            jugador = "O";
            t = turno(jugador);
        }
        tablero(jugador, fila, columna);
        boton3.setText(jugador);
		checaTablero();
    }//GEN-LAST:event_boton3MouseClicked

    private void boton4MouseClicked(java.awt.event.MouseEvent evt) {//GEN-FIRST:event_boton4MouseClicked
        String jugador;
        int fila = 1, columna = 0;
        if(t){
            jugador = "X";
            t = turno(jugador);
        }
        else{
            jugador = "O";
            t = turno(jugador);
        }
        tablero(jugador, fila, columna);
        boton4.setText(jugador);
		checaTablero();
    }//GEN-LAST:event_boton4MouseClicked

    private void boton5MouseClicked(java.awt.event.MouseEvent evt) {//GEN-FIRST:event_boton5MouseClicked
        String jugador;
        int fila = 1, columna = 1;
        if(t){
            jugador = "X";
            t = turno(jugador);
        }
        else{
            jugador = "O";
            t = turno(jugador);
        }
        tablero(jugador, fila, columna);
        boton5.setText(jugador);
		checaTablero();
    }//GEN-LAST:event_boton5MouseClicked

    private void boton6MouseClicked(java.awt.event.MouseEvent evt) {//GEN-FIRST:event_boton6MouseClicked
        String jugador;
        int fila = 1, columna = 2;
        if(t){
            jugador = "X";
            t = turno(jugador);
        }
        else{
            jugador = "O";
            t = turno(jugador);
        }
        tablero(jugador, fila, columna);
        boton6.setText(jugador);
		checaTablero();
    }//GEN-LAST:event_boton6MouseClicked

    private void boton7MouseClicked(java.awt.event.MouseEvent evt) {//GEN-FIRST:event_boton7MouseClicked
        String jugador;
        int fila = 2, columna = 0;
        if(t){
            jugador = "X";
            t = turno(jugador);
        }
        else{
            jugador = "O";
            t = turno(jugador);
        }
        tablero(jugador, fila, columna);
        boton7.setText(jugador);
		checaTablero();
    }//GEN-LAST:event_boton7MouseClicked

    private void boton8MouseClicked(java.awt.event.MouseEvent evt) {//GEN-FIRST:event_boton8MouseClicked
        String jugador;
        int fila = 2, columna = 1;
        if(t){
            jugador = "X";
            t = turno(jugador);
        }
        else{
            jugador = "O";
            t = turno(jugador);
        }
        tablero(jugador, fila, columna);
        boton8.setText(jugador);
		checaTablero();
    }//GEN-LAST:event_boton8MouseClicked

    private void boton9MouseClicked(java.awt.event.MouseEvent evt) {//GEN-FIRST:event_boton9MouseClicked
        String jugador;
        int fila = 2, columna = 2;
        if(t){
            jugador = "X";
            t = turno(jugador);
        }
        else{
            jugador = "O";
            t = turno(jugador);
        }
        tablero(jugador, fila, columna);
        boton9.setText(jugador);
		checaTablero();
    }//GEN-LAST:event_boton9MouseClicked

    /**
     * Devuelve verdadero si es el turno de "X", devuelve falso si es el turno de "O"
     * @param jugador
     * @return
     */
    public boolean turno(String jugador){
        if(jugador.equals("X")){
            t = false;
        }
        else{
            t = true;
        }
        return t;
    }
    /**
     * Método que guarda las jugadas
     */
    public void tablero(String jugador, int fila, int columna){
        matriz[fila][columna] = jugador;
    }

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
            java.util.logging.Logger.getLogger(Ventana.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (InstantiationException ex) {
            java.util.logging.Logger.getLogger(Ventana.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (IllegalAccessException ex) {
            java.util.logging.Logger.getLogger(Ventana.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (javax.swing.UnsupportedLookAndFeelException ex) {
            java.util.logging.Logger.getLogger(Ventana.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        }
        //</editor-fold>

        /* Create and display the form */
        java.awt.EventQueue.invokeLater(new Runnable() {
            public void run() {
                new Ventana().setVisible(true);
            }
        });
    }

    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JButton boton1;
    private javax.swing.JButton boton2;
    private javax.swing.JButton boton3;
    private javax.swing.JButton boton4;
    private javax.swing.JButton boton5;
    private javax.swing.JButton boton6;
    private javax.swing.JButton boton7;
    private javax.swing.JButton boton8;
    private javax.swing.JButton boton9;
    // End of variables declaration//GEN-END:variables
}
