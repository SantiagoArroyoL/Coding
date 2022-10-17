package sort;

import java.awt.BorderLayout;
import java.awt.EventQueue;
import java.awt.Graphics2D;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.image.BufferedImage;
import java.io.File;
import java.util.List;
import java.util.Random;
import javax.imageio.ImageIO;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.SwingWorker;
import javax.swing.UIManager;

public class Sort {

  int[] numeros;

  public Sort(String archivo, int framerate, String metodo) {
    EventQueue.invokeLater(new Runnable() {
      @Override
      public void run() {
        try {
          UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
          JFrame frame = new JFrame("Ordenamientos");
          frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
          frame.setLayout(new BorderLayout());
          frame.add(new Contenedor(archivo, framerate, metodo));
          frame.pack();
          frame.setLocationRelativeTo(null);
          frame.setVisible(true);
        } catch (Exception e) {
          System.out.println("\t:(");
        }
      }
    });
  }

  public class Contenedor extends JPanel {

    private JLabel etiqueta;

    public Contenedor(String archivo, int framerate, String metodo) {
      setLayout(new BorderLayout());
      etiqueta = new JLabel(new ImageIcon(createImage(archivo)));
      add(etiqueta);
      JButton botonOrdenar = new JButton("Ordenar");
      add(botonOrdenar, BorderLayout.SOUTH);
      botonOrdenar.addActionListener(new ActionListener() {
        @Override
        public void actionPerformed(ActionEvent e) {
          BufferedImage imagen = (BufferedImage) ((ImageIcon) etiqueta.getIcon()).getImage();
          new UpdateWorker(imagen, etiqueta, archivo, framerate, metodo).execute();
        }
      });

    }

    public BufferedImage createImage(String archivo) {
      BufferedImage imagen = null;
      try {
        imagen = ImageIO.read(new File("resource/" + archivo));
        ataqueHackerman(imagen);
        Graphics2D g = imagen.createGraphics();
        g.dispose();
      } catch (Exception e) {
        System.err.println("(-)\tAsegurate de estar en el directorio 'src'");
        System.err.println("\ty de haber escrito bien el nombre de imagen (la cual debe estar en la carpeta resource)");
      }
      return imagen;
    }

    public void ataqueHackerman(BufferedImage imagen) {
      int length = imagen.getHeight() * imagen.getWidth();
      numeros = new int[length];
      for (int i = 0; i < numeros.length; i++)
        numeros[i] = i;
      Random r = new Random();
      for (int i = 0; i < length; i++) {
        int j = r.nextInt(length);
        swapImagen(imagen, i, j);
      }
    }

    public void swapImagen(BufferedImage imagen, int i, int j) {
      int colI = i % imagen.getWidth();
      int renI = i / imagen.getWidth();
      int colJ = j % imagen.getWidth();
      int renJ = j / imagen.getWidth();
      int aux = imagen.getRGB(colI, renI);
      imagen.setRGB(colI, renI, imagen.getRGB(colJ, renJ));
      imagen.setRGB(colJ, renJ, aux);
      aux = numeros[i];
      numeros[i] = numeros[j];
      numeros[j] = aux;
    }

  }

  public class UpdateWorker extends SwingWorker<BufferedImage, BufferedImage> {

    private BufferedImage referencia;
    private BufferedImage copia;
    private JLabel target;
    int framerate;
    int n;
    String metodo;
    int iteracion;

    public UpdateWorker(BufferedImage master, JLabel target, String archivo, int speed, String algoritmo) {
      this.target = target;
      try {
        referencia = ImageIO.read(new File("resource/" + archivo));
        copia = master;
        n = copia.getHeight() * copia.getWidth();
      } catch (Exception e) {
        System.err.println(":c Esto no deberia ocurrir");
      }
      framerate = speed; // Indica cada cuantas iteraciones se actualizara la imagen
      metodo = algoritmo;
      iteracion = 0;
    }

    public BufferedImage updateImage() {
      Graphics2D g = copia.createGraphics();
      g.drawImage(copia, 0, 0, null);
      g.dispose();
      return copia;
    }

    @Override
    protected void process(List<BufferedImage> chunks) {
      target.setIcon(new ImageIcon(chunks.get(chunks.size() - 1)));
    }

    public void update() {
      for (int i = 0; i < n; i++) {
        int indiceDeOriginal = numeros[i];
        int colOriginal = indiceDeOriginal % copia.getWidth();
        int renOriginal = indiceDeOriginal / copia.getWidth();
        int colI = i % copia.getWidth();
        int renI = i / copia.getWidth();
        copia.setRGB(colI, renI, referencia.getRGB(colOriginal, renOriginal));
      }
      publish(updateImage());
    }

    @Override
    protected BufferedImage doInBackground() throws Exception {
      if (metodo.equals("bubble"))
        bubbleSort();
      if (metodo.equals("selection"))
        selectionSort();
      if (metodo.equals("insertion"))
        insertionSort();
      if (metodo.equals("merge"))
        mergeSort();
      if (metodo.equals("quick"))
        quickSort();
      update();
      return null;
    }

    private void bubbleSort() {
      for (int i = 0; i < n - 1; i++) {
        for (int j = 0; j < n - i - 1; j++) {
          if (numeros[j] > numeros[j + 1])
            swap(j, j + 1);
        }
        if (iteracion % framerate == 0)
          update(); // Actualizamos la interfaz grafica solo si han pasado el numero de iteraciones
                    // deseadas
        iteracion = (iteracion + 1) % framerate; // Aumentamos el numero de iteraciones
      }
    }

    private void selectionSort() {
      for (int i = 0; i < numeros.length - 1; i++) {
        int m = i;
        for (int j = i + 1; j < numeros.length; j++)
          if (numeros[j] < numeros[m])
            m = j;
        swap(i, m);
        if (iteracion % framerate == 0)
          update(); // Actualizamos la interfaz grafica solo si han pasado el numero de iteraciones
                    // deseadas
        iteracion = (iteracion + 1) % framerate; // Aumentamos el numero de iteraciones
      }
    }

    private void insertionSort() {
      for (int i = 1; i < numeros.length; i++) {
        int k = numeros[i];
        int j = i - 1;
        while (j >= 0 && numeros[j] > k) {
          numeros[j + 1] = numeros[j];
          j = j - 1;
        }
        numeros[j + 1] = k;
        if (iteracion % framerate == 0)
          update(); // Actualizamos la interfaz grafica solo si han pasado el numero de iteraciones
                    // deseadas
        iteracion = (iteracion + 1) % framerate; // Aumentamos el numero de iteraciones
      }
    }

    private void mergeSort() {
      mergeSortAux(0, numeros.length - 1);
    }

    /**
     * Método Auxiliar recursivo para MergeSort
     * 
     * @param a Lo cota inferior
     * @param b La cota superior
     */
    private void mergeSortAux(int a, int b) {
      if (a >= b)
        return;
      int mid = (int) (a + b) / 2;
      mergeSortAux(a, mid);
      mergeSortAux(mid + 1, b);
      mezcla(a, mid, b);
    }

    /**
     * Método Auxiliar que junta dos listas ordenadas
     * 
     * @param a   Lo cota inferior
     * @param mid El nidice que marca la mitad del arreglo
     * @param b   La cota superior
     */
    private void mezcla(int a, int mid, int b) {
      int n1 = mid - a + 1;
      int n2 = b - mid;
      int izquierda[] = new int[n1];
      int derecha[] = new int[n2];
      for (int i = 0; i < n1; i++)
        izquierda[i] = numeros[a + i];
      for (int j = 0; j < n2; j++)
        derecha[j] = numeros[mid + j + 1];
      int i = 0, j = 0, k = a;
      while (i < n1 && j < n2) {
        if (izquierda[i] <= derecha[j]) {
          numeros[k] = izquierda[i];
          i++;
        } else {
          numeros[k] = derecha[j];
          j++;
        }
        k++;
      }
      while (i < izquierda.length) {
        numeros[k] = izquierda[i];
        i++;
        k++;
      }
      while (j < derecha.length) {
        numeros[k] = derecha[j];
        j++;
        k++;
      }
      if (iteracion % framerate == 0)
        update(); // Actualizamos la interfaz grafica solo si han pasado el numero de iteraciones
                  // deseadas
      iteracion = (iteracion + 1) % framerate; // Aumentamos el numero de iteraciones
    }

    private void quickSort() {
      quickSortAux(0, numeros.length - 1);
    }

    /**
     * Método auxiliar para quickSort,el cual es el que en realiza el algoritmo
     * QuickSort recursivo.
     * 
     * @param a Cota inferior
     * @param b Cota superior
     */
    private void quickSortAux(int a, int b) {
      if (a >= b)
        return;
      int i = a + 1;
      int j = b;
      while (i < j)
        if (numeros[i] > numeros[a] && numeros[j] <= numeros[a])
          swap(i++, j--);
        else if (numeros[i] <= numeros[a])
          i++;
        else
          j--;
      if (numeros[i] > numeros[a])
        i--;
      if (iteracion % framerate == 0)
        update(); // Actualizamos la interfaz grafica solo si han pasado el numero de iteraciones
                  // deseadas
      iteracion = (iteracion + 1) % framerate; // Aumentamos el numero de iteraciones
      swap(i, a);
      quickSortAux(a, i - 1);
      quickSortAux(i + 1, b);
    }

    public void swap(int i, int j) {
      int aux = numeros[i];
      numeros[i] = numeros[j];
      numeros[j] = aux;
    }

  }

}
