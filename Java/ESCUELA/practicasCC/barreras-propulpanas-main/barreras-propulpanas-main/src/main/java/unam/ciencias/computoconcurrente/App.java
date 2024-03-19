package unam.ciencias.computoconcurrente;

import java.awt.Color;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import javax.swing.JFrame;
import javax.swing.SwingUtilities;

public class App {

  static final boolean ENABLE_KILLER = false;

  static BallWorld world = new BallWorld(ENABLE_KILLER);
  static List<Ball> balls =
      Arrays.asList(
          new Ball(world, 50, 220, 5, 10, Color.red),
          new Ball(world, 70, 180, 8, 6, Color.blue),
          new Ball(world, 150, 20, 9, 7, Color.green),
          new Ball(world, 350, 130, 3, 8, Color.black),
          new Ball(world, 115, 290, 4, 4, Color.CYAN),
          new Ball(world, 100, 250, 11, 6, Color.DARK_GRAY),
          new Ball(world, 300, 20, 4, 3, Color.MAGENTA));

  static List<Thread> threads = new ArrayList<>();

  public static void main(String[] a) {
    initGraphicalContext();
    runSimulation();
  }

  private static void initGraphicalContext() {
    JFrame window = new JFrame();
    SwingUtilities.invokeLater(
        () -> {
          window.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
          window.getContentPane().add(world);
          window.pack();
          window.setVisible(true);
        });
  }

  private static void runSimulation() {
    for (Ball b : balls) {
      threads.add(new Thread(b::keepMoving, String.format("Color %s", b.getColor())));
    }
    for (Thread t : threads) {
      t.start();
    }
  }
}
