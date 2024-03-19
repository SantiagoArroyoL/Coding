package unam.ciencias.computoconcurrente;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.util.ArrayList;
import java.util.List;
import javax.swing.JPanel;

public class BallWorld extends JPanel {
  private static final int WIDTH = 400;
  private static final int HEIGHT = 400;
  private static final Color BG_COLOR = Color.white;

  private final List<Ball> balls;

  public BallWorld(boolean killerEnabled) {
    setPreferredSize(new Dimension(WIDTH, HEIGHT));
    setOpaque(true);
    setBackground(BG_COLOR);
    this.balls = new ArrayList<>();
  }

  public void addBall(Ball b) {
    balls.add(b);
  }

  @Override
  public void paintComponent(Graphics g) {
    super.paintComponent(g);
    synchronized (this) {
      balls.forEach(b -> b.draw(g));
    }
  }
}
