import java.awt.AWTException;
import java.awt.GridLayout;
import java.awt.Robot;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.InputEvent;
import java.util.Random;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.SwingUtilities;

public class RobotControlTest
{
    public static void main(String[] args)
    {
        SwingUtilities.invokeLater(new Runnable()
        {
            @Override
            public void run()
            {
                createAndShowGUI();
            }
        });
    }

    private static void createAndShowGUI()
    {
        JFrame f = new JFrame();
        f.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

        final RobotControl robotControl = new RobotControl();

        f.getContentPane().setLayout(new GridLayout(1,2));

        final JButton startButton = new JButton("Start");
        f.getContentPane().add(startButton);

        final JButton stopButton = new JButton("Stop");
        stopButton.setEnabled(false);
        f.getContentPane().add(stopButton);

        startButton.addActionListener(new ActionListener()
        {
            @Override
            public void actionPerformed(ActionEvent e)
            {
                startButton.setEnabled(false);
                stopButton.setEnabled(true);
                robotControl.startClicking();
            }
        });

        stopButton.addActionListener(new ActionListener()
        {
            @Override
            public void actionPerformed(ActionEvent e)
            {
                robotControl.stopClicking();
                startButton.setEnabled(true);
                stopButton.setEnabled(false);
            }
        });

        f.pack();
        f.setLocationRelativeTo(null);
        f.setVisible(true);
    }
}

class RobotControl
{
    private final Random random = new Random();
    private final Robot robot;
    private volatile boolean running = false;

    RobotControl()
    {
        try
        {
            robot = new Robot();
        }
        catch (AWTException e)
        {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    void startClicking()
    {
        Thread thread = new Thread(new Runnable()
        {
            @Override
            public void run()
            {
                running = true;
                performClicks();
            }
        });
        thread.start();
    }

    void stopClicking()
    {
        System.out.println("Stopping");
        running = false;
    }

    private void performClicks()
    {
        System.out.println("Starting");
        while (running)
        {
            leftClick();
            System.out.println("Clicked");
        }
    }

    private void leftClick()
    {
        int no = random.nextInt(6) + 1;
        robot.mousePress(InputEvent.BUTTON1_MASK);
        robot.delay(50 * no);
        robot.mouseRelease(InputEvent.BUTTON1_MASK);
        robot.delay(220 * no);
      }
}
