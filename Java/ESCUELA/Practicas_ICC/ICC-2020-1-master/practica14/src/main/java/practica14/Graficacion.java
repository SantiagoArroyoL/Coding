/**
* Clase que grafica una regresión lineal simple a partir de números aleatorios almacenados en un archivo CSV.
* @author Arroyo Lozano Santiago
* @version 11/11/2019 A
*/

package practica14;

import org.knowm.xchart.XYChart;
import org.knowm.xchart.XYChartBuilder;
import org.knowm.xchart.XYSeries;
import org.knowm.xchart.XYSeries.XYSeriesRenderStyle;
import org.knowm.xchart.style.Styler.LegendPosition;
import org.knowm.xchart.style.Styler.ChartTheme;
import org.knowm.xchart.style.colors.ChartColor;
import org.knowm.xchart.style.colors.XChartSeriesColors;
import org.knowm.xchart.SwingWrapper;
import practica14.LectorCSV;
import java.util.List;
import java.io.IOException;

public class Graficacion {

    public static void main(String[] args) {
        XYChart chart = new XYChartBuilder()
                            .title("Regresión lineal")
                            .width(800)
                            .height(600)
                            .xAxisTitle("X")
                            .yAxisTitle("Y")
                            .theme(ChartTheme.Matlab)
                            .build();

        chart.getStyler().setPlotBackgroundColor(ChartColor.getAWTColor(ChartColor.GREY));
        chart.getStyler().setChartTitleVisible(true);
        chart.getStyler().setLegendPosition(LegendPosition.InsideSW);
        chart.getStyler().setPlotGridLinesVisible(false);
        chart.getStyler().setMarkerSize(6);

        //Bloque try-catch
         try {
            List<String[]> listaCSV = LectorCSV.leer("src/main/resources/317150700.csv");

            int n = listaCSV.size();
            double[] xData = new double[n];
            double[] yData = new double[n];
            double m, b, sumaXY = 0, sumaX = 0, sumaY = 0, sumaXcuadrada = 0;
            int indice = 0;

            // Se toman las cadenas de cada fila, se convierten a reales y se almacenan en arreglos diferentes.
            for (String[] fila : listaCSV) {
               xData[indice] = Double.parseDouble(fila[0]);
               yData[indice] = Double.parseDouble(fila[1]);
               indice++;
            }

            double x1 = xData[0];
            double x2 = xData[n-1];

            // Sumatoria de los valores x, y, x*y y x*x
            for (int i = 0; i < n; i++) {
               sumaX += xData[i];
               sumaY += yData[i];
               sumaXY += xData[i]*yData[i];
               sumaXcuadrada += xData[i]*xData[i];
            }

            // Pendiente de la recta
            m = (n * sumaXY - sumaX * sumaY) / (n * sumaXcuadrada - Math.pow(sumaX,2));

            // Ordenada al origen
            b = (sumaY - m * sumaX) / n;

            double y1 = m * x1 + b;
            double y2 = m * x2 + b;

            XYSeries sampleSeries = chart.addSeries("Observaciones", xData, yData);
            sampleSeries.setXYSeriesRenderStyle(XYSeriesRenderStyle.Scatter);
            sampleSeries.setMarkerColor(XChartSeriesColors.RED);

            XYSeries lineSeries = chart.addSeries(
            "Línea", new double[]{x1, x2}, new double[]{y1, y2});
            lineSeries.setXYSeriesRenderStyle(XYSeriesRenderStyle.Line);
            lineSeries.setLineColor(XChartSeriesColors.BLUE);
            lineSeries.setLineWidth(3);

            new SwingWrapper<XYChart>(chart).displayChart();

         } catch(IOException ioe) {
           ioe.printStackTrace();
         }
    }//Cierre del main
}//Cierre de la clase
