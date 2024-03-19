# Reporte

## Integrantes del equipo
Santiago Arroyo Lozano - santiagoarroyo@ciencias,unam.mx <br>
Rodrigo Liprandi Cortes - godites@ciencias.unam.mx

## Problema 1. Suma de Matrices
Para la prueba de additionSqrtFile3. Tenemos: 
<table>
    <tr>
        <th>Número de hilos</th>
        <th>Aceleración teórica</th>
        <th>Aceleración obtenida</th>
        <th>Porcentaje de código paralelo</th>
    </tr>
    <tr>
        <td>1</td>
        <td>1</td>
        <td>1</td>
        <td>99%</td>
    </tr>
    <tr>
        <td>2</td>
        <td>1.98x</td>
        <td>1.65x</td>
        <td>99%</td>
    </tr>
    <tr>
        <td>4</td>
        <td>3.8x</td>
        <td>1.73x</td>
        <td>99%</td>
    </tr>
    <tr>
        <td>8</td>
        <td>7.4x</td>
        <td>1.9x</td>
        <td>99%</td>
    </tr>
</table>
Vemos que, sí hay una mejora al usar más hilos, aunque no son resultados tan buenos a como nos dice la ley de Amdahl.
La tendencia se reproduce en los diferentes tamaños de entradas
![Grafica de barras hilos vs segs](/images/Figure_1.png)

## Problema 2. Multiplicación de Matrices
Para el problema de matrices
<table>
    <tr>
        <th>Número de hilos</th>
        <th>Aceleración teórica</th>
        <th>Aceleración obtenida</th>
        <th>Porcentaje de código paralelo</th>
    </tr>
    <tr>
        <td>1</td>
        <td>1</td>
        <td>1x</td>
        <td>99%</td>
    </tr>
    <tr>
        <td>2</td>
        <td>1.98x</td>
        <td>1.6x</td>
        <td>99%</td>
    </tr>
    <tr>
        <td>4</td>
        <td>3.8x</td>
        <td>0.2x</td>
        <td>99%</td>
    </tr>
    <tr>
        <td>8</td>
        <td>7.4x</td>
        <td>0.10x</td>
        <td>99%</td>
    </tr>
</table>
![Grafica de barras hilos vs segs](/images/Figure_2.png)

## Problema 3. Blur Gaussiano
<table>
    <tr>
        <th>Número de hilos</th>
        <th>Aceleración teórica</th>
        <th>Aceleración obtenida</th>
        <th>Porcentaje de código paralelo</th>
    </tr>
    <tr>
        <td>1</td>
        <td>1</td>
        <td>1</td>
        <td>98%</td>
    </tr>
    <tr>
        <td>2</td>
        <td>2</td>
        <td>1.9672341235315098</td>
        <td>98%</td>
    </tr>
    <tr>
        <td>4</td>
        <td>4</td>
        <td>3.9925026960582684</td>
        <td>99%</td>
    </tr>
    <tr>
        <td>8</td>
        <td>8</td>
        <td>7.658369211898486</td>
        <td>99%</td>
    </tr>
</table>
![Grafica de barras hilos vs segs](/images/Figure_3.png)
