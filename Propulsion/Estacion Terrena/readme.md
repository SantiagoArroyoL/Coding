# GUI Estación terrena para cohete de Propulsión UNAM
Código de una GUI para una estación terrena para cohetes donde se muestran los datos de diferentes sensores en tiempo real. **No se necesitan sensores para probarlo**.

### Bugs, TO-DO's
* La mayoría de las veces los elementos de texto desaparecen, los invito a resolver esto.

* El gráfico de velocidad está en desarrollo, crece hasta el infinito.

* No hay indicador de texto u otro para los despliegues de las cargas, esto derivado del primer error

___
## Librerias
El proyecto se crea con:
* numpy==1.22.4
* PyQt5==5.15.6
* PyQt5-Qt5==5.15.2
* PyQt5-sip==12.10.1
* pyqtgraph==0.12.4
* pyserial==3.5

___
## Configuracion 
Para poder ejecutarlo tienes que abrir la terminal en la carpeta y escribir:
```
$ pip3 install -r requiments.txt
$ python3 main.py
```
Esto es válido para Windows, Linux y Mac sempre y cuando tengan python instalado.
Si no tienes la electrónica aun puedes probarla! Cuando la terminal te pide que escribas un puerto serie, escribe cualquier cosa y funcionará, graficará datos aleatorios. (pero el error de texto permanece ;v).

## ¿Cómo toma las muestras?
Cada 500 ms toma una muestra, este número proviene de la tasa de datos que tiene el Arduino, **si no tiene el Arduino y los sensores, la GUI aún funciona, grafica datos aleatorios**. El bucle es:
```
timer = pg.QtCore.QTimer()
timer.timeout.connect(update)
timer.start(500)
```

### Que valores usa?
La función `update()` actualiza los gráficos y el texto de la interfaz. Lo primero que hace es obtener una lista de la información a ser actualizada, esta lista es anotada como un `value_chain`.

Luego, dentro de `update` se ejecutan los métodos *update* específicos para cada elemento que depende de esta lista.

Los valores que recibe son:

0. Tiempo de registro
1. Altura relativa
2. Temperatura
3. Presión atmosférica
4. Pitch
5. Roll
6. Yaw
7. Aceleración en X
8. Aceleración en Y
9. Aceleración en Z


### ¿Cómo almacena la información?
El manejo del CSV es con botones para evitar corromper el archivo. Es decir, se debe iniciar **manualmente** el CSV