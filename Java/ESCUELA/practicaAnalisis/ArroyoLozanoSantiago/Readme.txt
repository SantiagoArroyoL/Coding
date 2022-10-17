PRACTICA 3 ANALISIS DE ALGORITMOS
SANTIAGO ARROYO LOZANO

Instrucciones para compilar:

/***********************
  Utilizando terminal
************************/

Desde el directorio 'src':

-)  Compilar con:
      javac sort/Main.java

-)  Correr con:
      java sort.Main <archivo de resource> <velocidad> <algoritmo>

    <archivo de resource> = Nombre de archivo de imagen a procesar, debe encontrarse en la carpeta 'resource'
    <velocidad> = Numero de iteraciones que ocurrirán antes de hacer un update a la interfaz grafica
    <algoritmo> = Algoritmo de ordenamiento a utilizar, puede ser 'bubble', 'selection', 'insertion', 'merge', 'quick'

    Por ejemplo:
      java sort.Main imagen1 30 bubble
      java sort.Main imagen2 100 bubble

/***********************
  Utilizando make
************************/

-)  Para ejecutar el ejemplo:
        make
      Lo cual genera una ventana con la imagen1, framerate 30 y utilizando bubble sort

-)  Para ejecutar con parametros:
      make run p1=imagen p2=framerate p3=algoritmo
    Ejemplo:
    	make run p1=imagen2 p2=100 p3=bubble
