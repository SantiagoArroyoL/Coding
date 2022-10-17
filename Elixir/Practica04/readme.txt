Practica04

INTEGRANTES

- Santiago Arroyo Lozano
- Jesús Israel Gutiérrez Elizalde
- Carlos Andrade Hernandez
- Ricardo Adrián Luévano Ballesteros

La practica se desarrolló como siempre con amor.
Nos dividimos las partes y al final revisamos el trabajo de todos

Parte1:

    Hay varias formas de realizar lo especificado, como siempre
    primero compilamos el archivo:

    $ iex src/Parte1.exs

    Creamos una lista con los procesos de la practica pasada.
    y les mandamos el mensaje.

    iex> procesos = Parte1.ejercicio_1(5)
    iex> Parte1.ejercicio_2(procesos)

    Otra forma utilizando funciones las funciones mas generales que hicimos:

    iex> procesos1 = Parte1.spawn_in_list(5, Parte1, :leeMensaje, [])
    iex> Parte1.send_msg(procesos1, {:pid, self()}) 

Parte2:

    El código se prueba (por ejemplo) con 
    pid = spawn(Parte2.GetBack, :converter, [])
    send(pid, {self(), :rectangulo, %{:base => 3, :altura => 2}})

    Los datos pedidos por figura geométrica son:
        CIRCULO:    :radio
        TRIANGULO:  :base,  :altura
        RECTANGULO: :base,  :altura
        TRAPEZOIDE: :base1, :base2, :altura


Parte3:

    El código no recibe datos de entrada, utiliza los eventos del ejemplo e imprime la agenda óptima. Sólo basta, desde src/, ejecutar:

    python Parte3.py
