# Integrantes de equipo:
#
# - Santiago Arroyo Lozano
# - Jesús Israel Gutiérrez Elizalde
# - Carlos Andrade Hernandez
# - Ricardo Adrián Luévano Ballesteros
defmodule Parte2 do
  @moduledoc """
  Modulo con las funciones de la parte 2 de la practica 04
  """

  defmodule GetBack do
    @moduledoc """
    Modulo con funciones para mandar mensajes y regresarlos.
    Calculando ademas el area de distintas figuras geometricas en funciones privadas
    """

    @doc """
    Funcion para hacer el ejercicio 1. Spawneamos n procesos de la practica 3.
    """
    def converter do
      receive do
         {sender, figure, data} ->
          send(sender, area(figure, data))
          converter()
      end
    end

    # Circulo
    defp area(:circulo, %{radio: r}) when r >= 0 do
      import :math, only: [pi: 0]
      pi() * r * r
    end

    # Rectangulo
    defp area(:rectangulo, %{base: b, altura: h}) when b >= 0 and h >= 0 do
      b * h
    end

    # Triangulo
    defp area(:triangulo, %{base: b, altura: h}) when b >= 0 and h >= 0 do
      (b * h)/2
    end

    # Trapezoide
    defp area(:trapezoide, %{base1: b1, base2: b2, altura: h}) when (b1 >= 0 and b2 >= 0) and h >= 0 do
      (b1 + b2)/2 * h
    end
  end
end
