# Integrantes de equipo:
#
# - Santiago Arroyo Lozano
# - Jesús Israel Gutiérrez Elizalde
# - Carlos Andrade Hernandez
# - Ricardo Adrián Luévano Ballesteros

defmodule Generales do
  @moduledoc """
  Modulo con las funciones de la parte 1 de la practica 04
  """

  @doc """
  Funcion generales para recibir y mandar mensajes conforme
  al algoritmo generales.
  """
  def generales(es_lider \\ false, otro \\ nil, hora \\ 0)
      when is_boolean(es_lider) and is_number(hora) do

    if es_lider do
      send(otro, {self(), hora})
      receive do
        :ok ->
          IO.puts("Comenzamos a atacar a las #{hora}")
      end

    else
      receive do
        {lider, hora} ->
          IO.puts("Recibi mensaje: Atacamos a las #{hora}")
          send(lider, :ok)
      end
    end

  end

end

## ejecucion
b = spawn(Generales, :generales, [false])
spawn(Generales, :generales, [true, b, 12])
