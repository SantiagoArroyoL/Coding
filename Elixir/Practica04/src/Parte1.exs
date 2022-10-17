# Integrantes de equipo:
#
# - Santiago Arroyo Lozano
# - Jesús Israel Gutiérrez Elizalde
# - Carlos Andrade Hernandez
# - Ricardo Adrián Luévano Ballesteros

defmodule Parte1 do
  @moduledoc """
  Modulo con las funciones de la parte 1 de la practica 04
  """
  import Enum, only: [map: 2, all?: 2, each: 2]

  @doc """
  Funcion para spawnear n funciones de la funcion del modulo especificado pasandole
  los argumentos adecuados.
  """
  def spawn_in_list(n, modulo, func, arglist) when is_integer(n) and n > 0 do
    1..n |> map(fn _ -> (spawn(modulo, func, arglist)) end)
  end

  @doc """
  Funcion para hacer el ejercicio 1. Spawneamos n procesos de la practica 3.
  """
  def ejercicio_1(n), do: n |> spawn_in_list(Parte1, :leeMensaje, [])

  @doc """
  Funcion para mandar mensajes a todos los procesos de una lista.
  La lista debe ser una lista de PIDs.
  """
  def send_msg(list, msg) when is_list(list) do
    if all?(list, &(is_pid(&1))) do
      each(list, &(send(&1, msg)))
    else
      raise ArgumentError, message: "Argumento incorrecto la lista debe ser de PIDs"
    end
  end

  @doc """
  Funcion para mandar el mensaje {:pid, self()} a todos los procesos
  que se encuentren en la lista.
  """
  def ejercicio_2(list), do: list |> send_msg({:pid, self()})

  @doc """
  Funcion de la practica pasada para leer mensajes recibidos.
  """
  def leeMensaje() do
    import IO, only: [puts: 1]
    receive do
      {:pid, msj} -> puts("Hola #{inspect(msj)}, soy #{inspect(self())}")
      leeMensaje()
      {:ok, msj} -> puts(msj)
      leeMensaje()
      {:nok, msj} -> puts(msj <> msj)
      leeMensaje()
    end
  end
end
