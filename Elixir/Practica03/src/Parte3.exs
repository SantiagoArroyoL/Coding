# Integrantes de equipo:
#
# - Santiago Arroyo Lozano
# - Jesús Israel Gutiérrez Elizalde
# - Carlos Andrade Hernandez
# - Ricardo Adrián Luévano Ballesteros

defmodule Parte3 do
  @moduledoc """
  Modulo con las funciones de la parte 3 de la Practica03
  """

  @doc """
  Crea una función para leer los mensajes recibidos
      Hacemos inspect del mensaje para segurar que sin importar el tipo que sea, este se pueda imprimir.
      Ademas aseguramos que :pid solo pueda recibir otro pid
  """
  def leeMensaje() do
    import IO, only: [puts: 1]
    receive do
      {:pid, msj} -> puts("Hola #{inspect(msj)}, soy #{inspect(self())}")
      {:ok,  msj} -> puts(msj)
      {:nok, msj} -> puts(msj <> msj)
    end
  end
end
