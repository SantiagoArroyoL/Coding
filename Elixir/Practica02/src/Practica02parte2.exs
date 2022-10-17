# Integrantes de equipo:
#
# - Santiago Arroyo Lozano
# - Jesús Israel Gutiérrez Elizalde
# - Carlos Andrade Hernandez
# - Ricardo Adrián Luévano Ballesteros

defmodule Practica02parte2 do
  alias Practica02parte1, as: P1

  @moduledoc """
  Modulo con las funciones de la parte 2 de la practica 2
  """

  @list1 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

  @doc """
  Funcion para obtener la lista que tenemos como atributo del modulo.
  """
  def list1(), do: @list1

  @doc """
  Función que dada una cadena, un elemento, un número n y un índice
  i < n, crea una lista con la cadena repetida "n" veces, y a esta lista, le
  agrega el elemento en el índice dado.
  """
  def func_2(cadena, valor, n, i) when is_bitstring(cadena) do
    import P1, only: [repiteCadena: 2, insertaElemento: 3]
    repiteCadena(n, cadena) |> insertaElemento(i, valor)
  end

  defmodule Ejercicio3 do
    @moduledoc """
    Modulo con las funciones del ejercicio 3 de la parte 2.
    """

    @doc """
    Función que dado un map y un índice, elimina de la lista generada
    por el map, el elemento en el índice dado.
    """
    def func_a(map, i) when is_map(map) and is_integer(i) do
      import P1, only: [mapAlista: 1, eliminaIndex: 2]
      mapAlista(map) |> eliminaIndex(i)
    end

    @doc """
    Función que dada una tupla y un valor, agrega el valor a la tupla,
    pasa la tupla a lista y finalmente regresa el último elemento de
    esta lista.
    """
    def func_b(tupla, valor) do
      import P1, only: [insertaTupla: 2, tuplaALista: 1]
      insertaTupla(tupla, valor) |> tuplaALista() |> List.last(nil)
    end
  end
end
