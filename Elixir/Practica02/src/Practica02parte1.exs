# Integrantes de equipo:
#
# - Santiago Arroyo Lozano
# - Jesús Israel Gutiérrez Elizalde
# - Carlos Andrade Hernandez
# - Ricardo Adrián Luévano Ballesteros

defmodule Practica02parte1 do
  @moduledoc """
  Modulo con las funciones de la primera parte de la Practica02
  """

  @doc """
  1. Función que dado un número n y una cadena, regresa una lista con n
  veces la cadena.
  """
  def repiteCadena(num, cadena) do
    import List, only: [duplicate: 2]
    duplicate(cadena, num)
  end

  @doc """
  2. Función que dada una lista, un índice i y un valor, regresa la lista con el valor
  insertado en el índice i de la lista.
  """
  def insertaElemento(lst, index, val)
      when is_list(lst) and is_number(index) do
    import List, only: [insert_at: 3]
    insert_at(lst, index, val)
  end

  @doc """
  3. Función que dada una lista y un índice i regresa la lista sin el elemento en la posición i.
  """
  def eliminaIndex(lst, index) when is_list(lst) and is_number(index) do
    # pop_at regresa una tupla {elemElim, listActualizada}.
    import List, only: [pop_at: 3]
    # Obtenemos solo la lista actualizada.
    elem(pop_at(lst, index, nil), 1)
  end

  @doc """
  4. Función que regresa el último elemento de una lista.
  """
  def raboLista(lst) when is_list(lst) do
    import List, only: [last: 1]
    last(lst)
  end

  @doc """
  5. Función que dada una lista de listas encapsula en tuplas los elementos
    correspondientes de cada lista
  """
  def encapsula(lst) do
    import Enum, only: [zip: 1]
    zip(lst)
  end

  @doc """
  6. Función que dado un map y una llave, regresa el map sin la entrada con la llave.
  """
  def mapBorra(map, key) do
    import Map, only: [delete: 2]
    delete(map, key)
  end

  @doc """
  7. Función que dado un map regresa su conversión a una lista.
  """
  def mapAlista(map) do
    import Map, only: [to_list: 1]
    to_list(map)
  end

  @doc """
  8. Función que calcula la distancia entre dos puntos.
  """
  def dist(a, b) when is_tuple(a) and is_tuple(b) do
    import :math, only: [sqrt: 1, pow: 2]

    sqrt(
      pow(
        elem(a, 0) - elem(b, 0),
        2
      ) +
        pow(
          elem(a, 1) - elem(b, 1),
          2
        )
    )
  end

  @doc """
  9. Función que inserta un elemento en una tupla.
  """
  def insertaTupla(t, v) when is_tuple(t) do
    import Tuple, only: [append: 2]
    append(t, v)
  end

  @doc """
  10. Función que pasa de una tupla a una lista.
  """
  def tuplaALista(t) when is_tuple(t) do
    import Tuple, only: [to_list: 1]
    to_list(t)
  end
end
