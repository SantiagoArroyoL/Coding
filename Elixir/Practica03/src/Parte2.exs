# Integrantes de equipo:
#
# - Santiago Arroyo Lozano
# - Jesús Israel Gutiérrez Elizalde
# - Carlos Andrade Hernandez
# - Ricardo Adrián Luévano Ballesteros

defmodule Parte2 do
  @moduledoc """
  Modulo con las funciones de la parte 2 de la Practica03
  """

  @doc """
  1. Implementar split
  """
  def split([], _), do: {[],[]}
  def split(lst, num) when is_list(lst) and is_number(num) do
    splitAux(lst, 0, num, [], [])
  end

  #1.1 FUnción auxiliar que parte en dos listas los elementos de una lista, dado un entero.
  # Usamos un contador para llegar a num.
  defp splitAux([], _, _, a, b), do: {a, b}
  defp splitAux([x|xs],cont, num, a, b) do
    case cont == num do
       false -> splitAux(xs, cont+1, num, a++[x], b )
       true -> splitAux(xs, cont , num, a, b++[x])
    end
  end 

  @doc """
  2. Implementar all?/2
  """
  def all?([], _), do: false
  def all?(lst, func) when is_list(lst), do: allAux?(lst, func)

  #2.1 Función que verifica que cada elemento de una lista cumpla un predicado.
  defp allAux?([], _), do: true # Verdadero si cada elemento cumple el predicado.
  defp allAux?([x|xs], func) do
    case func.(x) do
      true -> allAux?(xs, func) 
      false -> false #Falso si un elemento no cumple el predicado.
    end
  end

  @doc """
  3. Implementar Filter recursivo.
  """
  def filter(lst, func) when is_list(lst) do
    #Llamamos a la función auxiliar para filtrar con rec de cola.
    filtrar(lst, func, []) 
  end

  # 3.1 Función auxiliar para filtrar con recursión de cola. Se evalua cada elemento de
  # la lista, y si el elemento cumple con el cuerpo de la función; se agrega a la lista final. 
  defp filtrar([], _, lstAcc), do: lstAcc # Si la lista es vacía, se regresa la lista acumuladora.
  defp filtrar([x|xs], func, lstAcc) do
    case func.(x) do
      true -> filtrar(xs, func, lstAcc ++ [x]) # Si x cumple, se agrega a la lista acumuladora.
      false -> filtrar(xs, func, lstAcc) # Si x no cumple, se ignora.
    end
  end

end
