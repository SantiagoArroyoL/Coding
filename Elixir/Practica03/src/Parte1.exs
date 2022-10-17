# Integrantes de equipo:
#
# - Santiago Arroyo Lozano
# - Jesús Israel Gutiérrez Elizalde
# - Carlos Andrade Hernandez
# - Ricardo Adrián Luévano Ballesteros

ExUnit.start()

defmodule Parte1 do
  import Enum, only: [random: 1]
  @moduledoc """
  Modulo con las funciones de la parte 1 de la Practica03
  """
  use ExUnit.Case

  @rint1 random(0..100)
  @rint2 random(0..100)
  @rint3 random(0..100)
  @rint4 random(0..100)

  @doc """
  1. Factorial con recursión de cola.
  """
  def factorial(n) when is_integer(n) do
    if n < 0 do
      raise ArgumentError, message: ": la entrada debe ser un natural."
    else
      factorialCola(n, 1)
    end
  end
  defp factorialCola(0, acc), do: acc
  defp factorialCola(n, acc), do: factorialCola(n-1, n * acc)

  @doc """
  2. Función con recursión de cola para sacar el promedio de una lista de enteros.
  """
  def avgList(lst) when is_list(lst) do
    avgListCola(lst, 0, 0)
  end
  defp avgListCola([], suma, n), do: suma/n
  defp avgListCola([x|xs], suma, n) when is_integer(x) do
    avgListCola(xs, x + suma, n + 1)
  end

  @doc """
  3. Función con recursión de cola para seleccionar el elemento más pequeñode una lista de enteros.
  """
  def minList(lst) when is_list(lst) do
    minListCola(lst, :infinito)
  end
  defp minListCola([], min), do: min
  defp minListCola([x|xs], min) when is_number(x) do
    if x < min do
      minListCola(xs, x)
    else
      minListCola(xs, min)
    end
  end

  @doc """
  4. Función con recursión de cola para calcular la suma de Gauss.
  """
  def gauss(n) when is_integer(n) and n >= 0 do
    gaussAux(n, 0)
  end
  defp gaussAux(0, acc), do: acc
  defp gaussAux(n, acc), do: gaussAux(n - 1, acc + n)

  @doc """
  5. Función con recursión de cola para imprimir un mensaje n veces.
  """
  def imprime(n, msj) when is_integer(n) and n >= 0 and is_bitstring(msj) do
    imprimeAux(n, msj, "")
  end
  defp imprimeAux(0, _, msjAcc), do: IO.puts(msjAcc)
  defp imprimeAux(1, msj, msjAcc), do: imprimeAux(0, msj, msjAcc <> msj)
  defp imprimeAux(n, msj, msjAcc), do: imprimeAux(n - 1, msj, msjAcc <> msj <> "\n")

  test "test factorial(n)" do
    assert_raise ArgumentError, fn -> factorial(-1) end
    assert factorial(5)  == 120
    assert factorial(10) == 3628800
    IO.puts("factorial(n) ... ok ")
  end

  test "test avgList(lst)" do
    assert avgList([0,1,2,3,4])      == 2.0
    assert avgList([-1,1,-2,2,-3,3]) == 0.0
    assert avgList([12,6,8,10,4])    == 8.0
    IO.puts("avgList(lst) ... ok ")
  end

  test "test minList(lst)" do
    assert minList([0,1,2,3,4])      == 0
    assert minList([-1,1,-2,2,-3,3]) == -3
    assert minList([12,6,8,10,4])    == 4
    IO.puts("minList(lst) ... ok ")
  end

  test "test gauss(n)" do
    assert @rint1 |> gauss() == div(@rint1 * (@rint1 + 1), 2)
    assert @rint2 |> gauss() == div(@rint2 * (@rint2 + 1), 2)
    assert @rint3 |> gauss() == div(@rint3 * (@rint3 + 1), 2)
    assert @rint4 |> gauss() == div(@rint4 * (@rint4 + 1), 2)
    IO.puts("gauss(n) ... ok ")
  end

end
