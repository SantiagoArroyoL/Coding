# Integrantes de equipo:
#
# - Santiago Arroyo Lozano
# - Jesús Israel Gutiérrez Elizalde
# - Carlos Andrade Hernandez
# - Ricardo Adrián Luévano Ballesteros

ExUnit.start() # framework para pruebas unitarias en elixir

defmodule Practica01 do
  @moduledoc """
  Modulo con las funciones de la practica01
  """
  use ExUnit.Case # usamos el framework

  @doc """
  1. Función que calcula el cuadruple de un numero (Dos veces el doble)
  """
  def cuadruple(num) when is_number(num) do
    (num * 2) * 2
  end

  @doc """
  2. Función que calcula el sucesor de un número.
  """
  def sucesor(num) when is_number(num) do
    num + 1
  end

  @doc """
  3. Función que regresa el máximo de dos números.
  """
  def maximo(num1, num2) when is_number(num1) and is_number(num2) do
    if num1 >= num2 do
      num1
    else
      num2
    end
  end

  @doc """
  4 Función que calcula el máximo de dos números.
  """
  def suma(num1, num2) when is_number(num1) and is_number(num2) do
    num1 + num2
  end

  @doc """
  5. Función que calcula la resta de dos números.
  """
  def resta(a, b) when is_number(a) and is_number(b), do: a-b

  @doc """
  6. Función que calcula la multiplicación de conjugados
  """
  def multiplicacionConjugados(a, b) when is_number(a) and is_number(b), do: (a-b)*(a+b)

  @doc """
  7. Función que calcula la negación de un valor booleano.
  """
  def negacion(bool) when is_boolean(bool), do: !bool


  @doc """
  8. Funcion para calcular la conjuncion de dos valores booleanos.
  """
  def conjuncion(bool1, bool2) when is_boolean(bool1) and is_boolean(bool2) do
    bool1 and bool2
  end

  @doc """
  9. Funcion para calcular la disyuncion de dos valores booleanos.
  """
  def disyuncion(bool1, bool2) when is_boolean(bool1) and is_boolean(bool2) do
    bool1 or bool2
  end

  @doc """
  10. Funcion que calcula el valor absoluto de un numero.
  """
  def absoluto(num) when is_number(num) do
    if num < 0 do
      -num
    else
      num
    end
  end

  @doc """
  11. Función que calcula el área de un círculo dado su radio.
  """
  def areaCirculo(r) when is_number(r) do
    3.14 * r ** 2
  end

  @doc """
  12. a) Función recursiva que calcula la suma de Gauss
  """
  def sumaGaussRec(1) do
    1
  end
  def sumaGaussRec(n) when is_number(n) do
    n + sumaGaussRec(n - 1)
  end

  @doc """
  12. b) Fórmula para calcular la suma de Gauss.
  """
  def sumaGauss(n) when is_number(n) do
    div(n * (n + 1), 2)
  end

  @doc """
  13. Función que calcula el área de un triángulo dados tres puntos.
  """
  def areaTriangulo(a, b, c) when is_tuple(a) and
                                  is_tuple(b) and
                                  is_tuple(c) do
    absoluto(
      prodPunto(
        normal(vector(a, b)),
        vector(a, c))) / 2
  end

  @doc """
  13a. Función auxiliar que calcula el vector de dos puntos.
  """
  def vector(a, b) when is_tuple(a) and
                        is_tuple(b) do
    {elem(b, 0) - elem(a, 0), elem(b, 1) - elem(a, 1)}
  end

  @doc """
  13b. Función auxiliar que calcula la normal de un vector.
  """
  def normal(a) when is_tuple(a) do
    {elem(a, 1), -1 * elem(a, 0)}
  end

  @doc """
  13c. Función auxiliar que calcula el producto punto de dos puntos.
  """
  def prodPunto(a, b) when  is_tuple(a) and
                            is_tuple(b) do
    elem(a, 0) * elem(b, 0) + elem(a, 1) * elem(b, 1)
  end

  # ----------- Pruebas -----------
  test "pruebaCuadruple" do
    IO.puts " -> Probando cuadruple(num)"
    num = Enum.random(-1000..1000)
    assert cuadruple(num) == 4 * num
  end

  test "pruebaSucesor" do
    IO.puts " -> Probando sucesor(num)"
    num = Enum.random(-1000..1000)
    assert sucesor(num) == num + 1
  end

  test "pruebaMaximo" do
    IO.puts " -> Probando máximo(num1, num2)"
    assert maximo(5, 6) == 6
    assert maximo(7,6) == 7
    assert maximo(4,4) == 4
  end

  test "pruebaSuma" do
    IO.puts " -> Probando suma(num1, num2)"
    assert suma(5, 6) == 11
    assert suma(7,6) == 13
    assert suma(4,4) == 8
  end

  test "pruebaResta" do
    IO.puts " -> Probando resta(a, b)"
    assert resta(5, 3) == 2
    assert resta(7,6) == 1
    assert resta(4,4) == 0
  end

  test "pruebaMultiplicacionConjugada" do
    IO.puts " -> Probando multipliacionConjugados(a, b)"
    assert multiplicacionConjugados(5, 3) == 16
    assert multiplicacionConjugados(7,6) == 13
    assert multiplicacionConjugados(4,4) == 0
  end

  test "pruebaNegacion" do
    IO.puts " -> Probando negacion(bool)"
    assert negacion(true) == false
    assert negacion(false) == true
  end

  test "pruebaConjucion" do
    IO.puts " -> Probando conjuncion(bool1, bool2)"
    assert conjuncion(true, true) == true
    assert conjuncion(false, true) == false
    assert conjuncion(true, false) == false
    assert conjuncion(false, false) == false
  end

  test "pruebaDisyuncion" do
    IO.puts " -> Probando disyuncion(bool1, bool2)"
    assert disyuncion(true, true) == true
    assert disyuncion(false, true) == true
    assert disyuncion(true, false) == true
    assert disyuncion(false, false) == false
  end

  test "pruebaAbsoluto" do
    IO.puts " -> Probando absoluto(num)"
    assert absoluto(Enum.random(-1000..0)) >= 0
    assert absoluto(Enum.random(0..1000)) >= 0
  end

  test "pruebaAreaCirculo" do
    IO.puts " -> Probando areaCirculo(r)"
    assert areaCirculo(1) == 3.14
    assert areaCirculo(2) == 12.56
  end

  test "pruebaSumaGaussRecursiva" do
    IO.puts " -> Probando sumaGaussRec(n)"
    assert sumaGaussRec(10) == 55
    assert sumaGaussRec(15) == 120
  end

  test "pruebaSumaGauss" do
    IO.puts " -> Probando sumaGauss(n)"
    assert sumaGauss(10) == 55
    assert sumaGauss(15) == 120
  end

  test "pruebaAreaTriangulo" do
    IO.puts " -> Probando areaTriangulo(a, b, c)"
    assert areaTriangulo({2,0}, {3,4}, {-2,5}) == 10.5
    assert areaTriangulo({3,4}, {4,7}, {6,-3}) == 8
  end

end
