# Integrantes de equipo:
#
# - Santiago Arroyo Lozano
# - Jesús Israel Gutiérrez Elizalde
# - Carlos Andrade Hernandez
# - Ricardo Adrián Luévano Ballesteros

defmodule Broadcast do

  def inicia do
    estado_inicial = %{:procesado => false}
    recibe_mensaje(estado_inicial)
  end

  def recibe_mensaje(estado) do
    receive do
      mensaje -> {:ok, nuevo_estado} = procesa_mensaje(mensaje, estado)
      recibe_mensaje(nuevo_estado)
    end
  end

  def procesa_mensaje({:id, id}, estado) do
    estado = Map.put(estado, :id, id)
    {:ok, estado}
  end

  def procesa_mensaje({:vecinos, vecinos}, estado) do
    estado = Map.put(estado, :vecinos, vecinos)
    {:ok, estado}
  end

  def procesa_mensaje({:mensaje, mensaje, id_p}, estado) do
    estado = transmite(estado, mensaje, id_p)
    {:ok, estado}
  end

  def transmite(estado, mensaje, id_p) do
    %{:id => i, :vecinos => vs, :procesado => p} = estado

    if id_p == nil do
      IO.puts "Soy la raíz con id(#{i}) y mando el mensaje <#{mensaje}>"
      Enum.map(vs, &(send(&1, {:mensaje, mensaje, i})))
      Map.put(estado, :procesado, true)
    else
      if (not p) do
        IO.puts "Soy el id(#{i}) y mi padre(#{id_p}) me pasó el mensaje <#{mensaje}>"
        Enum.map(vs, &(send(&1, {:mensaje, mensaje, i})))
        Map.put(estado, :procesado, true)
      else
        estado
      end
    end
  end

end

a = spawn(Broadcast, :inicia, [])
b = spawn(Broadcast, :inicia, [])
c = spawn(Broadcast, :inicia, [])
d = spawn(Broadcast, :inicia, [])
e = spawn(Broadcast, :inicia, [])
f = spawn(Broadcast, :inicia, [])
g = spawn(Broadcast, :inicia, [])
h = spawn(Broadcast, :inicia, [])
i = spawn(Broadcast, :inicia, [])
j = spawn(Broadcast, :inicia, [])
k = spawn(Broadcast, :inicia, [])
l = spawn(Broadcast, :inicia, [])
m = spawn(Broadcast, :inicia, [])

vertices = [a,b,c,d,e,f,g,h,i,j,k,l,m]
tuplest_vert = Enum.zip(1..13, vertices)

Enum.map(tuplest_vert, &(send(elem(&1, 1), {:id, elem(&1, 0)})))

send(a, {:vecinos, [b,c,e,i]})
send(b, {:vecinos, [a,g,f]})
send(c, {:vecinos, [a]})
send(d, {:vecinos, [j]})
send(e, {:vecinos, [a,k]})
send(f, {:vecinos, [b,h]})
send(g, {:vecinos, [b]})
send(h, {:vecinos, [f]})
send(i, {:vecinos, [a,j]})
send(j, {:vecinos, [d,i,m]})
send(k, {:vecinos, [e,l]})
send(l, {:vecinos, [k]})
send(m, {:vecinos, [j]})

send(a, {:mensaje, "Ola k ase", nil})

defmodule Convergecast do

  def inicia do
    estado_inicial = %{:raiz => false, :padre => nil, :candidatos => []}
    recibe_mensaje(estado_inicial)
  end

  def recibe_mensaje(estado) do
    receive do
      mensaje -> {:ok, nuevo_estado} = procesa_mensaje(mensaje, estado)
      recibe_mensaje(nuevo_estado)
    end
  end

  def procesa_mensaje({:id, id}, estado) do
    estado = Map.put(estado, :id, id)
    {:ok, estado}
  end

  def procesa_mensaje({:vecinos, vecinos}, estado) do
    estado = Map.put(estado, :vecinos, vecinos)
    {:ok, estado}
  end

  def procesa_mensaje({:padre, padre}, estado) do
    estado = Map.put(estado, :padre, padre)
    {:ok, estado}
  end

  def procesa_mensaje({:respuestas}, estado) do
    estado = Map.put(estado, :respuestas, 0)
    {:ok, estado}
  end

  def procesa_mensaje({:raiz}, estado) do
    estado = Map.put(estado, :raiz, true)
    {:ok, estado}
  end

  def procesa_mensaje({:inicia, mensaje_num}, estado) do
    estado = convergecast_suma(estado, mensaje_num)
    {:ok, estado}
  end

  def procesa_mensaje({:mensaje, mensaje}, estado) do
    %{:id => id, :respuestas => resp, :vecinos => vecinos, :candidatos => candidatos, :raiz => raiz} = estado
    estado = Map.put(estado, :respuestas, resp+1)
    estado = Map.put(estado, :candidatos, candidatos ++ [mensaje])
    {:ok, estado}

    if raiz do
      flag_l = (length vecinos)
      flag_r = resp + 1
      "Soy la raíz(#{id}) y alguien me pasó un número <#{mensaje}>\t\t[#{flag_r}/#{flag_l}]"
    else
      flag_l = (length vecinos) - 1
      flag_r = resp + 1
      "Soy (#{id}) y alguien me pasó un número <#{mensaje}>\t\t\t[#{flag_r}/#{flag_l}]"
    end
    estado = convergecast_suma(estado, 0)
    {:ok, estado}
  end

  def convergecast_suma(estado, mensaje_num) do
    %{:id => id, :vecinos => vecinos, :raiz => raiz,
    :respuestas => resp, :padre => daddy, :candidatos => candidatos} = estado
    if raiz do
      if (resp == (length vecinos)) do
        suma = Enum.reduce(candidatos, mensaje_num, fn x, y -> x+y end)
        IO.puts("<<La suma del spanning tree es #{suma}>>")
        estado = Map.put(estado, :result, suma)
        estado
      end
      estado
    else
      if (resp == (length vecinos) - 1) do
        suma = Enum.reduce(candidatos, mensaje_num, fn x, y -> x+y end)
        IO.puts("No soy la raíz(#{id}) y los números son: #{inspect(candidatos, charlists: false)}\nY mi papá(#{inspect daddy}) recibirá #{suma}")
        send(daddy, {:mensaje, suma})
      else
        estado
      end
    end
  end

end

IO.puts("\n\n") #Para crear espacio con Broadcaast

#Spawneamos, creamos y enumeramos
a = spawn(Convergecast, :inicia, [])
b = spawn(Convergecast, :inicia, [])
c = spawn(Convergecast, :inicia, [])
d = spawn(Convergecast, :inicia, [])
e = spawn(Convergecast, :inicia, [])
f = spawn(Convergecast, :inicia, [])
g = spawn(Convergecast, :inicia, [])
h = spawn(Convergecast, :inicia, [])
i = spawn(Convergecast, :inicia, [])
j = spawn(Convergecast, :inicia, [])
k = spawn(Convergecast, :inicia, [])
l = spawn(Convergecast, :inicia, [])
m = spawn(Convergecast, :inicia, [])

vertices = [a,b,c,d,e,f,g,h,i,j,k,l,m]
tuplest_vert = Enum.zip(1..13, vertices)

Enum.map(tuplest_vert, &(send(elem(&1, 1), {:id, elem(&1, 0)})))

#Vecinos
send(a, {:vecinos, [b,c,m]})
send(b, {:vecinos, [a,d]})
send(c, {:vecinos, [a,e,f]})
send(d, {:vecinos, [b,k,l]})
send(e, {:vecinos, [c]})
send(f, {:vecinos, [c,g,h]})
send(g, {:vecinos, [f]})
send(h, {:vecinos, [f,i,j]})
send(i, {:vecinos, [h]})
send(j, {:vecinos, [h]})
send(k, {:vecinos, [d]})
send(l, {:vecinos, [d]})
send(m, {:vecinos, [a]})

Enum.map(vertices, &(send(&1, {:respuestas})))

# Definimos padres
send(b, {:padre, a})
send(c, {:padre, a})
send(d, {:padre, b})
send(e, {:padre, c})
send(f, {:padre, c})
send(g, {:padre, f})
send(h, {:padre, f})
send(i, {:padre, h})
send(j, {:padre, h})
send(k, {:padre, d})
send(l, {:padre, d})
send(m, {:padre, a})

#Raiz
send(a, {:raiz})

#Hojas
send(e, {:inicia, 1})
send(g, {:inicia, 1})
send(i, {:inicia, 1})
send(j, {:inicia, 1})
send(k, {:inicia, 1})
send(l, {:inicia, 1})
send(m, {:inicia, 1})
