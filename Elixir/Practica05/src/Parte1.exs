# Integrantes de equipo:
#
# - Santiago Arroyo Lozano
# - Jesús Israel Gutiérrez Elizalde
# - Carlos Andrade Hernandez
# - Ricardo Adrián Luévano Ballesteros

defmodule Graphs do

  def inicia do
    estado_inicial = %{:procesado => false, :raiz => false}
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

  def procesa_mensaje({:inicia}, estado) do
    estado = conexion(estado)
    {:ok, estado}
  end

  def procesa_mensaje({:raiz}, estado) do
    estado = Map.put(estado, :raiz, true)
    {:ok, estado}
  end

  def procesa_mensaje({:mensaje, n_id}, estado) do
    estado = conexion(estado, n_id)
    {:ok, estado}
  end

  def procesa_mensaje({:ya}, estado) do
    %{:id => id, :procesado => procesado} = estado
    if procesado do
      IO.puts "Soy el proceso #{id} y ya me visitaron"
    else
      IO.puts "Soy el proceso #{id} y NO me visitaron :( La grafican no es conexa"
    end
    {:ok, estado}
  end

  def conexion(estado, n_id \\ nil) do
    %{:id => id, :vecinos => vecinos, :procesado => procesado, :raiz => raiz} = estado
    if raiz and (not procesado) do
      IO.puts "Soy el proceso inicial(#{id}) y mi papá es #{n_id}"
      Enum.map(vecinos, fn vecino -> send vecino, {:mensaje, id} end)
      Map.put(estado, :procesado, true)
    else
      if n_id != nil and (not procesado) do
        IO.puts "Soy el proceso #{id} y mi papá es #{(n_id)}"
        Enum.map(vecinos, fn vecino -> send vecino, {:mensaje, id} end)
        Map.put(estado, :procesado, true)
      else
        estado
      end
    end
  end

end

a = spawn(Graphs, :inicia, [])
b = spawn(Graphs, :inicia, [])
c = spawn(Graphs, :inicia, [])
d = spawn(Graphs, :inicia, [])
e = spawn(Graphs, :inicia, [])
f = spawn(Graphs, :inicia, [])

send(a, {:id, 1})
send(b, {:id, 2})
send(c, {:id, 3})
send(d, {:id, 4})
send(e, {:id, 5})
send(f, {:id, 6})

send(a, {:vecinos, [b,c,f]})
send(b, {:vecinos, [a,c,e]})
send(c, {:vecinos, [a,b,d]})
send(d, {:vecinos, [c,e,f]})
send(e, {:vecinos, [b,d,f]})
send(f, {:vecinos, [a,d,e]})

send(a, {:raiz})

send(a, {:inicia})
send(b, {:inicia})
send(c, {:inicia})
send(d, {:inicia})
send(e, {:inicia})
send(f, {:inicia})

Process.sleep(500)

IO.puts("\nVerificando conexidad primera grafica (la que nos dio emi)")

send(a, {:ya})
send(b, {:ya})
send(c, {:ya})
send(d, {:ya})
send(e, {:ya})
send(f, {:ya})

Process.sleep(500)
IO.puts("\n\n--------------------------------------------------\n\n")
#Carlos parte
# Vértices
z = spawn(Graphs, :inicia, [])
y = spawn(Graphs, :inicia, [])
x = spawn(Graphs, :inicia, [])
w = spawn(Graphs, :inicia, [])
v = spawn(Graphs, :inicia, [])
u = spawn(Graphs, :inicia, [])
t = spawn(Graphs, :inicia, [])
s = spawn(Graphs, :inicia, [])
r = spawn(Graphs, :inicia, [])
q = spawn(Graphs, :inicia, [])
# id's de los vértices
send(z, {:id, 26})
send(y, {:id, 25})
send(x, {:id, 24})
send(w, {:id, 23})
send(v, {:id, 22})
send(u, {:id, 21})
send(t, {:id, 20})
send(s, {:id, 19})
send(r, {:id, 18})
send(q, {:id, 17})
# Vecinos de cada vértice
send(z, {:vecinos, [y]})
send(y, {:vecinos, [z,u,x]})
send(x, {:vecinos, [y,v,w,t]})
send(w, {:vecinos, [x,t]})
send(v, {:vecinos, [x]})
send(u, {:vecinos, [y]})
send(t, {:vecinos, [x,w]})
send(s, {:vecinos, [r,q]})
send(r, {:vecinos, [s]})
send(q, {:vecinos, [s]})
# Raiz de la gráfica
send(x, {:raiz})

send(z, {:inicia})
send(y, {:inicia})
send(x, {:inicia})
send(w, {:inicia})
send(v, {:inicia})
send(u, {:inicia})
send(t, {:inicia})
send(s, {:inicia})
send(r, {:inicia})
send(q, {:inicia})


Process.sleep(500)
IO.puts("\nVerificando conexidad segunda grafica\n")

send(q, {:ya})
send(r, {:ya})
send(s, {:ya})
send(t, {:ya})
send(u, {:ya})
send(v, {:ya})
send(w, {:ya})
send(x, {:ya})
send(y, {:ya})
send(z, {:ya})
