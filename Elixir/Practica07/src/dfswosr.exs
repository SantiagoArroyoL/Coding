defmodule DFSWOSR do

  def init do
    init_state = %{ :parent => nil, :leader => -1, :children => [], :unexplored => []}
    message_receive(init_state)
  end

  def message_receive(state) do
    receive do
      msge -> {:ok, new_state} = process_message(msge, state)
      message_receive(new_state)
    end
  end

  # Asignamos id y vecinos a los procesos. Aún no despiertan.
  def process_message({:data, data}, state) do
    %{:id => id, :neighbours => ngbs} = data
    state = Map.put(state, :id, id)
    state = Map.put(state, :neighbours, ngbs)
    state = Map.put(state, :unexplored, ngbs)
    {:ok, state}
  end

  # Mensaje para comprobar el resultado final.
  def process_message({:ask_child}, state) do
    %{:id => id, :parent => pa, :children => ch} = state
    # IO.puts("Soy #{id} #{inspect self()}, mis hijos son #{inspect(child, charlists: false)}, mis vecinos son: #{inspect(ngbs, charlists: false)} y los no explorados son: #{inspect(unexp, charlists: false)}")
    IO.puts("Soy #{id} #{inspect self()}, mi padre es #{inspect pa}, y mis hijos son: #{inspect(ch, charlists: false)}")
    # IO.puts("Soy #{id} #{inspect self()} y mis vecinos son: #{inspect(ngbs, charlists: false)}")
    {:ok, state}
  end

  # Los procesos despiertan.
  # Lineas 1 a 5 del algoritmo 4.
  def process_message({:wakes, msg}, state) do
    %{:id => id} = state
    state = Map.put(state, :leader, id)
    state = Map.put(state, :parent, self())
    data = %{:message => msg, :from => self(), :id_parent => id}
    state = explore(state, data)
    {:ok, state}
  end

  # Se recibe un mensaje de algún proceso p_j
  # Lineas 6 a 14 del algoritmo 4.
  def process_message({:send, data}, state) do
    %{:message => msg, :from => from, :id_parent => id_j} = data
    # %{:leader => leader, :unexplored => unexp, :neighbours => neigh} = state
    %{:leader => leader, :neighbours => neigh} = state
    new_data = %{:message => msg, :from => self(), :id_parent => id_j}

    if leader < id_j do
      state = Map.put(state, :leader, id_j)
      state = Map.put(state, :parent, from)
      state = Map.put(state, :children, [])
      nexp  = List.delete(neigh, from)
      state = Map.put(state, :unexplored, nexp)
      state = explore(state, new_data)
      {:ok, state}
    else
      if leader == id_j do  # Ya está en el mismo árbol.
        new_data = %{:message => msg, :from => self(), :id_parent => leader}
        send(from, {:already, self(), new_data})
        {:ok, state}
      end
      {:ok, state}
      # Si leader > id_j, entonces el DFS de id_j se detiene
      # (e.d., no se hace nada más)
    end
  end

  # Se recibe mensaje <already>
  # Lineas 15 a 16 del algoritmo 4.
  def process_message({:already, _not_child, data}, state) do # DUDA
    %{:message => msg, :id_parent => id_j} = data
    %{:leader => leader} = state
    new_data = %{:message => msg, :from => self(), :id_parent => id_j}
    if id_j == leader do
      state = explore(state, new_data)
      {:ok, state}
    end
    # {:ok, state}
  end

  # Se recibe mensaje <parent>
  # Lineas 17 a 20 del algoritmo 4.
  def process_message({:parent, child_proc, data}, state) do # DUDA
    %{:id_parent => id_j} = data
    %{:children => children, :leader => leader, :id => id} = state
    flag = Enum.member?(children, child_proc) # DUDA
    if flag do
      {:ok, state}
    else
      if id_j == leader do
        IO.puts("---> El nuevo hijo de #{id} es: #{inspect child_proc}")
        children = children ++ [child_proc]
        IO.puts("---> Hijos: #{inspect(children, charlists: false)}")

        state = Map.put(state, :children, children)
        state = explore(state, data)
        {:ok, state}
      end
      # IO.puts("---> process_message({:parent...)} id_j != leader. (Soy #{id})")
      {:ok, state}
    end
  end

  # Lineas 21 a 28 del algoritmo 4.
  def explore(state, data) do
    %{:message => msg} = data
    %{:id => id, :leader => leader, :unexplored => unexp, :parent => parent} = state
    new_data = %{:message => msg, :from => self(), :id_parent => leader}

    # IO.puts("::: EXPLORE (Soy #{id}, lider #{leader}, #{inspect self()}), UNEXP: #{inspect(unexp, charlists: false)}, PARENT: #{inspect parent}")
    if unexp != [] do
      # IO.puts("::: EXPLORE unexp != []")
      [u | nexp] = unexp
      state = Map.put(state, :unexplored, nexp)
      send(u, {:send, new_data})
      state
    else
      if parent != self() do
        # IO.puts("::: EXPLORE unexp == [], parent != self(), (soy #{id}, lider #{leader}, PARENT: #{inspect parent})")
        send(parent, {:parent, self(), new_data})
        state
      else
        # IO.puts("::: EXPLORE unexp == [], parent == self(), (soy la RAIZ: #{id}, #{inspect self()})")
        state
      end
    end

  end

end

a = spawn(DFSWOSR, :init, [])
b = spawn(DFSWOSR, :init, [])
c = spawn(DFSWOSR, :init, [])
d = spawn(DFSWOSR, :init, [])
e = spawn(DFSWOSR, :init, [])
f = spawn(DFSWOSR, :init, [])
g = spawn(DFSWOSR, :init, [])
h = spawn(DFSWOSR, :init, [])

data_a = %{:id => 1, :neighbours => [b,c]}
send(a, {:data, data_a})
data_b = %{:id => 2, :neighbours => [a,c,d,e]}
send(b, {:data, data_b})
data_c = %{:id => 3, :neighbours => [a,b,f]}
send(c, {:data, data_c})
data_d = %{:id => 4, :neighbours => [b]}
send(d, {:data, data_d})
data_e = %{:id => 5, :neighbours => [b,f,g,h]}
send(e, {:data, data_e})
data_f = %{:id => 6, :neighbours => [c,e,h]}
send(f, {:data, data_f})
data_g = %{:id => 7, :neighbours => [e,h]}
send(g, {:data, data_g})
data_h = %{:id => 8, :neighbours => [e,f,g]}
send(h, {:data, data_h})

Process.sleep(1000)

all = [a,b,c,d,e,f,g,h]
Enum.each(all, &(send(&1, {:wakes, "Wakey wakey, rise and shine"})))

Process.sleep(1000)

IO.puts("\n >>>>>>>>>> Muestra del árbol >>>>>>>>> \n")

Enum.each(all, &(send(&1, {:ask_child})))
