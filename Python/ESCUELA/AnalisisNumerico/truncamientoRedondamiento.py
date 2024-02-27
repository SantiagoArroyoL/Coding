import matplotlib.pyplot as plt
import numpy as np

# Valores para la demostración
x_values = np.linspace(-3.5, 3.5, 1000)
y_trunc = np.trunc(x_values)
y_round = np.round(x_values)

# Crear la figura y los ejes
plt.figure(figsize=(12, 6))

# Gráfica para el truncamiento
plt.subplot(1, 2, 1)
plt.plot(x_values, y_trunc, label="Truncamiento", color="blue")
plt.scatter(x_values, y_trunc, color="red", s=10)
plt.title("Función fl con Truncamiento")
plt.xlabel("Números reales")
plt.ylabel("Números en punto flotante")
plt.grid(True)
plt.axhline(0, color='black',linewidth=0.5)
plt.axvline(0, color='black',linewidth=0.5)
plt.legend()

# Gráfica para el redondeo
plt.subplot(1, 2, 2)
plt.plot(x_values, y_round, label="Redondeo", color="green")
plt.scatter(x_values, y_round, color="orange", s=10)
plt.title("Función fl con Redondeo")
plt.xlabel("Números reales")
plt.ylabel("Números en punto flotante")
plt.grid(True)
plt.axhline(0, color='black',linewidth=0.5)
plt.axvline(0, color='black',linewidth=0.5)
plt.legend()

# Mostrar las gráficas
plt.tight_layout()
plt.show()
