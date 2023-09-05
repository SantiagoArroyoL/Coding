"""
Estacion Terrena de Propulsion UNAM
@author Santiago Arroyo
"""
import sys
from obj import Communication, CSV, PopUp
#PyQt
import pyqtgraph as pg
import serial.tools.list_ports
from pyqtgraph.Qt import QtGui, QtCore, QtWidgets
#Graficas y texto
from graphs.vel import graph_vel
from graphs.temp import graph_temp
from graphs.acel import graph_acel
from graphs.gyro import graph_gyro
from graphs.caida import graph_caida
from graphs.altura import graph_altura
from graphs.tiempo import graph_tiempo
from graphs.bateria import graph_bateria
from graphs.presion import graph_presion

# Configuracion ventana
pg.setConfigOption('background', (33, 33, 33))
pg.setConfigOption('foreground', (197, 198, 199))
app = QtWidgets.QApplication(sys.argv)
view = pg.GraphicsView()
Layout = pg.GraphicsLayout()
view.setCentralItem(Layout)
view.show()
view.setWindowTitle('Estacion Terrena')
view.resize(1200, 700)

# Objetos propios
pop_up = PopUp(view)
ser = Communication(pop_up.baudrate(), "COM15")
CSV = CSV()

# Estilos y fuentes
font = QtGui.QFont()
font.setPixelSize(90)
style = "background-color:rgb(29, 185, 84);color:rgb(0,0,0);font-size:14px;"

#Iniciamos los objetos graph para cada grafica
vel = graph_vel()
acel = graph_acel()
gyro = graph_gyro()
temp = graph_temp()
altura = graph_altura()
presion = graph_presion()
caida = graph_caida(font=font)
tiempo = graph_tiempo(font=font)
bateria = graph_bateria(font=font)

# Boton 1
proxy = QtWidgets.QGraphicsProxyWidget()
inicia_csv = QtWidgets.QPushButton('Inicia escritura CSV')
inicia_csv.setStyleSheet(style)
inicia_csv.clicked.connect(CSV.inicia)
proxy.setWidget(inicia_csv)

# Boton 2
proxy2 = QtWidgets.QGraphicsProxyWidget()
termina_csv = QtWidgets.QPushButton('Deten escritura CSV')
termina_csv.setStyleSheet(style)
termina_csv.clicked.connect(CSV.termina)
proxy2.setWidget(termina_csv)


## DEBEMOS PONER MANUALMENTE TODO EN EL LAYOUT

# Titulo
text = """
Estacion terrena para monitorrear datos de vuelo de cohete desarrollado por Propulsion UNAM .
"""
Layout.addLabel(text, colspan=21)
Layout.nextRow()

lb = Layout.addLayout(colspan=21)
lb.addItem(proxy)
lb.nextCol()
lb.addItem(proxy2)

Layout.nextRow()

l1 = Layout.addLayout(colspan=20, rowspan=2)
l11 = l1.addLayout(rowspan=1, border=(83, 83, 83))

# altura, vel
l11.addItem(altura)
l11.addItem(vel)
l1.nextRow()

# acel, gyro, presion, temp
l12 = l1.addLayout(rowspan=1, border=(83, 83, 83))
l12.addItem(acel)
l12.addItem(gyro)
l12.addItem(presion)
l12.addItem(temp)

# graphs de texto
# COMENTADO PORQUE SIRVE CUANDO QUIERE
# l2 = Layout.addLayout(rowspan=2, border=(200, 150, 83))
# l2.addItem(tiempo)
# l2.nextRow()
# l2.addItem(bateria)
# l2.nextRow()
# l2.addItem(caida)
# l2.nextRow()
# l2.addItem(caida)

#Funcion que sera llamada por el timer
def update():
    try:
        value_chain = []
        value_chain = ser.getData()
        tiempo.update(value_chain[0])
        altura.update(value_chain[1])
        print("RSSI:", value_chain[2])
        # temp.update(value_chain[2])
        # presion.update(value_chain[3])
        # gyro.update(value_chain[4], value_chain[5], value_chain[6])
        # vel.update(value_chain[7], value_chain[8], value_chain[9])
        # acel.update(value_chain[2], value_chain[3], value_chain[4])
        CSV.guardar(value_chain)
    except IndexError:
        print('perate mano, no funcionaaaa')

######## TIMER
# Cada 500ms actualizamos la ventana
if(ser.isOpen() or ser.dummyMode):
    timer = pg.QtCore.QTimer()
    timer.timeout.connect(update)
    timer.start(500)
else:
    print("algo salio mal al actualizar")
     
# Iniciamos Qt event loop a menos de estar en interactive mode
if __name__ == '__main__':
    if (sys.flags.interactive != 1) or not hasattr(QtCore, 'PYQT_VERSION'):
        QtWidgets.QApplication.instance().exec_()
