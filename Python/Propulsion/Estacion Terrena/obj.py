import os
import time
import csv
import random
import serial
import serial.tools.list_ports
from PyQt5.QtWidgets import QMessageBox, QInputDialog

# OBJETO ENCARGADO DE CREAR EL CSV EN LA COMPUTADORA!
class CSV():
    archivo = ""
    header = ['Tiempo', 'Altura', 'Temp', 'Presion', 'gX', 'gY', 'gZ', 'aX', 'aY', 'aZ', ]

    def __init__(self):
        self.state = False
        if not os.path.exists('./salida'):
            os.makedirs('./salida')
        # CONTAMOS NUMERO DE ARCHIVOS DE SALIDA
        dir_path = r'./salida'
        count = 0
        for path in os.listdir(dir_path):
            # si es archivo lo contamos
            if os.path.isfile(os.path.join(dir_path, path)):
                count += 1      
        self.archivo = "./salida\D"+str(count)+".csv"

    def guardar(self, data):
        if self.state == True:
            with open(self.archivo, "a") as f:
                writer = csv.writer(f, delimiter=",")
                writer.writerow(data)

    def inicia(self):
        self.state = True
        print('guardando en csv')
        with open(self.archivo, "a") as f:
                writer = csv.writer(f)
                writer.writerow(self.header)

    def termina(self):
        self.state = False
        print('csv listo!')

# COMUNICACION SERIAL!  
class Communication:
    dummyMode = False
    ser = serial.Serial()
    ports = serial.tools.list_ports.comports()

    def __init__(self, baudrate, portName):
        self.baudrate = baudrate
        self.portName = portName
        try:
            self.ser = serial.Serial(self.portName, self.baudrate)
        except serial.serialutil.SerialException:
            print("No se puede abrir : ", self.portName)
            self.dummyMode = True
            print("Dummy mode activado")

    def close(self):
        if(self.ser.isOpen()):
            self.ser.close()
        else:
            print(self.portName, " cerrado")

    def getData(self):
        if(not self.dummyMode):
            value = self.ser.readline()  # leemos solo una linea del puerto serial
            decoded_bytes = str(value[0:len(value) - 2].decode("utf-8"))
            # print(decoded_bytes) 
            value_chain = decoded_bytes.split(",")
        else: # en caso contrario generamos datos al azar
            value_chain = [0] + random.sample(range(0, 300), 1) + \
                [random.getrandbits(1)] + random.sample(range(0, 20), 8)
        return value_chain

    def isOpen(self):
        return self.ser.isOpen()


#POP UP
class PopUp:
    ports = serial.tools.list_ports.comports()
    def __init__(self, view):
        self.view = view
        #POP UP
        msg = QMessageBox()
        msg.setWindowTitle("Configurar Puerto")
        msg.setText("Por favor escribe el nombre del purto serial (ex: /dev/ttyUSB0) en el siguiente popup")
        msg.setIcon(QMessageBox.Information)
        msg.setInformativeText("Además habrá un pop-up solicitando el baudrate de comunicación.\nSelecciona mas detalles para conocer los puertos disponibles")

        cadena = "Los puertos disponibles son (si ninguno aparece escribe cualquier cosa):\n"
        for port in sorted(self.ports):
            # obtener la lista de puetos: https://stackoverflow.com/a/52809180
            cadena += "{}\n".format(port)

        msg.setDetailedText(cadena)
        x = msg.exec_()
    
    def baudrate(self):
        baudrate, don2 = QInputDialog.getText(self.view, 'Configuracion Baudrate', 'Por favor escribe en número el baudrate al que te quieres comunicar con el dispositivo:')
        return baudrate
        
    def puerto(self):
        portName, don1 = QInputDialog.getText(self.view, 'Configuracion Puerto Serial', 'Por favor escribe exactamente el puerto serial:')
        return portName


        
        
