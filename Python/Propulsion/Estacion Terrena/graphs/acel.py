import numpy as np
import pyqtgraph as pg

class graph_acel(pg.PlotItem):
     
    def __init__(self, parent=None, name=None, labels=None, title='Aceleraciones [m/s²]', viewBox=None, axisItems=None, enableMenu=True, **kargs):
        super().__init__(parent, name, labels, title, viewBox, axisItems, enableMenu, **kargs)
        
        self.addLegend()
        self.hideAxis('bottom')

        self.aX_plot = self.plot(pen=(102, 252, 241), name="X")
        self.aY_plot = self.plot(pen=(29, 185, 84), name="Y")
        self.aZ_plot = self.plot(pen=(203, 45, 111), name="Z")

        self.aX_data = np.linspace(0, 0)
        self.aY_data = np.linspace(0, 0)
        self.aZ_data = np.linspace(0, 0)
        self.ptr = 0


    def update(self, ax, ay, az):

        self.aX_data[:-1] = self.aX_data[1:]
        self.aY_data[:-1] = self.aY_data[1:]
        self.aZ_data[:-1] = self.aZ_data[1:]

        self.aX_data[-1] = float(ax)
        self.aY_data[-1] = float(ay)
        self.aZ_data[-1] = float(az)
        self.ptr += 1

        self.aX_plot.setData(self.aX_data)
        self.aY_plot.setData(self.aY_data)
        self.aZ_plot.setData(self.aZ_data)

        self.aX_plot.setPos(self.ptr, 0)
        self.aY_plot.setPos(self.ptr, 0)
        self.aZ_plot.setPos(self.ptr, 0)