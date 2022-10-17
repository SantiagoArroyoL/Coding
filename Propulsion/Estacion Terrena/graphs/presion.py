import pyqtgraph as pg
import numpy as np


class graph_presion(pg.PlotItem):
    
    def __init__(self, parent=None, name=None, labels=None, title='Presion', viewBox=None, axisItems=None, enableMenu=True, **kargs):
        super().__init__(parent, name, labels, title, viewBox, axisItems, enableMenu, **kargs)

        self.presion_plot = self.plot(pen=(102, 252, 241))
        self.presion_data = np.linspace(0, 0, 30)
        self.ptr = 0


    def update(self, value):
        self.presion_data[:-1] = self.presion_data[1:]
        self.presion_data[-1] = float(value)
        self.ptr += 1
        self.presion_plot.setData(self.presion_data)
        self.presion_plot.setPos(self.ptr, 0)