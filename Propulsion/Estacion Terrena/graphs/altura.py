import pyqtgraph as pg
import numpy as np

class graph_altura(pg.PlotItem):

    def __init__(self, parent=None, name=None, labels=None, title='Altura [m]', viewBox=None, axisItems=None, enableMenu=True, **kargs):
        super().__init__(parent, name, labels, title, viewBox, axisItems, enableMenu, **kargs)
        self.altura_plot = self.plot(pen=(29, 185, 84), symbol='x')
        self.altura_data = np.linspace(0, 0, 30)
        self.ptr1 = 0

    def update(self, value):
        self.altura_data[:-1] = self.altura_data[1:]
        self.altura_data[-1] = float(value)
        self.ptr1 += 1
        self.altura_plot.setData(self.altura_data)
        self.altura_plot.setPos(self.ptr1, 0)