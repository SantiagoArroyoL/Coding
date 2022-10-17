import pyqtgraph as pg


class graph_tiempo(pg.PlotItem):
        
    def __init__(self, parent=None, name=None, labels=None, title='Tiempo [min]', viewBox=None, axisItems=None, enableMenu=True, font = None,**kargs):
        super().__init__(parent, name, labels, title, viewBox, axisItems, enableMenu, **kargs)

        self.hideAxis('bottom')
        self.hideAxis('left')
        self.tiempo_text = pg.TextItem("test", anchor=(0.5, 0.5), color="w")
        if font != None:
            self.tiempo_text.setFont(font)
        self.addItem(self.tiempo_text)


    def update(self, value):
        self.tiempo_text.setText('')
        self.tiempo = round(int(value) / 60000, 2)
        self.tiempo_text.setText(str(self.tiempo))