import pyqtgraph as pg

class graph_bateria(pg.PlotItem):
    
    def __init__(self, parent=None, name=None, labels=None, title='Batería', viewBox=None, axisItems=None, enableMenu=True, font = None,**kargs):    
        super().__init__(parent, name, labels, title, viewBox, axisItems, enableMenu, **kargs)

        self.hideAxis('bottom')
        self.hideAxis('left')
        self.bateria_text = pg.TextItem("test", anchor=(0.5, 0.5), color="w")
        if font != None:
            self.bateria_text.setFont(font)
        self.addItem(self.bateria_text)

    def update(self, value_chain):
        pass