--Creacion del esquema
DROP SCHEMA IF EXISTS public CASCADE;
CREATE SCHEMA public;

/*
Parte Roja
*/

CREATE TABLE sucursal(
  rfc CHAR(13) NOT NULL UNIQUE CHECK(CHAR_LENGTH(rfc) = 13),
  nombre VARCHAR(50) NOT NULL CHECK(nombre <> ''),
  tel CHAR(10) UNIQUE CHECK (tel SIMILAR TO '[0-9]*'),
  horario TIME NOT NULL,
  edo VARCHAR(50) NOT NULL CHECK(edo <> ''),
  calle VARCHAR(50) NOT NULL CHECK(calle <> ''),
  num INT NOT NULL,
  cp CHAR(5) NOT NULL CHECK(CHAR_LENGTH(cp) = 5),
  alcMun VARCHAR(50) NOT NULL CHECK(alcMun <> ''),
  correo VARCHAR(50) NOT NULL CHECK(correo <> '')
);

COMMENT ON TABLE sucursal IS 'Tabla que contiene la informacion de las sucursales';
COMMENT ON COLUMN sucursal.rfc IS 'El rfc del sucursal';
COMMENT ON COLUMN sucursal.nombre IS 'El nombre de la sucursal';
COMMENT ON COLUMN sucursal.tel IS 'El telefono de la sucursal';
COMMENT ON COLUMN sucursal.horario IS 'El horario de la sucursal';
COMMENT ON COLUMN sucursal.edo IS 'El estado de donde esta la sucursal';
COMMENT ON COLUMN sucursal.calle IS 'La calle de donde esta la sucursal';
COMMENT ON COLUMN sucursal.num IS 'El numero de donde esta la sucursal';
COMMENT ON COLUMN sucursal.cp IS 'El codigo postal de donde esta la sucursal';
COMMENT ON COLUMN sucursal.alcMun IS 'La alcalcdia o municipio donde esta la sucursal';
COMMENT ON COLUMN sucursal.correo IS 'El correo de la sucursal';


CREATE TABLE proveedor(
  rfc CHAR(13) NOT NULL UNIQUE CHECK(CHAR_LENGTH(rfc) = 13),
  nombre VARCHAR(50) NOT NULL CHECK(nombre <> ''),
  tel CHAR(10) UNIQUE CHECK (tel SIMILAR TO '[0-9]*'),
  edo VARCHAR(50) NOT NULL CHECK(edo <> ''),
  calle VARCHAR(50) NOT NULL CHECK(calle <> ''),
  num INT NOT NULL,
  cp CHAR(5) NOT NULL CHECK(CHAR_LENGTH(cp) = 5)
);

COMMENT ON TABLE proveedor IS 'Tabla que contiene la informacion de los proveedores';
COMMENT ON COLUMN proveedor.rfc IS 'El rfc del proveedor';
COMMENT ON COLUMN proveedor.nombre IS 'El nombre del proveedor';
COMMENT ON COLUMN proveedor.tel IS 'El telefono del proveedor';
COMMENT ON COLUMN proveedor.edo IS 'El estado de donde vive el proveedor';
COMMENT ON COLUMN proveedor.calle IS 'La calle de donde vive el proveedor';
COMMENT ON COLUMN proveedor.num IS 'El numero de donde vive el proveedor';
COMMENT ON COLUMN proveedor.cp IS 'El codigo postal de donde vive el proveedor';


CREATE TABLE proveer(
  rfcSucursal CHAR(13) NOT NULL CHECK(CHAR_LENGTH(rfcSucursal) = 13),
  rfcProveedor CHAR(13) NOT NULL CHECK(CHAR_LENGTH(rfcProveedor) = 13)
);

COMMENT ON TABLE proveer IS 'Tabla que contiene la informacion de la relacion proveer';
COMMENT ON COLUMN proveer.rfcSucursal IS 'El rfc de la sucursal';
COMMENT ON COLUMN proveer.rfcProveedor IS 'El rfc del proveedor';

CREATE TABLE ingrediente(
  idInventario INT NOT NULL UNIQUE,
  rfc CHAR(13) NOT NULL CHECK(CHAR_LENGTH(rfc) = 13),
  cantidad INT NOT NULL,
  fechaCaduc DATE NOT NULL CHECK(CURRENT_DATE < fechaCaduc),
  marca VARCHAR(50) NOT NULL CHECK(marca <> ''),
  diaCompra DATE NOT NULL CHECK(CURRENT_DATE >= diaCompra),
  precio INT NOT NULL
);

COMMENT ON TABLE ingrediente IS 'Tabla que contiene la informacion de los ingredientes';
COMMENT ON COLUMN ingrediente.idInventario IS 'El id que corresponde a la llave del ingrediente';
COMMENT ON COLUMN ingrediente.cantidad IS 'La cantidad de los ingredientes';
COMMENT ON COLUMN ingrediente.fechaCaduc IS 'La fecha de caducidad de los ingredientes';
COMMENT ON COLUMN ingrediente.marca IS 'La marca de los ingredientes';
COMMENT ON COLUMN ingrediente.diaCompra IS 'El dia en que se compraron los ingredientes';
COMMENT ON COLUMN ingrediente.precio IS 'El precio de los ingredientes';


CREATE TABLE mobiliario(
  idInventario INT NOT NULL UNIQUE,
  rfc CHAR(13) NOT NULL CHECK(CHAR_LENGTH(rfc) = 13),
  cantidad INT NOT NULL,
  fechaCaduc DATE NOT NULL CHECK(CURRENT_DATE < fechaCaduc),
  marca VARCHAR(50) NOT NULL CHECK(marca <> ''),
  diaCompra DATE NOT NULL CHECK(CURRENT_DATE >= diaCompra),
  precio INT NOT NULL,
  tipo VARCHAR(50) NOT NULL CHECK(tipo <> '')
);

COMMENT ON TABLE mobiliario IS 'Tabla que contiene la informacion de los mobiliarios';
COMMENT ON COLUMN mobiliario.idInventario IS 'El id que corresponde a la llave del mobiliario';
COMMENT ON COLUMN mobiliario.rfc IS 'El rfc de mobiliario';
COMMENT ON COLUMN mobiliario.cantidad IS 'La cantidad de los mobiliarios';
COMMENT ON COLUMN mobiliario.fechaCaduc IS 'La fecha de caducidad de los mobiliarios';
COMMENT ON COLUMN mobiliario.marca IS 'La marca de los mobiliarios';
COMMENT ON COLUMN mobiliario.diaCompra IS 'El dia en que se compraron los mobiliarios';
COMMENT ON COLUMN mobiliario.precio IS 'El precio de los mobiliarios';
COMMENT ON COLUMN mobiliario.tipo IS 'El tipo de los mobiliarios';


CREATE TABLE contener(
  idInventario INT NOT NULL,
  idProducto INT NOT NULL
);

COMMENT ON TABLE contener IS 'Tabla que contiene la informacion de la relacion contener';
COMMENT ON COLUMN contener.idInventario IS 'El id que corresponde a la llave del ingrediente';
COMMENT ON COLUMN contener.idProducto IS 'El id que corresponde a la llave del producto';

/*
Parte Amarilla
*/
CREATE TABLE ticket(
  idTicket INT NOT NULL UNIQUE,
  idPersonaMesero INT NOT NULL,
  idPersona INT NOT NULL,
  rfc CHAR(13) NOT NULL CHECK(CHAR_LENGTH(rfc) = 13),
  idPago INT NOT NULL,
  fecha DATE NOT NULL CHECK(CURRENT_DATE >= fecha),
  detalleProducto VARCHAR(100) NOT NULL CHECK(detalleProducto <> '')
);

COMMENT ON TABLE ticket IS 'Tabla que contiene la informacion del ticket';
COMMENT ON COLUMN ticket.idTicket IS 'El id del ticket';
COMMENT ON COLUMN ticket.idPersonaMesero IS 'El id del mesero';
COMMENT ON COLUMN ticket.idPersona IS 'El id de la persona';
COMMENT ON COLUMN ticket.rfc IS 'El rfc del mesero';
COMMENT ON COLUMN ticket.idPago IS 'El id del pago';
COMMENT ON COLUMN ticket.fecha IS 'La fecha en que se hizo el ticket';
COMMENT ON COLUMN ticket.detalleProducto IS 'Los productos que fueron comprados';


CREATE TABLE metodoPago(
  idPago INT NOT NULL UNIQUE,
  esEfectivo BOOLEAN NOT NULL,
  esPunto BOOLEAN NOT NULL,
  esTarjeta BOOLEAN NOT NULL
);

COMMENT ON TABLE metodoPago IS 'Tabla que contiene la informacion del metodo de pago';
COMMENT ON COLUMN metodoPago.idPago IS 'El id del pago';
COMMENT ON COLUMN metodoPago.esEfectivo IS 'El pago es en efectivo';
COMMENT ON COLUMN metodoPago.esPunto IS 'El pago es en puntos';
COMMENT ON COLUMN metodoPago.esTarjeta IS 'El pago es en tarjeta';


CREATE TABLE producto(
  idProducto INT NOT NULL UNIQUE,
  nombre VARCHAR(50) NOT NULL CHECK(nombre <> ''),
  descr VARCHAR(200) NOT NULL CHECK(descr <> ''),
  fecha DATE NOT NULL CHECK(fecha > '2017-01-01')
);

COMMENT ON TABLE producto IS 'Tabla que contiene la informacion del producto';
COMMENT ON COLUMN producto.idProducto IS 'El id del producto';
COMMENT ON COLUMN producto.nombre IS 'El nombre del producto';
COMMENT ON COLUMN producto.descr IS 'El descuento del producto';
COMMENT ON COLUMN producto.fecha IS 'La fecha del producto';


CREATE TABLE precio(
  idProducto INT NOT NULL,
  precio INT NOT NULL UNIQUE,
  valor INT NOT NULL,
  fecha DATE NOT NULL CHECK(fecha > '2017-01-01')
);

COMMENT ON TABLE precio IS 'Tabla que contiene la informacion del precio';
COMMENT ON COLUMN precio.idProducto IS 'El id del producto';
COMMENT ON COLUMN precio.precio IS 'El precio';
COMMENT ON COLUMN precio.valor IS 'El valor';
COMMENT ON COLUMN precio.fecha IS 'La fecha del precio';


CREATE TABLE registrar(
  idProducto INT NOT NULL,
  idTicket INT NOT NULL,
  cantidad INT NOT NULL
);

COMMENT ON TABLE registrar IS 'Tabla que contiene la informacion de la relacion registrar';
COMMENT ON COLUMN registrar.idProducto IS 'El id que corresponde a la llave del producto';
COMMENT ON COLUMN registrar.idTicket IS 'El id que corresponde a la llave del ticket';
COMMENT ON COLUMN registrar.cantidad IS 'La cantidad de la relacion registrar';


CREATE TABLE torta(
  idProducto INT NOT NULL UNIQUE
);

COMMENT ON TABLE torta IS 'Tabla que contiene la informacion de la torta';
COMMENT ON COLUMN torta.idProducto IS 'El id de la torta';


CREATE TABLE taco(
  idProducto INT NOT NULL UNIQUE
);

COMMENT ON TABLE taco IS 'Tabla que contiene la informacion del taco';
COMMENT ON COLUMN taco.idProducto IS 'El id del taco';


CREATE TABLE platilloMexicano(
  idProducto INT NOT NULL UNIQUE
);

COMMENT ON TABLE platilloMexicano IS 'Tabla que contiene la informacion del platillo mexicano';
COMMENT ON COLUMN platilloMexicano.idProducto IS 'El id del platillo mexicano';


CREATE TABLE burrito(
  idProducto INT NOT NULL UNIQUE
);

COMMENT ON TABLE burrito IS 'Tabla que contiene la informacion del burrito';
COMMENT ON COLUMN burrito.idProducto IS 'El id del burrito';


CREATE TABLE gringa(
  idProducto INT NOT NULL UNIQUE
);

COMMENT ON TABLE gringa IS 'Tabla que contiene la informacion del gringa';
COMMENT ON COLUMN gringa.idProducto IS 'El id de la gringa';


CREATE TABLE quesadilla(
  idProducto INT NOT NULL UNIQUE
);

COMMENT ON TABLE quesadilla IS 'Tabla que contiene la informacion de la quesadilla';
COMMENT ON COLUMN quesadilla.idProducto IS 'El id de la quesadilla';


CREATE TABLE bebida(
  idProducto INT NOT NULL UNIQUE
);

COMMENT ON TABLE bebida IS 'Tabla que contiene la informacion de la bebida';
COMMENT ON COLUMN bebida.idProducto IS 'El id de la bebida';


CREATE TABLE salsa(
  idProducto INT NOT NULL UNIQUE,
  recomendacion VARCHAR(50) NOT NULL CHECK(recomendacion <> ''),
  nivelPicor INT NOT NULL,
  presentacion INT NOT NULL
);

COMMENT ON TABLE salsa IS 'Tabla que contiene la informacion de la salsa';
COMMENT ON COLUMN salsa.idProducto IS 'El id de la salsa';
COMMENT ON COLUMN salsa.recomendacion IS 'La recomendacion de salsa';
COMMENT ON COLUMN salsa.nivelPicor IS 'El nivel de picor de la salsa';
COMMENT ON COLUMN salsa.presentacion IS 'La presentacion de la salsa';

/*
Parte Azul
*/
 
CREATE TABLE persona(
  idPersona INT NOT NULL UNIQUE,
  rfcSucursal CHAR(13) NOT NULL CHECK(CHAR_LENGTH(rfc) = 13),
  nombre VARCHAR(50) NOT NULL CHECK(nombre <> ''),
  pat VARCHAR(50) NOT NULL CHECK(pat <> ''),
  mat VARCHAR(50) NOT NULL CHECK(mat <> ''),
  edo VARCHAR(50) NOT NULL CHECK(edo <> ''),
  calle VARCHAR(50) NOT NULL CHECK(calle <> ''),
  num INT NOT NULL,
  cp CHAR(5) NOT NULL CHECK(CHAR_LENGTH(cp) = 5),
  correo VARCHAR(50) NOT NULL CHECK(correo <> ''),
  curp CHAR(18) NOT NULL CHECK(CHAR_LENGTH(curp) = 18),
  rfc CHAR(13) NOT NULL CHECK(CHAR_LENGTH(rfc) = 13),
  nss CHAR(11) NOT NULL CHECK(CHAR_LENGTH(nss) = 11),
  salario INT NOT NULL,
  antiguedad INT NOT NULL,
  fechaNac DATE NOT NULL CHECK(fechaNac < '2017-01-01'),
  puntos INT NOT NULL,
  esEmpleado BOOLEAN NOT NULL,
  esCliente BOOLEAN NOT NULL
);

COMMENT ON TABLE persona IS 'Tabla que contiene la informacion de los clientes y empleados';
COMMENT ON COLUMN persona.idPersona IS 'El id de la persona';
COMMENT ON COLUMN persona.rfcSucursal IS 'El rfc de la sucursal';
COMMENT ON COLUMN persona.nombre IS 'El nombre de la persona';
COMMENT ON COLUMN persona.pat IS 'El apellido paterno de la persona';
COMMENT ON COLUMN persona.mat IS 'El apellido materno de la persona';
COMMENT ON COLUMN persona.edo IS 'El estado en donde vive la persona';
COMMENT ON COLUMN persona.calle IS 'La calle de donde vive la persona';
COMMENT ON COLUMN persona.num IS 'El numero en donde vive la persona';
COMMENT ON COLUMN persona.cp IS 'El codigo postal en donde vive la persona';
COMMENT ON COLUMN persona.correo IS 'El correo de la persona';
COMMENT ON COLUMN persona.curp IS 'El curp de la persona';
COMMENT ON COLUMN persona.rfc IS 'El rfc de la persona';
COMMENT ON COLUMN persona.nss IS 'El nss de la persona';
COMMENT ON COLUMN persona.salario IS 'El salario del empleado';
COMMENT ON COLUMN persona.antiguedad IS 'La antiguedad del empleado';
COMMENT ON COLUMN persona.fechaNac IS 'La fecha de nacimiento de la persona';
COMMENT ON COLUMN persona.puntos IS 'Los puntos de la persona';
COMMENT ON COLUMN persona.esEmpleado IS 'La persona es un empleado';
COMMENT ON COLUMN persona.esCliente IS 'La persona es un cliente';


CREATE TABLE telefono(
  idPersona INT NOT NULL UNIQUE,
  telefono CHAR(10) NOT NULL UNIQUE CHECK (telefono SIMILAR TO '[0-9]*')
);

COMMENT ON TABLE telefono IS 'Tabla que contiene el telefono de la persona';
COMMENT ON COLUMN telefono.idPersona IS 'El id de la persona';
COMMENT ON COLUMN telefono.telefono IS 'El telefono de la persona';


CREATE TABLE parrillero(
  idPersona INT NOT NULL UNIQUE
);

COMMENT ON TABLE parrillero IS 'Tabla que contiene la informacion del parrillero';
COMMENT ON COLUMN parrillero.idPersona IS 'El id del empleado';


CREATE TABLE tortillero(
  idPersona INT NOT NULL UNIQUE
);

COMMENT ON TABLE tortillero IS 'Tabla que contiene la informacion del tortillero';
COMMENT ON COLUMN tortillero.idPersona IS 'El id del empleado';


CREATE TABLE cajero(
  idPersona INT NOT NULL UNIQUE
);

COMMENT ON TABLE cajero IS 'Tabla que contiene la informacion del cajero';
COMMENT ON COLUMN cajero.idPersona IS 'El id del empleado';


CREATE TABLE mesero(
  idPersona INT NOT NULL UNIQUE
);

COMMENT ON TABLE mesero IS 'Tabla que contiene la informacion del mesero';
COMMENT ON COLUMN mesero.idPersona IS 'El id del empleado';


CREATE TABLE taquero(
  idPersona INT NOT NULL UNIQUE
);

COMMENT ON TABLE taquero IS 'Tabla que contiene la informacion del taquero';
COMMENT ON COLUMN taquero.idPersona IS 'El id del empleado';


CREATE TABLE repartidor(
  idPersona INT NOT NULL UNIQUE
);

COMMENT ON TABLE repartidor IS 'Tabla que contiene la informacion del repartidor';
COMMENT ON COLUMN repartidor.idPersona IS 'El id del empleado';


CREATE TABLE motocicleta(
  idTransporte INT NOT NULL UNIQUE,
  modelo VARCHAR(50) NOT NULL CHECK(modelo <> ''),
  marca VARCHAR(50) NOT NULL CHECK(marca <> ''),
  numLic INT NOT NULL
);

COMMENT ON TABLE motocicleta IS 'Tabla que contiene la informacion de la motocicleta';
COMMENT ON COLUMN motocicleta.idTransporte IS 'El id del transporte';
COMMENT ON COLUMN motocicleta.modelo IS 'El modelo de la motocicleta';
COMMENT ON COLUMN motocicleta.marca IS 'La marca de la motocicleta';
COMMENT ON COLUMN motocicleta.numLic IS 'El numero de licencia del repartidor';


CREATE TABLE tenerMoto(
  idPersona INT NOT NULL,
  idTransporte INT NOT NULL
);

COMMENT ON TABLE tenerMoto IS 'Tabla que contiene la informacion de tener motocicleta';
COMMENT ON COLUMN tenerMoto.idPersona IS 'El id del empleado';
COMMENT ON COLUMN tenerMoto.idTransporte IS 'El id del transporte';


CREATE TABLE bicicleta(
  idTransporte INT NOT NULL UNIQUE,
  modelo VARCHAR(50) NOT NULL CHECK(modelo <> ''),
  marca VARCHAR(50) NOT NULL CHECK(marca <> '')
);

COMMENT ON TABLE bicicleta IS 'Tabla que contiene la informacion de la bicicleta';
COMMENT ON COLUMN bicicleta.idTransporte IS 'El id del transporte';
COMMENT ON COLUMN bicicleta.modelo IS 'El modelo de la bicicleta';
COMMENT ON COLUMN bicicleta.marca IS 'La marca de la bicicleta';


CREATE TABLE tenerBici(
  idPersona INT NOT NULL,
  idTransporte INT NOT NULL
);

COMMENT ON TABLE tenerBici IS 'Tabla que contiene la informacion de tener bicicleta';
COMMENT ON COLUMN tenerBici.idPersona IS 'El id del empleado';
COMMENT ON COLUMN tenerBici.idTransporte IS 'El id del transporte';

/*
Integridad Referencial
*/
ALTER TABLE sucursal ADD CONSTRAINT sucursal_pkey PRIMARY KEY (rfc);
COMMENT ON CONSTRAINT sucursal_pkey ON sucursal IS 'La llave primaria de la tabla sucursal';

ALTER TABLE proveedor ADD CONSTRAINT proveedor_pkey PRIMARY KEY (rfc);
COMMENT ON CONSTRAINT proveedor_pkey ON proveedor IS 'La llave primaria de la tabla proveedor';

ALTER TABLE proveer ADD CONSTRAINT proveer_fkey1 FOREIGN KEY (rfcSucursal)
REFERENCES sucursal(rfc) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT proveer_fkey1 ON proveer IS 'La llave foranea de la tabla proveer que referencia a proveedor';
ALTER TABLE proveer ADD CONSTRAINT proveer_fkey2 FOREIGN KEY (rfcProveedor)
REFERENCES proveedor(rfc) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT proveer_fkey2 ON proveer IS 'La llave foranea de la tabla proveer que referencia a sucursal';

ALTER TABLE persona ADD CONSTRAINT persona_pkey PRIMARY KEY (idPersona);
COMMENT ON CONSTRAINT persona_pkey ON persona IS 'La llave primaria de la tabla persona';
ALTER TABLE persona ADD CONSTRAINT persona_fkey FOREIGN KEY (rfcSucursal)
REFERENCES sucursal(rfc) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT persona_fkey ON persona IS 'La llave foranea de la tabla persona que referencia a sucursal';

ALTER TABLE telefono ADD CONSTRAINT telefono_pkey PRIMARY KEY (idPersona,telefono);
COMMENT ON CONSTRAINT telefono_pkey ON telefono IS 'La llave primaria de la tabla telefono';
ALTER TABLE telefono ADD CONSTRAINT telefono_fkey FOREIGN KEY (idPersona)
REFERENCES persona (idPersona) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT telefono_fkey ON telefono IS 'La llave foranea de la tabla telefono que referencia a persona';

ALTER TABLE parrillero ADD CONSTRAINT parrillero_pkey PRIMARY KEY (idPersona);
COMMENT ON CONSTRAINT parrillero_pkey ON parrillero IS 'La llave primaria de la tabla parrillero';

ALTER TABLE tortillero ADD CONSTRAINT tortillero_pkey PRIMARY KEY (idPersona);
COMMENT ON CONSTRAINT tortillero_pkey ON tortillero IS 'La llave primaria de la tabla tortillero';

ALTER TABLE cajero ADD CONSTRAINT cajero_pkey PRIMARY KEY (idPersona);
COMMENT ON CONSTRAINT cajero_pkey ON cajero IS 'La llave primaria de la tabla cajero';

ALTER TABLE mesero ADD CONSTRAINT mesero_pkey PRIMARY KEY (idPersona);
COMMENT ON CONSTRAINT mesero_pkey ON mesero IS 'La llave primaria de la tabla mesero';

ALTER TABLE taquero ADD CONSTRAINT taquero_pkey PRIMARY KEY (idPersona);
COMMENT ON CONSTRAINT taquero_pkey ON taquero IS 'La llave primaria de la tabla taquero';

ALTER TABLE repartidor ADD CONSTRAINT repartidor_pkey PRIMARY KEY (idPersona);
COMMENT ON CONSTRAINT repartidor_pkey ON repartidor IS 'La llave primaria de la tabla repartidor';

ALTER TABLE motocicleta ADD CONSTRAINT motocicleta_pkey PRIMARY KEY (idTransporte);
COMMENT ON CONSTRAINT motocicleta_pkey ON motocicleta IS 'La llave primaria de la tabla motocicleta';

ALTER TABLE tenerMoto ADD CONSTRAINT tenerMoto_fkey1 FOREIGN KEY (idPersona)
REFERENCES repartidor(idPersona) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT tenerMoto_fkey1 ON tenerMoto IS 'La llave foranea de la tabla tenerMoto que referencia a repartidor';
ALTER TABLE tenerMoto ADD CONSTRAINT tenerMoto_fkey2 FOREIGN KEY (idTransporte)
REFERENCES motocicleta(idTransporte) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT tenerMoto_fkey2 ON tenerMoto IS 'La llave foranea de la tabla tenerMoto que referencia a motocicleta';

ALTER TABLE bicicleta ADD CONSTRAINT bicicleta_pkey PRIMARY KEY (idTransporte);
COMMENT ON CONSTRAINT bicicleta_pkey ON bicicleta IS 'La llave primaria de la tabla bicicleta';

ALTER TABLE tenerBici ADD CONSTRAINT tenerBici_fkey1 FOREIGN KEY (idPersona)
REFERENCES repartidor(idPersona) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT tenerBici_fkey1 ON tenerBici IS 'La llave foranea de la tabla tenerBici que referencia a repartidor';
ALTER TABLE tenerBici ADD CONSTRAINT tenerBici_fkey2 FOREIGN KEY (idTransporte)
REFERENCES bicicleta(idTransporte) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT tenerBici_fkey2 ON tenerBici IS 'La llave foranea de la tabla tenerBici que referencia a bicicleta';

ALTER TABLE ingrediente ADD CONSTRAINT ingrediente_pkey PRIMARY KEY (idInventario);
COMMENT ON CONSTRAINT ingrediente_pkey ON ingrediente IS 'La llave primaria de la tabla ingrediente';
ALTER TABLE ingrediente ADD CONSTRAINT ingrediente_fkey FOREIGN KEY (rfc)
REFERENCES sucursal(rfc) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT ingrediente_fkey ON ingrediente IS 'La llave foranea de la tabla ingrediente que referencia a sucursal';

ALTER TABLE mobiliario ADD CONSTRAINT mobiliario_pkey PRIMARY KEY (idInventario);
COMMENT ON CONSTRAINT mobiliario_pkey ON mobiliario IS 'La llave primaria de la tabla mobiliario';
ALTER TABLE mobiliario ADD CONSTRAINT mobiliario_fkey FOREIGN KEY (rfc)
REFERENCES sucursal(rfc) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT mobiliario_fkey ON mobiliario IS 'La llave foranea de la tabla mobiliario que referencia a sucursal';

ALTER TABLE contener ADD CONSTRAINT contener_fkey1 FOREIGN KEY (idInventario)
REFERENCES ingrediente(idInventario) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT contener_fkey1 ON contener IS 'La llave foranea de la tabla contener que referencia a ingrediente';
ALTER TABLE contener ADD CONSTRAINT contener_fkey2 FOREIGN KEY (idProducto)
REFERENCES producto(idProducto) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT contener_fkey2 ON contener IS 'La llave foranea de la tabla contener que referencia a producto';

ALTER TABLE producto ADD CONSTRAINT producto_pkey PRIMARY KEY (idProducto);
COMMENT ON CONSTRAINT producto_pkey ON producto IS 'La llave primaria de la tabla producto';

ALTER TABLE torta ADD CONSTRAINT torta_pkey PRIMARY KEY (idProducto);
COMMENT ON CONSTRAINT torta_pkey ON torta IS 'La llave primaria de la tabla torta';

ALTER TABLE taco ADD CONSTRAINT taco_pkey PRIMARY KEY (idProducto);
COMMENT ON CONSTRAINT taco_pkey ON taco IS 'La llave primaria de la tabla taco';

ALTER TABLE platilloMexicano ADD CONSTRAINT platilloMexicano_pkey PRIMARY KEY (idProducto);
COMMENT ON CONSTRAINT platilloMexicano_pkey ON platilloMexicano IS 'La llave primaria de la tabla platilloMexicano';

ALTER TABLE burrito ADD CONSTRAINT burrito_pkey PRIMARY KEY (idProducto);
COMMENT ON CONSTRAINT burrito_pkey ON burrito IS 'La llave primaria de la tabla burrito';

ALTER TABLE gringa ADD CONSTRAINT gringa_pkey PRIMARY KEY (idProducto);
COMMENT ON CONSTRAINT gringa_pkey ON gringa IS 'La llave primaria de la tabla gringa';

ALTER TABLE bebida ADD CONSTRAINT bebida_pkey PRIMARY KEY (idProducto);
COMMENT ON CONSTRAINT bebida_pkey ON bebida IS 'La llave primaria de la tabla bebida';

ALTER TABLE salsa ADD CONSTRAINT salsa_pkey PRIMARY KEY (idProducto);
COMMENT ON CONSTRAINT salsa_pkey ON salsa IS 'La llave primaria de la tabla salsa';

ALTER TABLE precio ADD CONSTRAINT precio_pkey PRIMARY KEY (idProducto,precio);
COMMENT ON CONSTRAINT precio_pkey ON precio IS 'La llave primaria de la tabla precio';
ALTER TABLE precio ADD CONSTRAINT precio_fkey FOREIGN KEY (idProducto)
REFERENCES producto (idProducto) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT precio_fkey ON precio IS 'La llave foranea de la tabla precio que referencia a producto';

ALTER TABLE registrar ADD CONSTRAINT registrar_fkey1 FOREIGN KEY (idProducto)
REFERENCES producto(idProducto) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT registrar_fkey1 ON registrar IS 'La llave foranea de la tabla registrar que referencia a producto';
ALTER TABLE registrar ADD CONSTRAINT registrar_fkey2 FOREIGN KEY (idTicket)
REFERENCES ticket(idTicket) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT registrar_fkey2 ON registrar IS 'La llave foranea de la tabla registrar que referencia a ticket';

ALTER TABLE metodoPago ADD CONSTRAINT metodoPago_pkey PRIMARY KEY (idPago);
COMMENT ON CONSTRAINT metodoPago_pkey ON metodoPago IS 'La llave primaria de la tabla metodoPago';

ALTER TABLE ticket ADD CONSTRAINT ticket_pkey PRIMARY KEY (idTicket);
COMMENT ON CONSTRAINT ticket_pkey ON ticket IS 'La llave primaria de la tabla ticket';
ALTER TABLE ticket ADD CONSTRAINT ticket_fkey1 FOREIGN KEY (idPersonaMesero)
REFERENCES mesero(idPersona) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT ticket_fkey1 ON ticket IS 'La llave foranea de la tabla ticket que referencia a mesero';
ALTER TABLE ticket ADD CONSTRAINT ticket_fkey2 FOREIGN KEY (idPersona)
REFERENCES persona(idPersona) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT ticket_fkey2 ON ticket IS 'La llave foranea de la tabla ticket que referencia a persona';
ALTER TABLE ticket ADD CONSTRAINT ticket_fkey3 FOREIGN KEY (rfc)
REFERENCES sucursal(rfc) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT ticket_fkey3 ON ticket IS 'La llave foranea de la tabla ticket que referencia a sucursal';
ALTER TABLE ticket ADD CONSTRAINT ticket_fkey4 FOREIGN KEY (idPago)
REFERENCES metodoPago(idPago) ON UPDATE CASCADE ON DELETE CASCADE;
COMMENT ON CONSTRAINT ticket_fkey4 ON ticket IS 'La llave foranea de la tabla ticket que referencia a metodoPago';