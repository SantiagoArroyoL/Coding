/********************************************** Funciones **********************************************/
--CREATE LANGUAGE plpgsql;

-- Funcion que nos da el precio más reciente de un producto
-- Recibe idProducto y nos regresa la fila completa del precio.
CREATE OR REPLACE FUNCTION obten_precio(int)
	RETURNS TABLE (idProducto int,
                 precio int, 
                 valor int, 
                 fecha date)
	AS $$
	DECLARE
		id_producto int;
	BEGIN
      id_producto := $1;
      RETURN QUERY 
      SELECT * FROM precio WHERE id_producto = precio.idProducto
      ORDER BY precio.fecha DESC LIMIT 1;
	END;
	$$
	Language plpgsql;


-- Funcion que nos da el total de un ticket dado
-- recibe el idTicket y regresa un int
-- Sumamos el valor de cada precio de cada producto en el ticket iterando la relacion registrar
-- a fuerzas debemos iterar porque para cada valor debemos multiplcar la cantidad de ese producto
-- Si el cliente es empleado en automatico el total es 0; gratis
CREATE OR REPLACE FUNCTION calcula_total(int)
	RETURNS int
	AS $$
	DECLARE
		valor_p int;
		id_ticket int;
		total int := 0;
		fila registrar%rowType;
	BEGIN
    id_ticket := $1;
    FOR fila IN SELECT * FROM registrar
    WHERE id_ticket = registrar.idTicket LOOP
      SELECT valor INTO valor_p FROM obten_precio(fila.idProducto);
      total := total + (fila.cantidad * valor_p);
    END LOOP;
    RETURN total;
	END;
	$$
	Language plpgsql;


/********************************************** Store Procedures **********************************************/

-- crea_default
-- SP que crea el ticket del usuario default. recibe el rfc de la sucursal, el mesero, idPago y detalle asociados
-- Si no existe el usuario default lo creamos con base en el rfc recibido
CREATE OR REPLACE PROCEDURE crea_default(_rfc IN CHAR(13),
										_mesero IN int,
										 _idPago IN int, 
										_detalle IN VARCHAR(100))
	AS $$
	DECLARE
		_nombre VARCHAR(50);
		_tel CHAR(10);
		_edo VARCHAR(50);
		_calle VARCHAR(50);
		_num INT;
		_cp CHAR(5);
		_correo VARCHAR(50);
		_id int;
		_id_temp int;
	BEGIN
		-- Si no existe el usuario default, lo creamos
		IF NOT (SELECT EXISTS (SELECT idPersona FROM persona WHERE 'LOMNJHG123R5P' = persona.nombre)) THEN
			SELECT COUNT(*) INTO _id FROM persona;
			_id := _id+1;
			SELECT nombre, tel, edo, calle, num, cp, correo INTO _nombre, _tel, _edo, _calle, _num, _cp, _correo
			FROM sucursal WHERE _rfc = sucursal.rfc;
			INSERT INTO persona (idPersona, rfcSucursal, nombre, pat, mat, edo, calle, num, cp, correo, curp, rfc, nss, salario, antiguedad, fechaNac, puntos, esEmpleado, esCliente)
			VALUES (_id, _rfc, _nombre, _nombre, _nombre, _edo, _calle, _num, _cp, _correo, '000000000000000000', _rfc, '00000000000', 0, 0, '2016-01-01', 0, false, true);
		END IF;
		SELECT COUNT(*) INTO _id_temp FROM ticket;
		_id_temp := _id_temp+1;
		INSERT INTO ticket(idTicket,idPersonaMesero,idPersona,rfc,idPago,fecha,detalleProducto) 
		VALUES (_id_temp,_mesero,_id,_rfc,_idPago,CURRENT_DATE,_detalle);
	END;
	$$
	Language plpgsql;



/********************************************** TRIGGERS **********************************************/

-- TRIGGER PUNTOS
--  Este trigger le almacena el 10% de puntos de la última compra al cliente. Sin perder los puntos anteriores
-- Se hace DESPUES de insertar en la base de datos la fila de registrar para asi poder hacer las consultas sin problemas
-- Es decir, le damos los puntos al cliente despues de que se registra el ticket con sus productos
-- Tiene la peculiaridad de que si el 10% de los puntos es un numero flotante se redondea, hacia abajo si es menor a .5 y hacia arriba en otro caso
-- ADEMAS este trigger revisará si el saldo de puntos del cliente seria suficiente para pagar el ticket, si el metodo de pago es puntos
-- Los empleados NO generan puntos pues su consumo es gratis
CREATE OR REPLACE FUNCTION almacena_puntos() RETURNS TRIGGER
	AS $$ 
	DECLARE
   	total_ticket int := calcula_total(NEW.idTicket);
		total_puntos int;
		id_persona int;
		punto boolean;
	BEGIN
		-- Obtenemos la persona que pago y sus puntos
		SELECT INTO id_persona, total_puntos, punto persona.idPersona, puntos, esPunto FROM metodoPago 
			INNER JOIN ticket ON ticket.idPago = metodoPago.idPago
			INNER JOIN persona ON ticket.idPersona = persona.idPersona
			WHERE NEW.idTicket = ticket.idTicket;
		-- Si va a pagar con puntos revisamos que le alcance
		IF punto THEN
			IF total_puntos < total_ticket THEN
				RAISE EXCEPTION 'El cliente quiere pagar con puntos que no tiene!';
			END IF;
			total_puntos := total_puntos - total_ticket;
		END IF;
		-- Finalmente calculamos el 10% y se lo sumamos a los puntos que ya tenia
		total_puntos := total_puntos + (total_ticket * 0.10);
		-- Actualizamos
		UPDATE persona
  		SET puntos = total_puntos
  		WHERE id_persona = persona.idPersona;
		RETURN NEW;
	END;
$$
LANGUAGE plpgsql;

CREATE OR REPLACE TRIGGER trigger_puntos
	AFTER INSERT
	ON registrar
	FOR EACH ROW
	EXECUTE PROCEDURE almacena_puntos();