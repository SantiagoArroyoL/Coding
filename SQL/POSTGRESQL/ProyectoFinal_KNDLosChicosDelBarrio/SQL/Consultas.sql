-- 1.Los 3 clientes que consumieron más en el primer trimestre de 2021
SELECT persona.idPersona, SUM(calcula_total(idTicket)) AS total
FROM ticket INNER JOIN persona ON persona.idPersona = ticket.idPersona
WHERE ticket.fecha >= '2022-01-01' AND ticket.fecha <= '2022-03-31'
GROUP BY persona.idPersona ORDER BY total DESC LIMIT 3;

-- 2.El empleado del mes
SELECT idPersonaMesero, SUM(calcula_total(idTicket)) AS total
	FROM ticket 
WHERE date_trunc('month', fecha) = date_trunc('month', CURRENT_DATE)
	AND date_trunc('year', fecha) = date_trunc('year', CURRENT_DATE)
GROUP BY idPersonaMesero ORDER BY total DESC LIMIT 1;

-- 3. Los 5 productos más vendidos 
SELECT producto.nombre, SUM(cantidad) AS total FROM producto 
	INNER JOIN registrar ON producto.idProducto = registrar.idProducto
	GROUP BY producto.nombre ORDER BY total DESC LIMIT 5;

--4. Alcaldía que más consume
SELECT sucursal.alcmun, SUM(calcula_total(idTicket)) AS total 
FROM sucursal 
INNER JOIN ticket ON sucursal.rfc = ticket.rfc 
GROUP BY sucursal.alcmun ORDER BY total DESC LIMIT 1;

--5. Que sucursal genera más ganancias o ventas
SELECT sucursal.alcmun, SUM(calcula_total(idTicket)) AS total FROM sucursal
INNER JOIN ticket ON sucursal.rfc = ticket.rfc
GROUP BY sucursal.alcmun ORDER BY total DESC LIMIT 1;

--6. El nombre del producto que se vende menos
SELECT producto.nombre, SUM(cantidad) AS total FROM producto 
    INNER JOIN registrar ON producto.idProducto = registrar.idProducto
    GROUP BY producto.nombre ORDER BY total ASC LIMIT 1;

--7. Los ingredientes que caducan el mes en el que nos encontramos.
SELECT idInventario, marca, sucursal.nombre,sucursal.rfc 
    FROM ingrediente INNER JOIN sucursal 
    ON sucursal.rfc = ingrediente.rfc 
    WHERE date_trunc('month', fechaCaduc) =
    date_trunc('month', CURRENT_DATE);

--8. El precio más vendido dentro del historial de precios del producto
SELECT producto.nombre, SUM(precio)AS total, precio.valor  FROM producto 
	INNER JOIN registrar ON producto.idProducto = registrar.idProducto
	INNER JOIN precio ON producto.idProducto = precio.idProducto
	GROUP BY producto.nombre, precio.valor ORDER BY total DESC LIMIT 5;

--9. Cliente que ha usado más puntos que no sea de la ciudad
SELECT persona.nombre, persona.pat, persona.mat, persona.edo, 
persona.esCliente, metodoPago.esPunto, SUM(calcula_total(idTicket)) 
AS total FROM persona 
INNER JOIN ticket ON persona.idPersona = ticket.idPersona 
INNER JOIN metodoPago ON ticket.idPago = metodoPago.idPago
WHERE persona.edo != 'Distrito Federal' 
AND persona.esCliente = true AND metodoPago.esPunto = true
GROUP BY persona.nombre, persona.pat, persona.mat, persona.edo, 
persona.esCliente, metodoPago.esPunto
ORDER BY total DESC LIMIT 1;

-- 10. Empleado que consume mas en una sucursal dada (Con ejemplo)
SELECT ticket.rfc, persona.idPersona, count(persona.idPersona) AS frecuencia_visita
		FROM persona 
		INNER JOIN ticket ON ticket.idPersona = persona.idPersona
	WHERE esEmpleado = true AND ticket.rfc = 'QURU260117138'
	GROUP BY ticket.rfc, persona.idPersona ORDER BY frecuencia_visita DESC LIMIT 1;
  
-- 11. El empleado con mas antiguedad 
SELECT * FROM persona WHERE esEmpleado = true ORDER BY antiguedad DESC LIMIT 1;
