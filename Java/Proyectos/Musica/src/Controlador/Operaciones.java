/*
* To change this license header, choose License Headers in Project Properties.
* To change this template file, choose Tools | Templates
* and open the template in the editor.
*/
package Controlador;
import Modelo.Datos;
import java.sql.ResultSet;
import javax.swing.JOptionPane;
/**
*
* @author USUARIO
*/
public class Operaciones {
static Datos cancion = new Datos();
static String sql,numreg;
static ResultSet resultado,resultadoNum;
static int totReg;
public static Datos CargarRegistros(){

sql="select * from canciones";

try{
resultado=Conexion.ejecutarSQLSelect(sql);
if(resultado.first()) //primero sin if y sin el else ;)
{
cancion.nombre=resultado.getString("nombre");
cancion.artista=resultado.getString("artista");
cancion.album=resultado.getString("album");
cancion.duracion=resultado.getString("duracion");
cancion.anio=resultado.getString("anio");
cancion.genero=resultado.getString("genero");
}
else
{
JOptionPane.showMessageDialog(null, "No hay ningún registro :P");
cancion.nombre="";
cancion.artista="";
cancion.album="";
cancion.duracion="";
cancion.anio="";
cancion.genero="";
}
}
catch (Exception e)
{

e.printStackTrace();
}
return cancion;
}

public static void GuardarRegistro(Datos cancion){
numreg="select count(*) as tot from canciones";
try{
resultadoNum=Conexion.ejecutarSQLSelect(numreg); 
if(resultadoNum.first()){
    totReg = Integer.parseInt(resultadoNum.getString("tot"));
    totReg++;
}
}catch (Exception e)
{ 
e.printStackTrace();
}

sql="insert into canciones values('"+cancion.nombre+"','"+cancion.artista+"','"+cancion.album+"','"+cancion.duracion+"','"+cancion.anio+"','"+cancion.genero+"','"+totReg+"')";
if(Conexion.ejecutarSQL(sql)){
JOptionPane.showMessageDialog(null, "Se ha agregado correctamente la canción");
}
}

}