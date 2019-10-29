/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package Controlador;
import java.sql.ResultSet;
import Modelo.Datos;
import javax.swing.JOptionPane;

/**
 *
 * @author ROOT
 */
public class Operaciones {
    static Datos cancion = new Datos();
    static String sql, numreg;
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
cancion.albúm=resultado.getString("album");
cancion.duracion=resultado.getString("duracion");
cancion.año=resultado.getString("anio");
cancion.genero=resultado.getString("genero");
}
else
{
JOptionPane.showMessageDialog(null, "No hay ningún registro :P");
cancion.nombre="";
cancion.artista="";
cancion.albúm="";
cancion.duracion="";
cancion.año="";
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
      numreg="select idcanciones from canciones order by idcanciones desc";
try{
resultadoNum=Conexion.ejecutarSQLSelect(numreg); 
if(resultadoNum.first())
{
totReg = Integer.parseInt(resultadoNum.getString("idcanciones"));
totReg++;
}
}catch (Exception e)
{

e.printStackTrace();
}
sql="insert into canciones values(\""+cancion.nombre+"\",\""+cancion.artista+"\",\""+cancion.albúm+"\",\""+cancion.duracion+"\",\""+cancion.año+"\",\""+cancion.genero+"\",\""+totReg+"\")";
if(Conexion.ejecutarSQL(sql)){
JOptionPane.showMessageDialog(null, "Se ha agregado correctamente la cancion");
}
}
    public static void BorrarRegistro(Datos cancion)
    {
       sql="delete from canciones where nombre ='"+cancion.nombre+"' and artista='"+cancion.artista+"' and album='"+cancion.albúm+"'";
       if(Conexion.ejecutarSQL(sql)){
           JOptionPane.showMessageDialog(null,"Se ha borrado correctamente la cancion");
       }
    }
    
}

