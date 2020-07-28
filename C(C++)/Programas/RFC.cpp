/* Notese que está incompleto XD*/

#include <iostream>
#include <string>
// #include <boost/algorithm/string.hpp>
using namespace std;
using namespace boost;


int main() {

	string nombre, fecha;
	string ano, mes, dia, apellidoM, apellidoP, inicial;
	int x;

	cout << "Introduce tu nombre completo:" << endl;
	cin >> nombre;
	cout << "Introduce tu fecha de nacimiento en formato dd/mm/aaaa:" << endl;
	cin >> fecha;

	//CREACIÓN DEL RFC

	//Apellido Paterno
	x = IndexOf(nombre," ");
	apellidoP = nombre.substr(x+1,x+3);
	//Apellido Materno
	size_t found = nombre.find_last_of(" ");
	apellidoM = nombre.substr(found+1);
	//Inicial del nombre
	x = 0;
	inicial = nombre.substr(x,x+1);

	//Año
	x = 6;
	ano = fecha.substr(x+2,x+4);
	//Mes
	x = IndexOf(fecha,"/");
	mes = fecha.substr(x+1,x+3);
	//Día
	x = 0;
	dia = fecha.substr(x,x+2);

	string rfc = apellidoP + apellidoM + inicial + ano + mes + dia;

	// to_upper(rfc);

	cout << "El RFC de " <<  nombre << " es: " << rfc << endl;

	return 0;
}
