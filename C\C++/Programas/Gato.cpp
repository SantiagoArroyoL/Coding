#include<stdio.h>
#include<stdlib.h>

int[][] c = [3][3];

bool gano(int x, int y){
	int posx1 = (x+1)%3,
		posx2 = (x+2)%3,
		posy1 = (y+1)%3,
		posy2 = (y+2)%3;
	if (c[x][posy1] == c[x][y] && c[x][posy2] == c[x][y]) {
		return true;
	}
	if (c[posx1][y] == c[x][y] && c[posx2][y] == c[x][y]) {
		return true;
	}
	return false;
}

int main(){

	char c1='1',c2='2',c3='3',c4='4',c5='5',c6='6',c7='7',c8='8',c9='9';
	char resp;
	int b=1,j1,j2,jug=0;

	printf("\t\tBienvenido al juego del gato -.-\n");

 while(b && jug < 9) {
		jug++;

		system("clear");
		printf(" %c | %c | %c\n",c1,c2,c3);
		printf("-----------\n");
		printf(" %c | %c | %c\n",c4,c5,c6);
		printf("-----------\n");
		printf(" %c | %c | %c\n",c7,c8,c9);


		printf("Donde quieres tirar jugador 1: \n");
		fflush(stdin);
		scanf("%d",&resp);

		//Revisamos si la casilla ya está ocupada
		switch(resp) {
			case '1':
				if(c1 == '1')
					c1 = 'X';
				else{
					printf("No puedes sobre escribir casillas \n");
					jug--;
				}
				break;

			case '2':c2='X';break;
			case '3':c3='X';break;
			case '4':c4='X';break;
			case '5':c5='X';break;
			case '6':c6='X';break;
			case '7':c7='X';break;
			case '8':c8='X';break;
			case '9':c9='X';break;

		}

		if(c1 == 'X' && c2 == 'X' && c3 == 'X' || c4 == 'X' && c5 == 'X' && c6 == 'X' || c7 == 'X' && c8 == 'X' && c9 == 'X' || c1 == 'X' && c4 == 'X' && c7 == 'X' || c2 == 'X' && c5 == 'X' && c8 == 'X' || c3 == 'X' && c6 == 'X' && c9 == 'X' || c1 == 'X' && c5 == 'X' && c9 == 'X' || c7 == 'X' && c5 == 'X' && c3 == 'X') {
			b = 0;
			j1 = 1, j2 = 0;
			system("clear");
			printf(" %c | %c | %c\n",c1,c2,c3);
			printf("-----------\n");
			printf(" %c | %c | %c\n",c4,c5,c6);
			printf("-----------\n");
			printf(" %c | %c | %c\n",c7,c8,c9);
			break;
		}

		system("clear");

		printf(" %c | %c | %c\n",c1,c2,c3);
		printf("-----------\n");
		printf(" %c | %c | %c\n",c4,c5,c6);
		printf("-----------\n");
		printf(" %c | %c | %c\n",c7,c8,c9);

		jug++;
		if(jug > 9)
			break;

		printf("Donde quieres tirar jugador 2: \n");
		fflush(stdin);
		scanf("%c",&resp);


		switch(resp){
			case '1':c1='O';break;
			case '2':c2='O';break;
			case '3':c3='O';break;
			case '4':c4='O';break;
			case '5':c5='O';break;
			case '6':c6='O';break;
			case '7':c7='O';break;
			case '8':c8='O';break;
			case '9':c9='O';break;

		}
		if(c1 == 'O' && c2 == 'O' && c3 == 'O' || c4 == 'O' && c5 == 'O' && c6 == 'O' || c7 == 'O' && c8 == 'O' && c9 == 'O' || c1 == 'O' && c4 == 'O' && c7 == 'O' || c2 == 'O' && c5 == 'O' && c8 == 'O' || c3 == 'O' && c6 == 'O' && c9 == 'O' || c1 == 'O' && c5 == 'O' && c9 == 'O' || c7 == 'O' && c5 == 'O' && c3 == 'O') {
			b=0;
			j1=0,j2=1;
			system("clear");
			printf(" %c | %c | %c\n",c1,c2,c3);
			printf("-----------\n");
			printf(" %c | %c | %c\n",c4,c5,c6);
			printf("-----------\n");
			printf(" %c | %c | %c\n",c7,c8,c9);
			break;
		}
		system("clear");
	}

	if(j1==1&&j2==0)
		printf("Gano el jugador 1\n");
	else if(j1==0&&j2==1)
		printf("Gano el jugador 2\n");
	else
		printf("GATO \n");
}
