%% Segunda parte Tarea01 - Santiago Arroyo Lozano
% 317150700

%% Ejercicio 1

% Definir la matriz A y el vector b del sistema
A = [0.2846 -0.1897; 0.1624 -0.1083];
b = [0.9486; 0.5414];
n = size(A, 1);

% Llevar a cabo la eliminación gaussiana
A_ext = [A b]; % Crear una matriz extendida con A y b
A_ext = AlgoUno(A_ext, n);

% Extraer la matriz A y el vector b modificados
A_mod = A_ext(:, 1:n);
b_mod = A_ext(:, end);

% Resolver el sistema usando sustitución hacia atrás
x = AlgoTres(A_mod, b_mod, n);

% Graficar el sistema de ecuaciones
% Crear un rango de valores para x1
x1_values = linspace(min(x)-1, max(x)+1, 400);

% Calcular x2 para cada ecuación
x2_values_1 = (b(1) - A(1,1) * x1_values) / A(1,2);
x2_values_2 = (b(2) - A(2,1) * x1_values) / A(2,2);

% Graficar las rectas de cada ecuación
plot(x1_values, x2_values_1, 'b');
hold on;
plot(x1_values, x2_values_2, 'r');
plot(x(1), x(2), 'ko', 'MarkerFaceColor', 'g'); % Punto de intersección
xlabel('x_1');
ylabel('x_2');
title('Sistema de Ecuaciones Lineales');
legend('0.2846x_1 - 0.1897x_2 = 0.9486', '0.1624x_1 - 0.1083x_2 = 0.5414', 'Solución');
grid on;
hold off;


%% Ejercicio 3
% Numero de condicion, inversa y producto de Hilbert
for n = 5:1:20
    H = hilb(n);
    K_H = cond(H);
    H_inv = inv(H);
    P = H_inv * H;
    fprintf('Para una matriz de Hilbert de tamaño: %d\n', n);
    % disp(H);
    fprintf('Constante de condición K(H): %e\n', K_H);
    fprintf('Resultado del producto:\n');
    %disp(P);
    fprintf('--------------------------\n');
end

%% Ejercicio 5
A = [0.780 0.563; 0.913 0.659];
b = [0.217; 0.254];

solucion = A \ b;

x_values = linspace(-1, 1, 400);
y_values_ec1 = (b(1) - A(1,1) * x_values) / A(1,2);
y_values_ec2 = (b(2) - A(2,1) * x_values) / A(2,2);
figure;

% Graficar la primera ecuación
plot(x_values, y_values_ec1, 'b');
hold on; % Mantener la grafica para la siguiente ecuación

% Graficar la segunda ecuación
plot(x_values, y_values_ec2, 'r');

% Graficar la solución como un punto
plot(solucion(1), solucion(2), 'ko', 'MarkerFaceColor', 'g');

% Configuraciones adicionales para la gráfica
title('Sistema de Ecuaciones');
xlabel('x_1');
ylabel('x_2');
legend('0.780x_1 + 0.563x_2 = 0.217', '0.913x_1 + 0.659x_2 = 0.254', 'Solución');
grid on;
axis equal;
hold off;


%% Ejercicio 6
A_bien_condicionado = [1 2; 3 4];
b_bien_condicionado = [5; 11];

A_mal_condicionado = [1 1; 1 1.0001];
b_mal_condicionado = [2; 2.0001];

cond_bien = cond(A_bien_condicionado);
cond_mal = cond(A_mal_condicionado);

sol_bien_condicionado = A_bien_condicionado \ b_bien_condicionado;
sol_mal_condicionado = A_mal_condicionado \ b_mal_condicionado;

% Graficar las soluciones de ambos sistemas
x_values = linspace(-10, 10, 400);
y_values_bien = (b_bien_condicionado(1) - A_bien_condicionado(1,1) * x_values) / A_bien_condicionado(1,2);
y_values_bien_2 = (b_bien_condicionado(2) - A_bien_condicionado(2,1) * x_values) / A_bien_condicionado(2,2);
y_values_mal = (b_mal_condicionado(1) - A_mal_condicionado(1,1) * x_values) / A_mal_condicionado(1,2);
y_values_mal_2 = (b_mal_condicionado(2) - A_mal_condicionado(2,1) * x_values) / A_mal_condicionado(2,2);
figure;

% Graficar el sistema bien condicionado
subplot(1, 2, 1);
plot(x_values, y_values_bien, 'b');
hold on;
plot(x_values, y_values_bien_2, 'r');
plot(sol_bien_condicionado(1), sol_bien_condicionado(2), 'ko', 'MarkerFaceColor', 'g');
title(sprintf('Sistema Bien Condicionado (Condición: %.2e)', cond_bien));
xlabel('x');
ylabel('y');
legend('Ecuación 1', 'Ecuación 2', 'Solución');
grid on;
hold off;

% Graficar el sistema mal condicionado
subplot(1, 2, 2);
plot(x_values, y_values_mal, 'b');
hold on;
plot(x_values, y_values_mal_2, 'r');
plot(sol_mal_condicionado(1), sol_mal_condicionado(2), 'ko', 'MarkerFaceColor', 'g');
title(sprintf('Sistema Mal Condicionado (Condición: %.2e)', cond_mal));
xlabel('x');
ylabel('y');
legend('Ecuación 1', 'Ecuación 2', 'Solución');
grid on;
hold off;



%% Ejericio 2. Inversa de la matriz de Hilbert
function [H_inv] = inversa()
    n = 10;
    H = hilb(n);
    H_inv = zeros(n);
    [LU] = AlgoUno(H, n);
    for col = 1:n
        e = zeros(n, 1); 
        e(col) = 1;
        y = AlgoDos(LU, e, n); 
        x = AlgoTres(LU, y, n); 
        H_inv(:, col) = x; 
    end
end


% Algo 2.1
function [A] = AlgoUno(A,n)
    for k = 1:n-1
        for i = k+1:n
            A(i,k) = A(i,k)/A(k,k);
        end
        for i = k+1:n
            for j = k+1:n
                A(i,j) = A(i,j) - A(i,k)*A(k,j);
            end
        end
    end
end

%Algo 2.2
% Sustitucion hacia adelante
function [b] = AlgoDos(A,b,n)
    b(1) = A(1,1);
    for i = 2:n
        sum = 0;
        for j = 1:i-1
            sum = sum + A(i,j) * b(j);
        end
        b(i) = b(i) - sum;
    end
end

%Algo 2.3
% Sustituicion hacia atras
function [b] = AlgoTres(A,b,n)
    b(n) = b(n)/A(n,n);
    for i = n-1:-1:1
        sum = 0;
        for j = i+1:n
            sum = sum + A(i,j) * b(j);
        end
        b(i) = (b(i) - sum) / A(i,i);
    end
end



