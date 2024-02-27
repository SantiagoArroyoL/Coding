%% Tarea 2 de Análisis Numérico - Santiago Arroyo Lozano
% 317150700

%%%%%%%%%%%%%%%%%%%%%%% 1
%%%%%%%%%%%%%%%%%%%%%%% 1
%%%%%%%%%%%%%%%%%%%%%%% 1
%%%%%%%%%%%%%%%%%%%%%%% 1

%% Inciso 1
% Intervalo dado
a = 1/10;
b = 100;

% Números de puntos en las particiones
numPuntos = [5, 10, 20, 50];

% Bucle para cada número de puntos
for n = numPuntos
    x = linspace(a, b, n);

    % Construir la matriz de Vandermonde
    V = vander(x);

    % Calcular la constante de condición K(A)
    K_A = cond(V);

    % Mostrar resultados
    fprintf('Para %d puntos:\n', n);
    % disp(V);
    fprintf('Constante de condición K(A): %e\n', K_A);
    fprintf('--------------------------\n');
end
%% Inciso 3

%%%%%%%%%%%%%%%%%%%%%%% 3
%%%%%%%%%%%%%%%%%%%%%%% 3
%%%%%%%%%%%%%%%%%%%%%%% 3
%%%%%%%%%%%%%%%%%%%%%%% 3

f = @(x) 1 ./ (1 + 25*x.^2); % Runge
I = [-1, 1]; %Intervalo
numPuntos = [10, 20, 30, 40]; %Particiones
% fplot(f);

for n = numPuntos
    x = linspace(I(1), I(2), n);
    y = f(x); 

    % Polinomio de interpolación
    p = polyfit(x, y, n-1);
    
    % Gráfica de f(x) y P(x)
    xDense = linspace(I(1), I(2), 1000); % Puntos para una gráfica más suave
    yDense = f(xDense);
    pVals = polyval(p, xDense);
    
    figure; 
    plot(xDense, yDense, 'b-', xDense, pVals, 'r--');
    legend('f(x)', 'P(x)');
    title(['Interpolación Polinomial con ', num2str(n), ' puntos']);
end

%% Inciso 4

%%%%%%%%%%%%%%%%%%%%%%% 4
%%%%%%%%%%%%%%%%%%%%%%% 4
%%%%%%%%%%%%%%%%%%%%%%% 4
%%%%%%%%%%%%%%%%%%%%%%% 4
for n = numPuntos
    x = linspace(I(1), I(2), n);
    y = f(x);
    
    % Spline cúbico natural
    pp = spline(x, y); % pp es la forma de la pieza polinomial
    
    xDense = linspace(I(1), I(2), 1000); % Puntos para una gráfica más suave
    yDense = f(xDense);
    sVals = ppval(pp, xDense);
    
    figure;
    plot(xDense, yDense, 'b-', xDense, sVals, 'r--');
    legend('f(x)', 'S(x)');
    title(['Interpolación Spline con ', num2str(n), ' puntos']);
end

