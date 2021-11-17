#lang plai

#|Integrantes:
   Rodrigo Arevalo Gaytan
   Santiago Arroyo Lozano
   Julio Escobedo|#

;; Definimos el tipo de dato abstracto Figura
(define-type Figura
  [triangulo (a real?) (b real?)(c real?)]
  [cuadrado (a real?)]
  [rectangulo (a real?) (b real?)]
  [rombo (a real?) (D real?) (d real?)]
  [paralelogramo (a real?) (b real?) (h real?)]
  [circulo (D real?)]
  [elipse (a real?) (b real?)])

;;Funcion perimetro recibe una figura y regresa su perimetro.
;;perimetro: Figura -> number
(define (perimetro f)
  (type-case Figura f
    [triangulo (a b c) (+ a b c)]
    [cuadrado (a) (* 4 a)]
    [rectangulo (a b) (+ (* 2 a) (* 2 b))]
    [rombo (a D d) (* 4 a)]
    [paralelogramo (a b h) (+ (* 2 a) (* 2 b))]
    [circulo (D) (* pi D)]
    [elipse (a b)
            (let ([H (expt (/ (- a b) (+ a b)) 2)])
              (* pi
                 (+ a b)
                 (+ 1
                    (/ (* 3 H) (+ 10 (sqrt (* (- 4 3) H))))
                    (* (- (/ 4 pi) (/ 14 11)) (expt H 12)))))]))
;; Para la elipse usamos la formula Ramanujan II-Cantrell


;;Funcion area recibe una figura y regresa su area.
;;area: Figura -> number
(define (area f)
  (type-case Figura f
    [triangulo (a b c) (let ([S (/ (perimetro (triangulo a b c)) 2)])
                         (sqrt (* S (- S a)(- S b)(- S c))))]
    [cuadrado (a) (* a a)]
    [rectangulo (a b) (* a b)]
    [rombo (a D d) (/ (* D d) 2)]
    [paralelogramo (a b h) (* b h)]
    [circulo (D) (* pi (sqr (/ D 2)))]
    [elipse (a b) (* pi a b)]))

;; Definimos el tipo de dato abstracto Vagon
(define-type Vagon
  [simple (capacidad integer?) (pasajeros integer?)]
  [locomotora (peso real?)]
  [restaurante (mesas integer?) (meseros integer?)]
  [dormitorio (camas integer?)]
  [carga (peso real?)])

;; Definimos una función auxiliar que revisará si es locomotora o no
(define (no-locomotora? vagon) (if (or (locomotora? vagon) (locomotora? (first vagon)))
                              (error "Los trenes solo pueden tener 2 locomotoras")
                              vagon))
;; Funcion auxiliar que nos ayuda a revisar la lista 
(define (vagonAux? xs) (cond
                        [(empty? xs) '()]
                        [else (cons (no-locomotora? (first xs)) (vagonAux? (rest xs)))]))
;; Definimos el tipo de dato Tren, que tiene en la cabeza una locomotora y al final tambien
;; Su cuerpo será una lista de Vagones
(define-type Tren 
    [tren (inicio locomotora?) (cuerpo vagonAux?) (fin locomotora?)])

;;(foldr (lambda (i v) (+ v (/ 1 (factorial i))))
;;           0 lst)
(foldr (lambda (i v) (cons i (no-locomotora? v))) '((locomotora 1)) '((simple 1 2) (locomotora 3)))