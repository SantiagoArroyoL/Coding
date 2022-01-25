#lang plai

(require "grammars.rkt")
(require "parser.rkt")
(require "desugar.rkt")
;; Búsqueda en el ambiente de evaluación.
;; lookup: symbol Env → AST
(define (lookup sub-id env)
   (match env
      [(mtSub) 
         (error 'lookup "Variable libre")]
      [(aSub id value rest-env)
         (if (symbol=? id sub-id)
             value
             (lookup sub-id rest-env))]))

;; Aplicación de puntos estrictos.
;; strict: AST-Value → AST-Value
(define (strict expr)
   (match expr
      [(exprV expr env) (strict (interp expr env))]
      [else expr]))

;; call-interp
;; Dada una expresión, llamaa la función interp con el ambiente inicial.
;; call-interp: AST -> AST-Value
(define (call-interp expr) (interp expr (mtSub)))

;; Análisis semántico
;; interp: AST Env → AST-Value
(define (interp expr env)
   (match expr
   [(id i) (lookup i env)]
   [(num n) (numV n)]
   [(op f l) (nob (evalua-op f l env))]
   [(iF test-expr then-expr else-expr) then-expr]
   [(fun param body) (closureV param body env)]
   [(lisT elems) (listV (interp-lista elems env))]
   [(app fun-exp arg)
    (let ([fun-val (interp fun-exp env)])
      (interp (get-e fun-val "body")
              (aSub (get-e fun-val "param")
                    (interp arg env)
                    (get-e fun-val "env"))))]))

(define expr18
  (app
   (app
    (fun 'p (fun 'q (iF (id 'p) (id 'p) (id 'q))))(bool #t)) (bool #f)))

;; Funcion auxiliar para interpretar operaciones
;; evalua-op: (listof Binding) symbol AST → (listof Binding)
(define (evalua-op f l env)
  (cond
    [(eq? f +) (if (null? l) 0 (+ (interp-op (car l) env) (evalua-op + (cdr l) env)))]
    [(eq? f -) (if (null? l) 0 (- (interp-op (car l) env) (evalua-op + (cdr l) env)))]
    [(eq? f *) (if (null? l) 1 (* (interp-op (car l) env) (evalua-op * (cdr l) env)))]
    [(eq? f /) (if (null? l) 1 (/ (interp-op (car l) env) (evalua-op * (cdr l) env)))]
    [(eq? f modulo) (modulo (interp-op (car l) env) (interp-op (car (cdr l)) env))]
    [(eq? f expt) (expt (interp-op (car l) env) (interp-op (car (cdr l)) env))]
    [(eq? f add1) (+ (interp-op (car l) env) 1)]
    [(eq? f sub1) (- (interp-op (car l) env) 1)]
    [(eq? f not) (not (interp-op (car l) env))]
    ;;[(eq? f (λ args (foldr (λ (x y) (and x y)) #t args))) (if (null? l) #t (if (interp-op (car l) env) (evalua-op and (cdr l) env) #f))]
    ;;[(eq? f (λ args (foldr (λ (x y) (or x y)) #f args))) (if (null? l) #t (or (interp-op (car l) env) (evalua-op or (cdr l) env)))]
    [(eq? f <) (verifica l <)]
    [(eq? f >) (verifica l >)]
    [(eq? f <=) (verifica l <=)]
    [(eq? f >=) (verifica l >=)]
    [(eq? f =) (verifica l =)]
    [(eq? f zero?) (zero? (interp-op (car l) env))]))

;; Funcion auxiliar que cambia los AST de una lista a numeros
;; transforma: (listof AST) → (listof num)
(define (transforma lista)
  (append (list (interp-op (car lista) (mtSub))) (transforma (cdr lista))))

;; Funcion auxiliar que verifica que toda la lista de números cumpla con la operación contra todos los elementos que le siguen
;; verifica: (listof )-> symbol → bool
(define (verifica lista simbolo)
  (let ([listaT (transforma lista)])
  (if(> (length lista) 2)
     (if (checa (car lista) (cdr listaT) simbolo)
         (verifica (cdr listaT))
         #f)
     (compara simbolo (car listaT) (caar listaT)))))

;; Funcion auxiliar que verifica que el primer elemento cumpla con la operación contra todos los elementos que le siguen
;; verifica: (listof )-> symbol → bool
(define (checa elemento lista simbolo)
  (if(empty? lista)
     #t
     (if (compara simbolo elemento (car lista))
         (checa elemento (cdr lista) simbolo)
         #f)))

;; Funcion auxiliar para preguntar por las operaciones que comparan numeros
;; compara: symbol -> number -> number -> boolean
(define (compara simbolo numero1 numero2)
  (cond
       [(eq? simbolo <) (< numero1 numero2)]
       [(eq? simbolo >) (> numero1 numero2)]
       [(eq? simbolo <=) (<= numero1 numero2)]
       [(eq? simbolo >=) (>= numero1 numero2)]
       [(eq? simbolo =) (= numero1 numero2)]))

;; Funcion auxiliar que decide poner boolV o numV
;; nob: expresion → AST-Value
(define (nob expr)
 (cond
   [(number? expr) (numV expr)]
   [(boolean? expr) (boolV expr)]))

;; Análisis semántico para op
;; interp: AST Env → AST-Value
(define (interp-op expr env)
 (match expr
   [(id i) (interp-op (lookup i env) env)]
   [(num n) n]
   [(numV n) n]
   [(op f l) (interp-op (interp (op f l) env) env)]))

;; Análisis semántico para booleanos
;; interp-opb: AST Env → AST-Value
(define (interp-opb expr env)
 (cond
   [(eq? expr 'true) true]
   [(eq? expr 'false) false]))

;; Funcion auxiliar para obtener el param, body o env de un AST-Value
;; get-e: Binding string → (listof Binding)
(define (get-e Env orden)
  (match Env
    [(closureV param body env) (match orden
                                 ["param" param]
                                 ["body" body]
                                 ["env" env])]))

;; Funcion auxiliar que interpreta una lista de elems
;; interp-lista: AST Env -> AST-Value
(define (interp-lista expr env)
  (if (empty? expr)
      '()
      (cons (interp (first expr) env) (interp-lista (cdr expr) env))))
