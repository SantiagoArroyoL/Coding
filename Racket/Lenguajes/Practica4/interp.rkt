#lang plai

(require "grammars.rkt")

;; Búsqueda en el ambiente de evaluación.
;, lookup: symbol Env → AST
(define (lookup sub-id env)
   (match env
      [(mtSub) 
         (error 'lookup "Variable libre")]
      [(aSub id value rest-env)
         (if (symbol=? id sub-id)
             value
             (lookup sub-id rest-env))]))

;; Análisis semántico
;; interp: AST Env → AST-Value
(define (interp expr env)
 (match expr
   [(id i) (lookup i env)]
   [(num n) (numV n)]
   [(op f l) (numV (evalua-op f l env))]
   [(fun param body) (closureV param body env)]
   [(app fun-exp arg)
    (let ([fun-val (interp fun-exp env)])
      (interp (get-e fun-val "body")
              (aSub (get-e fun-val "param")
                    (interp arg env)
                    (get-e fun-val "env"))))]))

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
  ))

;; Análisis semántico para op
;; interp: AST Env → AST-Value
(define (interp-op expr env)
 (match expr
   [(id i) (interp-op (lookup i env) env)]
   [(num n) n]
   [(numV n) n]
   [(op f l) (interp-op (interp (op f l) env) env)]
    ))

;; Funcion auxiliar para obtener el param, body o env de un AST-Value
;; get-e: Binding string → (listof Binding)
(define (get-e Env orden)
  (match Env
    [(closureV param body env) (match orden
                                 ["param" param]
                                 ["body" body]
                                 ["env" env])]))