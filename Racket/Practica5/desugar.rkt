#lang plai

;;(require "parser.rkt")
(require "grammars.rkt")

;; Elimina el azúcar sintáctica de las expresiones FWAE.
;; desugar: SAST → AST
(define (desugar expr)
  (match expr
    [(idS i) (id i)]
    [(numS n) (num n)]
    [(boolS b) (bool b)]
    [(opS f args) (op f (desugar-lis args))]
    [(withS bindings body) (conv-a-app bindings (conv-a-fun bindings (desugar body)))] ;;tenemos que hacer funcion auxiliar para hacer desugar a lista d bindings
    [(withS* bindings body) (conv-app-fun bindings (desugar body))]
    [(funS params body) (conv-ff params (desugar body))]
    [(appS fun-expr args) (conv-aapp (desugar fun-expr) args)]
    [(ifS test-expr then-expr else-expr) (iF (desugar test-expr) (desugar then-expr) (desugar else-expr))]
    [(condS cases) (conv-cond-if cases)]))

;; Funcion auxiliar que hace desugar en listas de SAST
;; desugar-lis: (listof SAST) -> (listof AST)
(define (desugar-lis l)
  (if (null? l)
      '()
      (cons (desugar (car l)) (desugar-lis (cdr l)))))

;; Funcion auxiliar que convierte expresiones de with a fun con los simbolos en la lista de bindings del with
;; conv-a-fun: (listof binding) -> AST -> fun
(define (conv-a-fun bindings body)
  (if (null? bindings)
      body
      (conv-a-fun (drop-right bindings 1) (fun (get-b (last bindings) "id") body))))

;; Funcion auxiliar que convierte expresiones de fun a app con el value de los simbolos en la lista de bindings del with
;; conv-a-app: (listof binding) -> fun -> app
(define (conv-a-app bindings fu)
  (if (null? bindings)
      fu
      (conv-a-app (cdr bindings) (app fu (desugar(get-b (car bindings) "sast"))))))

;; Funcion auxiliar que convierte expresiones de with* a app con los simbolos y values en la lista de bindings del with*
;; conv-app-fun: (listof binding) -> AST -> fun
(define (conv-app-fun bindings body)
  (if (null? bindings)
      body
      (conv-app-fun (drop-right bindings 1) (app (fun (get-b (last bindings) "id") body) (desugar(get-b (last bindings) "sast"))))))

;; Funcion auxiliar para obtener el id o value de un binding
;; get-b: Binding string → (listof Binding)
(define (get-b bind orden)
  (match bind
    [(binding id sast) (if (eq? orden "id") id sast)]))

;; Funcion auxiliar que convierte expresiones de funS a fun con los simbolos en la lista de parametros del funS
;; conv-ff: (listof symbol) -> AST -> fun
(define (conv-ff params body)
  (if (null? params)
      body
      (fun (car params) (conv-ff (cdr params) body))))

;; Funcion auxiliar que convierte expresiones de funS a fun con los simbolos en la lista de parametros del funS
;; conv-aapp: (listof symbol) -> AST -> fun
(define (conv-aapp fun-exp args)
  (if (null? args)
      fun-exp
      (conv-aapp (app fun-exp (desugar (car args))) (cdr args))))

;; Funcion auxiliar que convierte expresiones de condS a iF anidados
;; conv-cond-if: (listof symbol) -> AST -> iF
(define (conv-cond-if cases)
  (match (car cases)
    [(condition test-expr then-expr) (iF (desugar test-expr) (desugar then-expr) (conv-cond-if (cdr cases)))]
    [(else-cond else-expr) (desugar else-expr)]))
      