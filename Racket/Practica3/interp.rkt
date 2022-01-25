#lang plai

(require "grammars.rkt")
(require "parser.rkt")

;; Algoritmo de sustitución.
;; subst: AST symbol AST → AST
(define (subst expr sub-id value)
<<<<<<< HEAD
  "escribe aquí tu código")


=======
  (match expr
    [(id i) (if (eq? i sub-id) value (id i))]
    [(num n) (num n)]
    [(op f l) (op f (map (lambda (x) (subst x sub-id value)) l))]
    [(with bindings body) (with (subst-bin bindings sub-id value) (subst-withs-body bindings body sub-id value))]
    [(with* bindings body) (with* (subst-withs-id bindings sub-id value) (subst-withs-body bindings body sub-id value))]))

;; Función auxiliar que realiza la sustitución para with y with* en el body
;; subst-withs: (listof Binding) AST symbol AST-> AST
(define (subst-withs-body bindings body sub-id value)
  (if (busca-bin bindings sub-id)
       body                       ;;Si encuentra el binding con el mismo id dejamos el body como esta
      (subst body sub-id value))) ;; Si no, sustituimos el valor en el body

;; Función auxiliar que realiza la sustitución para with* en el id
;; subst-withs: (listof Binding) AST symbol AST-> AST
(define (subst-withs-id bindings sub-id value)
  (if (busca-bin bindings sub-id)
      (subst-bin-especial bindings sub-id value) ;;Si encuentra el binding con el mismo id, sustituimos el valor de ese binding
      (subst-bin bindings sub-id value)))        ;; Si no, sustituimos en el valor de todos los bindings


;; Funcion auxiliar que nos dice si un binding en una lista tiene el mismo id
;; busca-bin: (listof Binding) symbol → bool
(define (busca-bin bindings sub-id)
 (cond
  [(empty? bindings) false]
  [(eq? (match (car bindings) [(binding id ast) id]) sub-id) true]
  [else (busca-bin (cdr bindings) sub-id)]))


;; Funcion auxiliar que sustituye los valores de todos los bindings
;; subst-bin: (listof Binding) symbol AST → (listof Binding)
(define (subst-bin bindings sub-id value)
   (if (null? bindings)
       '()
       (cons (sust-ast (first bindings) sub-id value) (subst-bin (cdr bindings) sub-id value))))

;; Funcion auxiliar que sustituye los valores de todos los bindings,
;; pero si encuentra uno con el mismo id, sustituye en el valor de ese y regresa los demás bindings sin sustituir
;; subst-bin-especial: (listof Binding) symbol AST → (listof Binding)
(define (subst-bin-especial bindings sub-id value)
   (if (null? bindings)
       '()
       (if (eq? (get-b (first bindings) "id") sub-id)
           (cons (sust-ast (first bindings) sub-id value) (cdr bindings))
           (cons (sust-ast (first bindings) sub-id value) (subst-bin-especial (cdr bindings) sub-id value)))))

;; Funcion auxiliar que hace sustitución en el valor (ast) de un binding
;; sust-ast: Binding symbol AST → Binding
(define (sust-ast bind sub-id value)
  (match bind
    [(binding id ast) (binding id (subst ast sub-id value))]))
>>>>>>> 6e2f26b43cd0de96a071965e63b0233127a06f79

 ;;Análisis semántico
 ;;interp: AST → number
(define (interp expr)
<<<<<<< HEAD
  "escribe aquí tu codigo")

=======
 (match expr
   [(id i) (error 'interp "Variable libre")]
   [(num n) n]
   [(op f l) (evalua-op f l)]
   [(with bindings body) (interp (realiza-with body bindings))]
   [(with* bindings body) (interp (realiza-with body (bindings-with* bindings)))]
    ))

;; Funcion auxiliar para interpretar operaciones
;; evalua-op: (listof Binding) symbol AST → (listof Binding)
(define (evalua-op f l)
  (cond
    [(eq? f +) (if (null? l) 0 (+ (interp (car l)) (evalua-op + (cdr l))))]
    [(eq? f -) (if (null? l) 0 (- (interp (car l)) (evalua-op + (cdr l))))]
    [(eq? f *) (if (null? l) 1 (* (interp (car l)) (evalua-op * (cdr l))))]
    [(eq? f /) (if (null? l) 1 (/ (interp (car l)) (evalua-op * (cdr l))))]
    [(eq? f modulo) (modulo (interp (car l)) (interp (car (cdr l))))]
    [(eq? f expt) (expt (interp (car l)) (interp (car (cdr l))))]
    [(eq? f add1) (+ (interp (car l)) 1)]
    [(eq? f sub1) (- (interp (car l)) 1)]
  ))

;; Funcion auxiliar para obtener el id o value de un binding
;; get-b: Binding string → (listof Binding)
(define (get-b bind orden)
  (match bind
    [(binding id ast) (if (eq? orden "id") id ast)]))

;; Funcion auxiliar que aplica todos los bindings al body de un with
;; realiza-with: (listof Binding) symbol AST → (listof Binding)
(define (realiza-with body bindings)
  (if (null? bindings) body (realiza-with (subst body (get-b (car bindings) "id") (get-b (car bindings) "value")) (cdr bindings))))

;; Funcion auxiliar que hace sustitucion de los bindings si los encuentra
;; bindings-with*: (listof Binding) → (listof Binding)
(define (bindings-with* l)
  (if (null? l)
       '()
       (cons (car l) (bindings-with* (subst-bin (cdr l) (get-b (car l) "id") (get-b (car l) "ast"))))))
>>>>>>> 6e2f26b43cd0de96a071965e63b0233127a06f79
