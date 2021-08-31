#lang plai

;; Sintaxis Concreta
;; Lenguaje FWAE
;; <expr> ::= <id>
;;          | <num>
;;          | {+ <expr> <expr>}
;;          | {- <expr> <expr>}
;;          | {with {<id> <expr>} <expr>}
;;          | {fun {<id>} <expr>}
;;          | {<expr> <expr>}

;; Azúcar sintáctica
;; En este lenguaje consideramos a with azúcar sintáctica de una aplicación de función. Es decir,
;; la expresión:
;;
;; {with {id value} body}
;;
;; es semánticamente equivalente a:
;;
;; {{fun {id} body} value}
;;
;; Tarea Moral: Definir una función "desugar" que haga dicha transformación.

;; Sintaxis abstracta
(define-type ASA
  [id (i symbol?)]
  [num (n number?)]
  [add (i ASA?) (d ASA?)]
  [sub (i ASA?) (d ASA?)]
  [fun (param symbol?) (body ASA?)]
  [app (fun-expr ASA?) (arg ASA?)])

;; Valores para el regreso del intérprete.
(define-type ASA-Value
  [numV (n number?)]
  [closureV (param symbol?) (body ASA?) (env Env?)])

;; Ambientes de evaluación.
;; Almacenan parejas (id,valor)
(define-type Env
  [mtSub]
  [aSub (id symbol?) (value ASA-Value?) (rest-env Env?)])


;; lookup symbol Env -> ASA
;; Búsqueda de un id en el ambiente.
(define (lookup sub-id env)
  (match env
    [(mtSub) (error 'lookup "Variable libre")]
    [(aSub i v r)
        (if (equal? i sub-id)
            v
            (lookup sub-id r))]))

;; interp: ASA -> ASA
;; Intérprete para FAE, toma una expresión en sintaxis abstracta y nos devuelve el resultado de
;; evaluar dicha expresión.
(define (interp expr env)
  (match expr
    [(id i) (lookup i env)]
    [(num n) (numV n)]
    [(add i d) (numV (+ (numV-n (interp i env)) (numV-n (interp d env))))]
    [(sub i d) (numV (- (numV-n (interp i env)) (numV-n (interp d env))))]
    [(fun p b) (closureV p b env)]
    [(app f a)
        (let ([fun-val (interp f env)])
          (interp (closureV-body fun-val)
                  (aSub (closureV-param fun-val) (interp a env) (closureV-env fun-val))))]))

;; Prueba
;; {with {x 3}
;;    {with {f {fun {y} {+ x y}}
;;       {with {x 5}
;;           {f 4}}}}
(define e1 (app (fun 'x (app (fun 'f (app (fun 'x (app (id 'f) (num 4))) (num 5)))
     (fun 'y (add (id 'x) (id 'y))))) (num 3)))
