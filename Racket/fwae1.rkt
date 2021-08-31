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

;; Sintaxis Abstracta
(define-type ASA
  [id (i symbol?)]
  [num (n number?)]
  [add (i ASA?) (d ASA?)]
  [sub (i ASA?) (d ASA?)]
  [with (id symbol?) (value ASA?) (body ASA?)]
  [fun (param symbol?) (body ASA?)]
  [app (fun-expr ASA?) (arg ASA?)])

;; interp: ASA -> ASA
;; Intérprete para FWAE, toma una expresión en sintaxis abstracta y nos devuelve el resultado de
;; evaluar dicha expresión.
(define (interp expr)
  (match expr
    [(id i)
        (error 'interp "Variable libre")]
    [(num n)
        (num n)]
    [(add i d)
        (num (+ (num-n (interp i)) (num-n (interp d))))]
    [(sub i d)
        (num (- (num-n (interp i)) (num-n (interp d))))]
    [(with id value body)
        (interp (subst body id (interp value)))]
    [(fun param body)
        (fun param body)]
    [(app fun-expr arg)
        (interp (subst (fun-body fun-expr) (fun-param fun-expr) (interp arg)))]))

;; subst: ASA symbol ASA -> ASA
;; Algoritmo de sustitución modificado para soportar funciones y aplicaciones de función.
(define (subst expr sub-id val)
  (match expr
    [(id i)
        (if (equal? i sub-id) val expr)]
    [(num n)
        expr]
    [(add i d)
        (add (subst i sub-id val) (subst d sub-id val))]
    [(sub i d)
        (sub (subst i sub-id val) (subst d sub-id val))]
    [(with id value body)
        (if (equal? id sub-id)
            (with id (subst value sub-id val) body)
            (with id (subst value sub-id val) (subst body sub-id val)))]
    [(fun param body)
        (if (equal? param sub-id)
            expr
            (fun param (subst body sub-id val)))]
    [(app fun-expr arg)
        (app (subst fun-expr sub-id val)
             (subst arg sub-id val))]))

;; Prueba
;; {with {x 3}
;;    {with {f {fun {y} {+ x y}}
;;       {with {x 5}
;;           {f 4}}}}
(define expr1 (with 'x (num 3) (with 'f (fun 'y (add (id 'x) (id 'y))) (with 'x (num 5) (app (id 'f) (num 4))))))

