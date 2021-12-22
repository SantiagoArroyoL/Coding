#lang plai

(print-only-errors)

(require "grammars.rkt")
(require "parser.rkt")
(require "interp.rkt")

;; Definición de expresiones.

(define expr1  'foo)
(define expr2  1729)
(define expr3  '{+ 1 2 3})
(define expr4  '{- 1 2 3})
(define expr5  '{* 1 2 3})
(define expr6  '{/ 1 2 3})
(define expr7  '{modulo 9 3})
(define expr8  '{expt 2 3})
(define expr9  '{add1 17})
(define expr10 '{sub1 29})
(define expr11 '{with {{a 2} {b 3}}
                  {+ a b}})
(define expr12 '{with {{a 2} {b {+ a a}}}
                  b})
(define expr13 '{with* {{a 2} {b {+ a a}}}
                  b})
(define expr14 '{with {{a a}}
                  a})
(define expr15 '{with {{b a}}
                  a})

;; Pruebas parser :: parse

(test (parse expr1) (id 'foo))
(test (parse expr2) (num 1729))
(test (parse expr3) (op + (list (num 1) (num 2) (num 3))))
(test (parse expr4) (op - (list (num 1) (num 2) (num 3))))
(test (parse expr5) (op * (list (num 1) (num 2) (num 3))))
(test (parse expr6) (op / (list (num 1) (num 2) (num 3))))
(test (parse expr7) (op modulo (list (num 9) (num 3))))
(test (parse expr8) (op expt (list (num 2) (num 3))))
(test (parse expr9) (op add1 (list (num 17))))
(test (parse expr10) (op sub1 (list (num 29))))
(test (parse expr11) 
   (with (list (binding 'a (num 2)) (binding 'b (num 3))) (op + (list (id 'a) (id 'b)))))
(test (parse expr12)
   (with (list (binding 'a (num 2)) (binding 'b (op + (list (id 'a) (id 'a))))) (id 'b)))
(test (parse expr13)
   (with* (list (binding 'a (num 2)) (binding 'b (op + (list (id 'a) (id 'a))))) (id 'b)))
(test (parse expr14)
   (with (list (binding 'a (id 'a))) (id 'a)))
(test (parse expr15)
   (with (list (binding 'b (id 'a))) (id 'a)))

;; Pruebas interp :: subst

(test (subst (parse expr1) 'foo (num 2)) (num 2))
(test (subst (parse expr1) 'bar (num 2)) (parse expr1))
(test (subst (parse expr2) 'foo (num 2)) (parse expr2))
(test (subst (parse expr3) 'foo (num 2)) (parse expr3))
(test (subst (parse expr4) 'foo (num 2)) (parse expr4))
(test (subst (parse expr5) 'foo (num 2)) (parse expr5))
(test (subst (parse expr6) 'foo (num 2)) (parse expr6))
(test (subst (parse expr7) 'foo (num 2)) (parse expr7))
(test (subst (parse expr8) 'foo (num 2)) (parse expr8))
(test (subst (parse expr9) 'foo (num 2)) (parse expr9))
(test (subst (parse expr10) 'foo (num 2)) (parse expr10))
(test (subst (parse expr11) 'foo (num 2)) (parse expr11))
(test (subst (parse expr11) 'a (num 2)) (parse expr11))
(test (subst (parse expr11) 'b (num 2)) (parse expr11))
(test (subst (parse expr12) 'foo (num 2)) (parse expr12))
(test (subst (parse expr12) 'a (num 2)) 
   (with (list (binding 'a (num 2)) (binding 'b (op + (list (num 2) (num 2))))) (id 'b)))
(test (subst (parse expr12) 'b (num 2)) (parse expr12))
(test (subst (parse expr13) 'foo (num 2)) (parse expr13))
(test (subst (parse expr13) 'a (num 2)) 
   (with* (list (binding 'a (num 2)) (binding 'b (op + (list (num 2) (num 2))))) (id 'b)))
(test (subst (parse expr13) 'b (num 2)) (parse expr13))
(test (subst (parse expr14) 'a (num 2)) (with (list (binding 'a (num 2))) (id 'a)))
(test (subst (parse expr15) 'a (num 2)) (with (list (binding 'b (num 2))) (num 2)))

;; Pruebas interp :: interp

(test/exn (interp (parse expr1)) "Variable libre")
(test (interp (parse expr2)) 1729)
(test (interp (parse expr3)) 6)
(test (interp (parse expr4)) -4)
(test (interp (parse expr5)) 6)
(test (interp (parse expr6)) 1/6)
(test (interp (parse expr7)) 0)
(test (interp (parse expr8)) 8)
(test (interp (parse expr9)) 18)
(test (interp (parse expr10)) 28)
(test (interp (parse expr11)) 5)
(test/exn (interp (parse expr12)) "Variable libre")
(test (interp (parse expr13)) 4)
(test/exn (interp (parse expr14)) "Variable libre")
(test/exn (interp (parse expr15)) "Variable libre")
