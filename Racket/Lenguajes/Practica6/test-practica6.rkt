#lang plai

(print-only-errors)

(require "grammars.rkt")
(require "parser.rkt")
(require "desugar.rkt")
(require "interp.rkt")

;; Definiciรณn de expresiones.

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
(define expr16 '{fun {b h} {/ {* b h} 2}})
(define expr17 '{{fun {b h} {/ {* b h} 2}} 10 2})
(define expr18 '{{fun {p q} {if p p q}} true false})
(define expr19 '{{fun {p q} {if p q p}} false false})
(define expr20 '{{fun {x} {cond {{< x 10} 2} {{< x 20} 3} {else 4}}} 8})
(define expr21 '{{fun {x} {cond {{< x 10} 2} {{< x 20} 3} {else 4}}} 30})
(define expr22 '{not true})
(define expr23 '{with {{p true} {q false}} {not {and p {or p q}}}})
(define expr24 '{with* {{a 2} {b {/ a 0}}} 17})
(define expr25 '{{fun {x} 1} {sub1 {fun {x} x}}})
(define expr26 'empty)
(define expr27 '{list 1 2 3})
(define expr28 '{list {+ 2 3} {+ 5 2}})
(define expr29 '{rec {{fact {fun {n}
                         {if {zero? n}
                             1
                             {* n {fact {sub1 n}}}}}}}
                   {fact 5}})
(define expr30 '{rec {{len {fun {l}
                         {if {empty? l}
                             0
                             {+ 1 {len {cdr l}}}}}}}
                   {len {list 1 2 3}}})
(define expr31 '{car {list 1 2 3}})
(define expr32 '{empty? {list 1}})
(define expr33 '{cdr {list 1 2 3}})
(define expr34 '{rec {{longitud
                         {fun {l} 
                            {if {empty? l} 
                                0 
                                {+ 1 {longitud {cdr l}}}}}}
                      {suma
                         {fun {l}
                            {if {empty? l}
                                0
                                {+ {car l} {suma {cdr l}}}}}}
                      {lista {list 1 2 3}}}
       {+ {longitud lista} {suma lista}}})

;; Pruebas parser :: parse

(test (parse expr1) (idS 'foo))
(test (parse expr2) (numS 1729))
(test (parse expr3) (opS + (list (numS 1) (numS 2) (numS 3))))
(test (parse expr4) (opS - (list (numS 1) (numS 2) (numS 3))))
(test (parse expr5) (opS * (list (numS 1) (numS 2) (numS 3))))
(test (parse expr6) (opS / (list (numS 1) (numS 2) (numS 3))))
(test (parse expr7) (opS modulo (list (numS 9) (numS 3))))
(test (parse expr8) (opS expt (list (numS 2) (numS 3))))
(test (parse expr9) (opS add1 (list (numS 17))))
(test (parse expr10) (opS sub1 (list (numS 29))))
(test (parse expr11) 
      (withS (list (binding 'a (numS 2)) (binding 'b (numS 3))) (opS + (list (idS 'a) (idS 'b)))))
(test (parse expr12)
      (withS (list (binding 'a (numS 2)) (binding 'b (opS + (list (idS 'a) (idS 'a))))) (idS 'b)))
(test (parse expr13)
      (withS* (list (binding 'a (numS 2)) (binding 'b (opS + (list (idS 'a) (idS 'a))))) (idS 'b)))
(test (parse expr14)
      (withS (list (binding 'a (idS 'a))) (idS 'a)))
(test (parse expr15)
      (withS (list (binding 'b (idS 'a))) (idS 'a)))
(test (parse expr16)
      (funS '(b h) (opS / (list (opS * (list (idS 'b) (idS 'h))) (numS 2)))))
(test (parse expr17)
      (appS (parse expr16) (list (numS 10) (numS 2))))
(test (parse expr18)
      (appS (funS '(p q) (ifS (idS 'p) (idS 'p) (idS 'q))) (list (boolS #t) (boolS #f))))
(test (parse expr19)
      (appS (funS '(p q) (ifS (idS 'p) (idS 'q) (idS 'p))) (list (boolS #f) (boolS #f))))
(test (parse expr20)
      (appS (funS '(x) 
                  (condS (list (condition (opS < (list (idS 'x) (numS 10))) (numS 2)) 
                               (condition (opS < (list (idS 'x) (numS 20))) (numS 3))
                               (else-cond (numS 4)))))
            (list (numS 8))))
(test (parse expr21)
      (appS (funS '(x) 
                  (condS (list (condition (opS < (list (idS 'x) (numS 10))) (numS 2)) 
                               (condition (opS < (list (idS 'x) (numS 20))) (numS 3))
                               (else-cond (numS 4)))))
            (list (numS 30))))
(test (parse expr22) (opS not (list (boolS #t))))
#|
(test (parse expr23)
      (withS (list (binding 'p (boolS #t)) (binding 'q (boolS #f))) 
             (opS not 
                 (list (opS (elige 'and) (list (idS 'p) 
                       (opS (elige 'or) (list (idS 'p) (idS 'q)))))))))
|#
(test (parse expr24)
      (withS* (list (binding 'a (numS 2)) (binding 'b (opS / (list (idS 'a) (numS 0)))))
              (numS 17)))
(test (parse expr25)
      (appS (funS '(x) (numS 1)) (list (opS sub1 (list (funS '(x) (idS 'x)))))))
(test (parse expr26) (listS empty))
(test (parse expr27) (listS (list (numS 1) (numS 2) (numS 3))))
(test (parse expr28) 
      (listS (list (opS + (list (numS 2) (numS 3))) (opS + (list (numS 5) (numS 2))))))
(test (parse expr29)
      (recS (list (binding 'fact 
                            (funS '(n) 
                                  (ifS (opS zero? (list (idS 'n))) 
                                       (numS 1) 
                                       (opS * 
                                           (list (idS 'n) 
                                           (appS (idS 'fact) 
                                                 (list (opS sub1 (list (idS 'n))))))))))) 
            (appS (idS 'fact) (list (numS 5)))))
(test (parse expr30)
      (recS (list (binding 'len 
                            (funS '(l) 
                                  (ifS (opS empty? (list (idS 'l))) 
                                       (numS 0) 
                                       (opS + 
                                            (list (numS 1) 
                                                  (appS (idS 'len) 
                                                        (list (opS cdr (list (idS 'l))))))))))) 
            (appS (idS 'len) (list (listS (list (numS 1) (numS 2) (numS 3)))))))
(test (parse expr31) (opS car (list (listS (list (numS 1) (numS 2) (numS 3))))))
(test (parse expr32) (opS empty? (list (listS (list (numS 1))))))
(test (parse expr33) (opS cdr (list (listS (list (numS 1) (numS 2) (numS 3))))))
(test (parse expr34) 
      (recS (list (binding 'longitud 
                           (funS '(l) 
                                  (ifS (opS empty? (list (idS 'l))) 
                                       (numS 0) 
                                       (opS + 
                                           (list (numS 1)
                                                 (appS (idS 'longitud) 
                                                       (list (opS cdr (list (idS 'l))))))))))
                  (binding 'suma
                           (funS '(l)
                                  (ifS (opS empty? (list (idS 'l)))
                                       (numS 0)
                                      (opS +
                                          (list (opS car (list (idS 'l)))
                                                (appS (idS 'suma) 
                                                      (list (opS cdr (list (idS 'l))))))))))
                  (binding 'lista (listS (list (numS 1) (numS 2) (numS 3)))))
            (opS + 
                 (list (appS (idS 'longitud) (list (idS 'lista))) 
                       (appS (idS 'suma) (list (idS 'lista)))))))

;; Pruebas desugar :: desugar
(test (desugar (parse expr1)) (id 'foo))
(test (desugar (parse expr2)) (num 1729))
(test (desugar (parse expr3)) (op + (list (num 1) (num 2) (num 3))))
(test (desugar (parse expr4)) (op - (list (num 1) (num 2) (num 3))))
(test (desugar (parse expr5)) (op * (list (num 1) (num 2) (num 3))))
(test (desugar (parse expr6)) (op / (list (num 1) (num 2) (num 3))))
(test (desugar (parse expr7)) (op modulo (list (num 9) (num 3))))
(test (desugar (parse expr8)) (op expt (list (num 2) (num 3))))
(test (desugar (parse expr9)) (op add1 (list (num 17))))
(test (desugar (parse expr10)) (op sub1 (list (num 29))))
(test (desugar (parse expr11)) 
      (app (app (fun 'a (fun 'b (op + (list (id 'a) (id 'b))))) (num 2)) (num 3)))
(test (desugar (parse expr12)) 
      (app (app (fun 'a (fun 'b (id 'b))) (num 2)) (op + (list (id 'a) (id 'a)))))
(test (desugar (parse expr13)) 
      (app (fun 'a (app (fun 'b (id 'b)) (op + (list (id 'a) (id 'a))))) (num 2)))
(test (desugar (parse expr14)) (app (fun 'a (id 'a)) (id 'a)))
(test (desugar (parse expr15)) (app (fun 'b (id 'a)) (id 'a)))
(test (desugar (parse expr16)) 
      (fun 'b (fun 'h (op / (list (op * (list (id 'b) (id 'h))) (num 2))))))
(test (desugar (parse expr17))
      (app (app (fun 'b (fun 'h (op / (list (op * (list (id 'b) (id 'h))) (num 2))))) (num 10)) 
           (num 2)))
(test (desugar (parse expr18)) 
      (app (app (fun 'p (fun 'q (iF (id 'p) (id 'p) (id 'q)))) (bool #t)) (bool #f)))
(test (desugar (parse expr19)) 
      (app (app (fun 'p (fun 'q (iF (id 'p) (id 'q) (id 'p)))) (bool #f)) (bool #f)))
(test (desugar (parse expr20))
      (app (fun 'x 
                (iF (op < (list (id 'x) (num 10))) 
                    (num 2) 
                    (iF (op < (list (id 'x) (num 20))) (num 3) (num 4)))) 
           (num 8)))
(test (desugar (parse expr21))
      (app (fun 'x 
                (iF (op < (list (id 'x) (num 10))) 
                    (num 2) 
                    (iF (op < (list (id 'x) (num 20))) (num 3) (num 4)))) 
           (num 30)))
(test (desugar (parse expr22))
      (op not (list (bool #t))))
#|
(test (desugar (parse expr23)) 
      (app (app (fun 'p 
                     (fun 'q 
                          (op not 
                              (list (op (elige 'and) (list (id 'p) 
                                    (op (elige 'or) (list (id 'p) (id 'q))))))))) 
                (bool #t)) 
           (bool #f)))
|#
(test (desugar (parse expr24))
      (app (fun 'a (app (fun 'b (num 17)) (op / (list (id 'a) (num 0))))) (num 2)))
(test (desugar (parse expr25))
      (app (fun 'x (num 1)) (op sub1 (list (fun 'x (id 'x))))))
(test (desugar (parse expr26)) (lisT '()))
(test (desugar (parse expr27)) (lisT (list (num 1) (num 2) (num 3))))
(test (desugar (parse expr28)) 
      (lisT (list (op + (list (num 2) (num 3))) (op + (list (num 5) (num 2))))))
(test (desugar (parse expr29))
      (app (fun 'fact (app (id 'fact) (num 5))) 
           (app (id 'Y) 
                (fun 'fact 
                     (fun 'n 
                          (iF (op zero? (list (id 'n))) 
                              (num 1) 
                              (op * 
                                  (list (id 'n) 
                                        (app (id 'fact) 
                                             (op sub1 (list (id 'n))))))))))))
(test (desugar (parse expr30))
      (app (fun 'len (app (id 'len) (lisT (list (num 1) (num 2) (num 3))))) 
           (app (id 'Y) 
                (fun 'len 
                      (fun 'l 
                           (iF (op empty? (list (id 'l))) 
                               (num 0) 
                               (op + (list (num 1) (app (id 'len) (op cdr (list (id 'l))))))))))))
(test (desugar (parse expr31)) (op car (list (lisT (list (num 1) (num 2) (num 3))))))
(test (desugar (parse expr32)) (op empty? (list (lisT (list (num 1))))))
(test (desugar (parse expr33)) (op cdr (list (lisT (list (num 1) (num 2) (num 3))))))
(test (desugar (parse expr34))
      (app (fun 'longitud 
                (app (fun 'suma 
                           (app (fun 'lista 
                                     (op + 
                                         (list (app (id 'longitud) (id 'lista)) 
                                              (app (id 'suma) (id 'lista)))))
                                (app (id 'Y) (fun 'lista (lisT (list (num 1) (num 2) (num 3)))))))
                     (app (id 'Y) 
                          (fun 'suma 
                               (fun 'l 
                                    (iF (op empty? (list (id 'l))) 
                                        (num 0) 
                                        (op + 
                                           (list (op car (list (id 'l))) 
                                                 (app (id 'suma) 
                                                      (op cdr (list (id 'l))))))))))))
           (app (id 'Y) 
                (fun 'longitud 
                     (fun 'l 
                          (iF (op empty? (list (id 'l))) 
                              (num 0) 
                              (op + 
                                  (list (num 1) 
                                        (app (id 'longitud) (op cdr (list (id 'l))))))))))))

;; Pruebas interp :: call-interp
(test/exn (call-interp (desugar (parse expr1))) "Variable libre")
(test (call-interp (desugar (parse expr2))) (numV 1729))
(test (call-interp (desugar (parse expr3))) (numV 6))
(test (call-interp (desugar (parse expr4))) (numV -4))
(test (call-interp (desugar (parse expr5))) (numV 6))
(test (call-interp (desugar (parse expr6))) (numV 1/6))
(test (call-interp (desugar (parse expr7))) (numV 0))
(test (call-interp (desugar (parse expr8))) (numV 8))
(test (call-interp (desugar (parse expr9))) (numV 18))
(test (call-interp (desugar (parse expr10))) (numV 28))
(test (call-interp (desugar (parse expr11))) (numV 5))
(test (call-interp (desugar (parse expr12))) 
      (exprV (op + (list (id 'a) (id 'a))) 
             (aSub 'Y 
                   (exprV (fun 'f 
                              (app (fun 'x (app (id 'f) (app (id 'x) (id 'x)))) 
                                   (fun 'x (app (id 'f) (app (id 'x) (id 'x)))))) 
                          (mtSub)) 
                   (mtSub))))
(test (call-interp (desugar (parse expr13))) 
      (exprV (op + (list (id 'a) (id 'a))) 
             (aSub 'a 
                   (exprV (num 2) 
                          (aSub 'Y 
                                (exprV (fun 'f 
                                            (app (fun 'x (app (id 'f) (app (id 'x) (id 'x)))) 
                                                 (fun 'x (app (id 'f) (app (id 'x) (id 'x)))))) 
                                       (mtSub)) 
                                (mtSub))) 
                   (aSub 'Y 
                         (exprV (fun 'f 
                                     (app (fun 'x (app (id 'f) (app (id 'x) (id 'x)))) 
                                          (fun 'x (app (id 'f) (app (id 'x) (id 'x)))))) 
                                (mtSub)) 
                         (mtSub)))))
(test (call-interp (desugar (parse expr14))) 
      (exprV (id 'a) (aSub 'Y 
                           (exprV (fun 'f 
                                       (app (fun 'x (app (id 'f) (app (id 'x) (id 'x)))) 
                                            (fun 'x (app (id 'f) (app (id 'x) (id 'x)))))) 
                                  (mtSub)) 
                           (mtSub))))
(test/exn (call-interp (desugar (parse expr15))) "Variable libre")
(test (call-interp (desugar (parse expr16))) 
      (closureV 'b 
                (fun 'h (op / (list (op * (list (id 'b) (id 'h))) (num 2)))) 
                (aSub 'Y 
                      (exprV (fun 'f 
                                  (app (fun 'x (app (id 'f) (app (id 'x) (id 'x)))) 
                                       (fun 'x (app (id 'f) (app (id 'x) (id 'x)))))) 
                             (mtSub)) 
                      (mtSub))))
(test (call-interp (desugar (parse expr17))) (numV 10))
(test (call-interp (desugar (parse expr18))) 
      (exprV (bool #t) 
             (aSub 'Y 
                   (exprV (fun 'f 
                               (app (fun 'x (app (id 'f) (app (id 'x) (id 'x)))) 
                                    (fun 'x (app (id 'f) (app (id 'x) (id 'x)))))) 
                          (mtSub)) 
                   (mtSub))))
(test (call-interp (desugar (parse expr19))) 
      (exprV (bool #f) 
             (aSub 'Y 
                   (exprV (fun 'f 
                               (app (fun 'x (app (id 'f) (app (id 'x) (id 'x)))) 
                                    (fun 'x (app (id 'f) (app (id 'x) (id 'x)))))) 
                          (mtSub)) 
                   (mtSub))))
(test (call-interp (desugar (parse expr20))) (numV 2))
(test (call-interp (desugar (parse expr21))) (numV 4))
(test (call-interp (desugar (parse expr22))) (boolV #f))
(test (call-interp (desugar (parse expr23))) (boolV #f))
(test (call-interp (desugar (parse expr24))) (numV 17))
(test (call-interp (desugar (parse expr25))) (numV 1))
(test (call-interp (desugar (parse expr26))) (listV '()))
(test (call-interp (desugar (parse expr27))) (listV (list (numV 1) (numV 2) (numV 3))))
(test (call-interp (desugar (parse expr28))) (listV (list (numV 5) (numV 7))))
(test (call-interp (desugar (parse expr29))) (numV 120))
(test (call-interp (desugar (parse expr30))) (numV 3))
(test (call-interp (desugar (parse expr31))) (numV 1))
(test (call-interp (desugar (parse expr32))) (boolV #f))
(test (call-interp (desugar (parse expr33))) (listV (list (numV 2) (numV 3))))
(test (call-interp (desugar (parse expr34))) (numV 9))
