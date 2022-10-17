#lang plai

(require "grammars.rkt")
(require "parser.rkt")
(require "desugar.rkt")
(require "interp.rkt")

;; Función que saca valores de los respectivos constructores para mostrarlos al usuario.
;; desencapsula: AST-Value → string
(define (desencapsula expr)
  (match expr
    [(numV n)
       (number->string n)]
    [(boolV b)
       (if b "true" "false")]
    [(closureV _ _ _) 
       "#<procedure>"]))

;; Función encargada de ejecutar el intérprete para que el usuario interactúe con el lenguaje. Para
;; diferenciar el prompt de Racket del nuestro, usamos "(λ)". Aprovechamos los aspectos imperativos
;; del lenguaje para esta función.
;; ejecuta: void
(define (ejecuta)
   (begin
      (display "(λ) ")
      (define x (read))
      (if (equal? x '{exit})
          (display "")
          (begin 
            (with-handlers ([exn:fail? (lambda (exn) (display (exn-message exn)))]) 
               (display (desencapsula (strict (interp (desugar (parse x)) (mtSub))))))
            (display "\n")
            (ejecuta)))))

;; Llamada a la función
(ejecuta)
