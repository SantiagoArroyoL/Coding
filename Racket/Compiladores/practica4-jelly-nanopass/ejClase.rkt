#lang nanopass

(require  "ParserJly.rkt"
          "LexerJly.rkt")

;Completar esto para el ejercicio 2
(define (expr->string e)
  (match e
    [(num n) (number->string n)]
    [(bool "True") "#t"]
    [(bool "False") "#f"]
    ))

;Completar esto para el ejercicio 3
(define-language Jly
    (terminals
        (primitive (pr))
        (constante (c))
        )
    (Expr (e body)
        c
        (pr e* ... e)))

; Juicios para identificar una operacion primitiva o una constante.
(define (constante? x) (or (number? x) (boolean? x)))
(define (primitive? x) (memq x '(+ - * / and or % == != < > >= <= !)))


#| AQUI SE GENERA UN ERROR PORQUE EL SIMBOLO INICIAL DEL PARSER BUSCA UN METODO,
 Y 4-5 CLARAMENTE NO ES UN METODO, SI QUIERES QUE FUNCIONE CAMBIA EL SIMBOLO
 INICIAL DEL PARSER DE programa A exp |#
(define (lex-this lexer input) (lambda () (lexer input)))
(let ([input (open-input-string "4 - 5")])
  (expr->string (jelly-parser (lex-this jelly-lexer input))))

(define-parser parse-Jly Jly)
(println (parse-Jly '(+ 1 2 3 4 4 5 6)))