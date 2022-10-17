#lang nanopass
(require  "ParserJly.rkt"
          "LexerJly.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Ejercicio 1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lex-this: text -> tokens
;; Recibe un lexer pa lexear
(define (lex-this lexer input) (lambda () (lexer input)))
;; parsea: path -> AST
;; Recibe una archivo o su ruta, toma su contenido y le aplica el parser ParserJLy.rkt
;; La salida sera a parse.jly
(define (parsea path)
  (let* ([input  (open-input-file path)]
         [output (open-output-file "parse.jly" #:exists 'truncate)] ;; 13.1.4 File Ports docs.racket
         [AST (jelly-parser (lex-this jelly-lexer input))])
    (print AST output)
    (close-input-port input)
    (close-output-port output))) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Ejercicio 2 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; expr->string: AST -> Nanopass
(define (expr->string e)
  (match e
    ['void ""] ; Termina cadena
    [(id e1) (symbol->string e1)]
    ['INT "int"]
    ['BOOL "bool"]
    [(bool "True") "#t"]
    [(bool "False") "#f"]
    [(num n) (number->string n)] 
    [(return e1) (string-append "return " (expr->string e1))]
    [(main e1) (string-append "(main {"(expr->string e1) "})")]
    [(un-exp '- e1) (string-append "(- " (expr->string e1)")")]
    [(un-exp '! e1) (string-append "(! " (expr->string e1) ")")]
    [(decl e1 e2) (string-append (expr->string e1) " " (expr->string e2))]
    [(llamada e1 e2) (string-append "(" (expr->string e1) " " (expr->string e2) ")")]
    [(bin-exp '= e1 e2) (string-append "(= " (expr->string e1) " " (expr->string e2) ")")]
    [(bin-exp '< e1 e2) (string-append "(< " (expr->string e1) " " (expr->string e2) ")")]
    [(bin-exp '> e1 e2) (string-append "(> " (expr->string e1) " " (expr->string e2) ")")]
    [(bin-exp '+ e1 e2) (string-append "(+ " (expr->string e1) " " (expr->string e2) ")")]
    [(bin-exp '- e1 e2) (string-append "(- " (expr->string e1) " " (expr->string e2) ")")]
    [(bin-exp '* e1 e2) (string-append "(* " (expr->string e1) " " (expr->string e2) ")")]
    [(bin-exp '/ e1 e2) (string-append "(/ " (expr->string e1) " " (expr->string e2) ")")]
    [(bin-exp '% e1 e2) (string-append "(% " (expr->string e1) " " (expr->string e2) ")")]
    [(bin-exp 'OR e1 e2) (string-append "(| " (expr->string e1) " " (expr->string e2) ")")]
    [(bin-exp '<= e1 e2) (string-append "(<= " (expr->string e1) " " (expr->string e2) ")")]
    [(bin-exp '>= e1 e2) (string-append "(>= " (expr->string e1) " " (expr->string e2) ")")]
    [(bin-exp 'AND e1 e2) (string-append "(& " (expr->string e1) " " (expr->string e2) ")")]
    [(bin-exp '== e1 e2) (string-append "(== " (expr->string e1) " " (expr->string e2) ")")]
    [(bin-exp '!= e1 e2) (string-append "(!= " (expr->string e1) " " (expr->string e2) ")")]
    [(while-exp e1 e2) (string-append "(while " (expr->string e1) " {" (map expr->string (flatten e2)) "})")]
    [(if-exp e1 e2 e3) (string-append "(if " (expr->string e1) " " (expr->string e2) " " (expr->string e2) ")")]
    [(metodo e1 e2 e3 e4) (string-append "(" (expr->string e1) " [" (string-join (map expr->string (flatten e2)) " ") "] " (expr->string e3) " {" (expr->string e4) "})")]
    [else (string-join (map expr->string (flatten e)) " ")] ; APlasta los ultimos casos
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Ejercicio 3 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Juicios para juzgar
(define (tipo? x) (memq x '(int bool)))
(define (constante? x) (or (number? x) (boolean? x)))
(define (reservada? x) (memq x '(return while if main)))
(define (primitive? x) (memq x '(+ - * / AND OR % == != < > >= <= !)))
(define (id? x)
  (if (symbol? x)
      (and (not (reservada? (symbol->string x)))
           (andmap (lambda (c) (or (char-numeric? c) (char-alphabetic? c) (eq? c #\_)))
                   (string->list (symbol->string x)))) #f))
; Lenguaje
(define-language Jly
  (terminals (id (i)) (tipo (t)) (constante (c)) (primitive  (p))) ; Nuestros simbolos terminales
  ; Clausulas no terminales:
  (Programa (programa) (main_exp metodo* ...) (metodo* ...))
  (MainExp (main_exp) (main bloque))
  (Metodo (metodo) (i [declaracion* ...] t bloque))
  (Bloque (bloque) {sentencia* ... sentencia})
  (Sentencia (sentencia) while_exp if_exp exp declaracion)
  (Exp (exp) c i ; Const, id
    (p exp1 exp2) ; op - primitiva
    (= (i t) exp2) ; eq
    (= i exp2)  ; asig
    (- exp) ; sub
    (! exp) ; not
    (return exp) ;return
    (i (exp* ... exp))) ; decl 
  (Declaracion (declaracion) (i t)) 
  (IfExp (if_exp) (if exp1 exp2 exp3)) 
  (WhileExp (while_exp) (while exp1 bloque)))