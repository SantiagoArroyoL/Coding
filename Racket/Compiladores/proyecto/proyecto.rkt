#lang nanopass

(require "LexerJly.rkt")
(require "ParserJly.rkt")
(require "middle-end.rkt")
(require "back-end.rkt")

(define (compila path)
  (let* ([input  (open-input-file path)]
         [output (open-output-file "output/parse.jly" #:exists 'truncate)] ;; 13.1.4 File Ports docs.racket
         [outputD (open-output-file "output/nanopass.jly" #:exists 'truncate)]
         [AST (jelly-parser (lex-this jelly-lexer input))]
         [str (string-append "(" (expr->string AST) ")")])
    (print AST output)
    (print str outputD)
    (close-input-port input)
    (close-output-port output)
    (close-output-port outputD)))

;; PRUEBAS
(define ejemplo '((main {(gdc 12 #t 3 4)})
              (gdc [(stmt int) (stmt2 bool) (stmt3 int) (stmt4 int)] bool {
                (f 1 2 3)
                (if #t #f #t) 
                (return stmt2)
              })
              (f [(stmt int) (b int) (x int)] int {
                        (while (!= stmt 0) {(if (< stmt b) (= b (- b stmt)) (= stmt (- stmt b)))})
                        (return b)
              }))
)

;;;;;;;;;;;;;;;;;
;Programa
(define (c-language-programa e)
  (nanopass-case (Jly Programa) e
                 [(,metodo* ...)
                  (let ([elements (string-join (map (lambda (x) (c-language-metodo x)) metodo*) " ")])
                        elements)]
                 [(,main_exp ,metodo* ...)
                  (let ([elements (string-join (map (lambda (x) (c-language-metodo x)) metodo*) " ")])
                        (string-append (c-language-main main_exp) elements))]
                 [else (error "Programa")]))

; Main
(define (c-language-main e)
  (nanopass-case (Jly MainExp) e
                 [(main ,bloque) 
                    (let ([bloqueC (c-language-bloque bloque)])
                         (string-append "int main() {\n" bloqueC "return 0;}"))]
                 [else (error "Main")]))

; Metodo
(define (c-language-metodo e)
  (nanopass-case (Jly Metodo) e
                 [(,i [ ,declaracion* ... ] ,t ,bloque)
                  (let ([iC (symbol->string i)]
                        [tC (symbol->string t)]
                        [declC (decl-aux declaracion*)]
                        [bloqueC (c-language-bloque bloque)])     
                    (string-append tC " " iC "(" declC ") {\n" bloqueC "}"))]
                 [else (error "Metodo")]))

; Bloque
(define (c-language-bloque e)
  (nanopass-case (Jly Bloque) e
      [{,sentencia* ... ,sentencia}
        (string-join (map (lambda (x) (c-language-aux x)) (append sentencia* (list sentencia))) " ")]
      [else (error "Bloque")]))

; Exp
(define (c-language-exp e)
  (nanopass-case (Jly Exp) e
                 [,i (symbol->string i)]
                 [,n (number->string n)]
                 [,b (~a b)]
                 [(,p ,exp1 ,exp2)
                    (string-append (c-language-exp exp1) (symbol->string p) (c-language-exp exp2))
                  ]
                 [(= (,i ,t) ,exp2)
                  (let ([iC (symbol->string i)]
                        [tC (symbol->string t)])
                    (string-append tC " " iC " = " (c-language-exp exp2) ";\n"))]
                 [(= ,i ,exp2)
                  (let ([iC (symbol->string i)])
                    (string-append iC " = " (c-language-exp exp2) ";\n"))]
                 [(- ,exp) (string-append "-" (c-language-exp exp))]
                 [(! ,exp) (string-append "!" (c-language-exp exp))]
                 [(return ,exp) (string-append "return " (c-language-exp exp) ";\n")]
                 [(,i  ,exp* ... ,exp )
                  (let ([iC (symbol->string i)]
                        [expC (string-join (map (lambda (x) (c-language-exp x)) (append exp* (list exp))) " ")])
                      (string-append iC "(" expC ");\n"))]
                 [else (error "Exp")]))

; Declaracion
(define (c-language-decl e)
  (nanopass-case (Jly Declaracion) e
                 [(,i ,t) (string-append (symbol->string t) " " (symbol->string i))]
                 [else (error "Decl")]))

; IfExp
(define (c-language-if e)
  (nanopass-case (Jly IfExp) e
                 [(if ,exp0 ,exp1 ,exp2)
                  (string-append "if (" (c-language-exp exp0) ") {\n"
                    (c-language-exp exp1) "} else {\n" (c-language-exp exp2) "}")]
                 [else (error "If")]))

; WhileExp
(define (c-language-while e)
  (nanopass-case (Jly WhileExp) e
                 [(while ,exp0 ,bloque)
                  (string-append "while (" (c-language-exp exp0) ") {\n" 
                    (c-language-bloque bloque) "}")]
                 [else (error "While")]))

;;;;;;;;;;;;;;;;;;;;;; FUNCIONES AUXILIARES ;;;;;;;;;;;;;;;;;;;;;;
;; Esta es como tal, la symbol table
(define (c-language e) (c-language-aux e))
; Redirige a casos no terminales
(define (c-language-aux e)
  (cond
    [(Jly-IfExp? e)       (c-language-if e)]
    [(Jly-Exp? e)         (c-language-exp e)]
    [(Jly-MainExp? e)     (c-language-main e)]
    [(Jly-Declaracion? e) (c-language-decl e)]
    [(Jly-WhileExp? e)    (c-language-while e)]
    [(Jly-Metodo? e)      (c-language-metodo e)]
    [(Jly-Bloque? e)      (c-language-bloque  e)]
    [(Jly-Programa? e)    (c-language-programa e)]
    [else (print "erroR")]))

;; Función auxiliar para dar formato a las sentencias
(define (saltos l)
  (if (equal? (length l) 1)
      (string-append "  " (first l) ";")
      (string-append "  " (car l) ";\n" (saltos (cdr l)))))

; Función auxiliar para poner comas "," entre declaraciones
(define (decl-aux l)
  (if (empty? (cdr l))
      (c-language-aux (car l))
      (string-append (c-language-aux (car l)) ", " (decl-aux (cdr l)))))


(define (prueba e)
  (let* ([parseado (parse-Jly e)]
         [renombrado (rename-var parseado)]
         [simbolos (symbol-table renombrado)])
    (type-check renombrado simbolos)))
    
(define (pruebaR e)
  (let* ([parseado (parse-Jly e)]
         [renombrado (rename-var parseado)])
    (c-language renombrado)))

;(compila "test-in.jly")
;; Si no lanza error, significa que pasamos la verificación de tipos.

(let ([output (open-output-file "output/example.c" #:exists 'truncate)] ;; 13.1.4 File Ports docs.racket
         [str (pruebaR ejemplo)])
    (display str)
    (write str output)
    (close-output-port output))
