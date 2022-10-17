#|
Compiladores
Equipo: Compilelos
Integrantes:
  Arroyo Lozano Santiago
  Calvario González Berenice
  Liera Montaño Miguel Ángel
|#
#lang nanopass

(provide (all-defined-out))
(require parser-tools/lex
         (prefix-in : parser-tools/lex-sre)
         (prefix-in re- parser-tools/lex-sre)
         parser-tools/yacc)

(define-tokens contenedores (NUM VAR BOOL))

;; Definimos tokens
(define-empty-tokens vacios (SUM SUB PROD DIV AND OR IF THEN ELSE EOF
                             WHILE LP RP EQ NEQ LT GT LTE GTE T-BOOL LK RK
                             T-NUM NOT MOD ASSIGN OFTYPE COMMA LB RB RETURN))

;; La cadena vacía (transicion epsilon)
(define-lex-trans (epsilon stx)
  (syntax-case stx ()
    [(_) #'""]))

(define compilelos-lexer
  (lexer
    ; [Expresion Regular
     ; Token]

   ;; Espacios
   [(:or #\space #\tab #\newline) (compilelos-lexer input-port)]
   
   ;; Detecta el final de la cadena
   [(eof) (token-EOF)]

   ;; Numeros
   [(:: (:or #\- (epsilon)) (:+ (char-range #\0 #\9))) ; ([0..9])^+
     (token-NUM (string->number lexeme))]

   ;; Booleanos
   [(:: (:or (:: "True") (:: "true") (:: "false") (:: "False"))) ;; True | False
    (token-BOOL (match lexeme
                  ["True"  #t]
                  ["true"  #t]
                  ["False" #f]
                  ["false" #f]))]

   ;; Tipos
   [(:: "int") (token-T-NUM)]
   [(:: "boolean") (token-T-BOOL)]

   ;; Operadores
   [(:: "==") (token-EQ)]  
   [(:: #\<)  (token-LT)] 
   [(:: #\>)  (token-GT)]
   [(:: #\|)  (token-OR)]
   [(:: "!=") (token-NEQ)]
   [(:: "<=") (token-LTE)]
   [(:: ">=") (token-GTE)]
   [(:: #\+)  (token-SUM)]
   [(:: #\-)  (token-SUB)]
   [(:: #\/)  (token-DIV)]
   [(:: #\&)  (token-AND)]
   [(:: #\!)  (token-NOT)]
   [(:: #\%)  (token-MOD)]
   [(:: #\*)  (token-PROD)]

   ;; Puntuación
   [(:: #\=) (token-ASSIGN)]
   [(:: #\:) (token-OFTYPE)] 
   [(:: #\,) (token-COMMA)]  
   [(:: #\() (token-LP)]    
   [(:: #\)) (token-RP)]     
   [(:: #\{) (token-LB)]     
   [(:: #\}) (token-RB)]
   [(:: #\[) (token-RK)]
   [(:: #\]) (token-LK)]
    
   ;; Control de Flujo
   [(:: "return") (token-RETURN)] 
   [(:: "while")  (token-WHILE)] 
   [(:: "if")     (token-IF)]    
   [(:: "then")   (token-THEN)]   
   [(:: "else")   (token-ELSE)]

   ;; Variables
   ;; DEBE IR AL FINAL 
   [(:: (:: (char-range #\a #\z))
        (:* (:or #\_
                 (char-range #\a #\z)
                 (char-range #\0 #\9)
                 (char-range #\A #\Z)))) ;; ([a..z])([a..z] | [0..9] | _ | [A..Z])^*
    (token-VAR lexeme)]
   )
)

;; Función que devuelve el primer token correspondiente
;; al primer lexema de la cadena que recibe.
(define (tokeniza src)
  (let ((input (open-input-string src)))
    (compilelos-lexer input)))