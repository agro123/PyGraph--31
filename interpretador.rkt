#lang eopl
;----------------------- Cristian Daniel Medina Ortiz - 2310117

;******************************************************************************************

;; La definición BNF para las expresiones del lenguaje:
;;
;;  <program>      ::= <expression>
;;                      un-program (exp)
;;  <expression>     ::= <number>
;;                      number-lit (datum)
;;                  ::= <identifier>
;;                      var-exp (id)
;;                  ::= (<expression> <prim-binary> <expression>)
;;                       primapp-bin-exp (exp1 prim-binaria exp2)
;;
;;                  ::= <prim-unary> (<expression>)
;;                     primapp-un-exp (prim-unaria exp)
;;                  ::= Si <expression> entonces <expression> sino <expression> finSI
;;                      if-exp (pred-exp true-exp false-exp)
;;                  ::= declarar (identifier = <expression>)* { <expression> }
;;                      const-exp (ids exps cuerpo)
;;                  ::= procedimiento (<identifier>*',') haga <expression> finProc
;;                      procedimiento-ex (ids cuero)
;;                  ::=  "evaluar" expression   (expression ",")*  finEval
;;                        app-exp(exp exps)
;;                  ::= procRecursivo  {<identifier> "(" (<identifier>(,)) ")" "=>" <expression>}* haga <expression> finRec
;;                      rec-exp (nombre ids cuerpo recursion)

;;  <prim-binary> :=  + (primitiva-suma)
;;                      :=  ~ (primitiva-resta)
;;                      :=  / (primitiva-div)
;;                      :=  * (primitiva-multi)
;;                      :=  concat (primitiva-concat)

;;<prim-unary>   :=  longitud (primitiva-longitud)
;;                     :=  add1 (primitiva-add1)
;;                     :=  sub1 (primitiva-sub1)



;****************************************************************************************** Lexica y la gramatica

; / 1. definir la lexica y la gramatica
;Especificación Léxica
(define scanner-spec
'((whitespace (whitespace) skip)
  (comment ("//" (arbno (not #\newline))) skip)
  
  (identifier ("@" letter (arbno (or letter digit))) symbol)
  
  (text (letter (arbno (or letter digit whitespace "_" "-" ":" "."))) string)
  (char ("'"(or letter digit)"'") symbol)
        
  (number (digit (arbno digit)) number)
  (number ("-" digit (arbno digit)) number)
  (number (digit (arbno digit)) number)
  (number (digit (arbno digit) "." digit (arbno digit)) number)
  (number ("-" digit (arbno digit) "." digit (arbno digit)) number)))

;Especificación Sintáctica (gramática)

(define grammar
  '((program (expression) un-program)

    ;;Identificador
    (expression (identifier) var-exp)

    ;;Definiciones
    (expression ("var (" (separated-list identifier "=" expression ",") ") in {" expression "}") variable-exp)
    (expression ("const (" (separated-list identifier "=" expression ",") ") in {" expression "}") const-exp)
    (expression  ("rec (" (arbno identifier "=" "(" (separated-list identifier ",") ")" "=>" "{" expression "}") ") in {" expression "}") rec-exp)
    
    ;;Datos
    (expression (number) number-lit)
    (expression (char) char-lit)
    (expression ("\""text"\"") text-lit)
    (expression ("true") bool-true-lit)
    (expression ("false") bool-false-lit)
    
    ;;Estructura de control
    (expression ("begin " "{" expression (arbno ";" expression) "}") begin-exp)
    (expression ("if (" expr-bool ")" " then {" expression "} else {" expression "}") if-exp)
    (expression ("func (" (separated-list identifier ",") ")" "{" expression "}") proc-exp)
    (expression ("resultOf " expression "(" (separated-list expression ",") ")") app-exp)
    (expression ("set " identifier "->" expression) set-exp)

    ;;Booleanos
    (expression (expr-bool) bool-exp)
    (expr-bool (oper-bin-bool "(" expression "," expression ")?") pred-bin-exp)
    (expr-bool (oper-un-bool "(" expr-bool ")?") pred-un-exp)
   
    ;;Predicados
    (oper-bin-bool ("==") pred-igualdad)
    (oper-bin-bool ("<>") pred-diferencia)
    (oper-bin-bool (">") pred-mayor-que)
    (oper-bin-bool ("<") pred-menor-que)
    (oper-bin-bool (">=") pred-mayor-igual-que)
    (oper-bin-bool ("<=") pred-menor-igual-que)
    (oper-bin-bool ("<=") pred-menor-igual-que)
    (oper-bin-bool ("and") pred-and)
    (oper-bin-bool ("or") pred-or)
    
    (oper-un-bool ("not") pred-not)

    ;;Primitivas
    (expression ("(" expression prim-binary expression ")") primapp-bin-exp)
    (expression (prim-unary "(" expression ")") primapp-un-exp)
    
    (prim-binary ("+") primitiva-suma)
    (prim-binary ("~") primitiva-resta)
    (prim-binary ("*") primitiva-multi)
    (prim-binary ("/") primitiva-div)
    (prim-binary ("%") primitiva-res)
    (prim-binary (" concat ") primitiva-concat)
    
    (prim-unary ("longitud") primitiva-longitud)
    (prim-unary ("add1") primitiva-add1)
    (prim-unary ("sub1") primitiva-sub1)
    ))

; 2. Crear los datatypes con sllgen

(sllgen:make-define-datatypes scanner-spec grammar)

(define show-datatypes
  (lambda () (sllgen:list-define-datatypes scanner-spec grammar))) ;;Visualizar los datatypes

;*******************************************************************************************
; 3. Parser, Scanner, Interfaz

;El FrontEnd (Análisis léxico (scanner) y sintáctico (parser) integrados)
(define scan&parse
  (sllgen:make-string-parser scanner-spec grammar)) ;;Convertir de concreta a abstracta



;El Analizador Léxico (Scanner)
(define just-scan
  (sllgen:make-string-scanner scanner-spec grammar)) ;; Visualizar los tokens

;Entrada de texto del interpretador
(define interpreter
  (sllgen:make-rep-loop  "--> "
    (lambda (pgm) (eval-program  pgm))
    (sllgen:make-stream-parser scanner-spec grammar)))

;******************************************************************************************* Interprete

;;Ambiente inicial
(define init-env
  (lambda ()
    (extend-env
     '(@a @b @c @d @e @PI)
     '(1 2 3 "hola" "FLP" 3.14159265359)
     (empty-enviroment))))

;;Evaluar programa
(define eval-program
  (lambda (pgm)
    (cases program pgm
      (un-program (body)
                   (eval-expression body (init-env)))
      (else (eopl:error "ERROR")))))

;;Evaluar expresion
(define eval-expression
  (lambda (exp env)
    (cases expression exp
      ;;Datos
      (number-lit (num) num)
      (char-lit (char) char)
      (text-lit (txt) txt)
      (bool-true-lit () #t)
      (bool-false-lit () #f)

      ;;Evaluar Identificadores
      (var-exp (id) (find-var env id))

      ;;Evaluar Definiciones
      (variable-exp (ids exps body)
                    (let ((args (list-exps exps env)))
                         (eval-expression body (extend-env-var ids args env))))
      (const-exp (ids exps body)
                 (let ((args (list-exps exps env)))
                      (eval-expression body (extend-env ids args env))))
      (rec-exp (procNames procParams procBodies exp)
               (eval-expression exp
                                (extend-env-rec procNames procParams procBodies env)))

      ;;Evaluar primitivas
      (primapp-bin-exp (exp1 prim-binaria exp2) ((eval-binPrim prim-binaria) (eval-expression exp1 env) (eval-expression exp2 env)))
      (primapp-un-exp (prim-unaria exp) ((eval-unaPrim prim-unaria) (eval-expression exp env)))

      ;;Evaluar estructuras de control
      (bool-exp (exp) (eval-boolean exp env))
      (set-exp (id new-exp)
               (begin
                  (setref!
                          (find-var-to-set env id)
                          (eval-expression new-exp env))
                   1))
      (begin-exp (exp exps) 
                 (let loop ((acc (eval-expression exp env)) (exps exps))
                      (if (null? exps) 
                           acc
                          (loop (eval-expression (car exps) env)
                                (cdr exps)))))
      (if-exp (pred-exp true-exp false-exp)
              (if (eval-boolean pred-exp env)
                  (eval-expression true-exp env)
                  (eval-expression false-exp env)))
      
      (proc-exp (ids cuerpo) (cerradura ids cuerpo env))
      (app-exp (exp exps)
               (let ((proc (eval-expression exp env))
                     (args (list-exps exps env)))
                 (if (procVal? proc)
                     (aplicar-proc proc args)
                     (eopl:error 'eval-expression
                                 "Attempt to apply non-procedure ~s"))))
                     
      (else (eopl:error "ERROR eval-expression"))
      )))
;***************************************************************************************** Predicados

;;Evaluar expresion booleana
(define eval-boolean
  (lambda (bool env)
    (cases expr-bool bool
      (pred-bin-exp (pred exp1 exp2) ((eval-pred-binary pred) (eval-expression exp1 env) (eval-expression exp2 env)))
      (pred-un-exp (pred exp1) ((eval-pred-unary pred) (eval-boolean exp1 env)))
      (else (eopl:error "ERROR eval-boolean")))))

;;Evaluar predicado binario
(define eval-pred-binary
  (lambda (pred)
    (cases oper-bin-bool pred
      (pred-igualdad () (lambda (val1 val2) (equal? val1 val2)))
      (pred-diferencia () (lambda (val1 val2) (not (equal? val1 val2))))
      (pred-mayor-que () (lambda (val1 val2) (> val1 val2)))
      (pred-menor-que () (lambda (val1 val2) (< val1 val2)))
      (pred-mayor-igual-que () (lambda (val1 val2) (>= val1 val2)))
      (pred-menor-igual-que () (lambda (val1 val2) (<= val1 val2)))
      (pred-and () (lambda (val1 val2) (and val1 val2)))
      (pred-or () (lambda (val1 val2) (or val1 val2)))
      (else (eopl:error "ERROR eval-pred-binary")))))

;;Evaluar predicado binario
(define eval-pred-unary
  (lambda (pred)
    (cases oper-un-bool pred
      (pred-not () (lambda (val) (not val)))
      (else (eopl:error "ERROR eval-pred-unary")))))
;****************************************************************************************** Primitivas
  
;obtener la operacion de  primitiva binaria
(define eval-binPrim 
  (lambda (prim)
    (cases prim-binary prim
      (primitiva-suma () (lambda (val1 val2) (if (and (number? val1) (number? val2)) (+ val1 val2) (eopl:error 'primitiva-suma "Error, esta operacion solo permite numeros"))))
      (primitiva-resta () (lambda (val1 val2) (if (and (number? val1) (number? val2)) (- val1 val2) (eopl:error 'primitiva-resta "Error, esta operacion solo permite numeros"))))
      (primitiva-div () (lambda (val1 val2) (if (and (number? val1) (number? val2)) (/ val1 val2) (eopl:error 'primitiva-div "Error, esta operacion solo permite numeros"))))
      (primitiva-multi () (lambda (val1 val2) (if (and (number? val1) (number? val2)) (* val1 val2) (eopl:error 'primitiva-multi "Error, esta operacion solo permite numeros"))))
      (primitiva-res () (lambda (val1 val2) (if (and (number? val1) (number? val2)) (remainder val1 val2) (eopl:error 'primitiva-res "Error, esta operacion solo permite numeros"))))
      (primitiva-concat () concat)
      (else (eopl:error "ERROR")))))

;obtener la operacion de  primitiva unaria
(define eval-unaPrim 
  (lambda (prim)
    (cases prim-unary prim
      (primitiva-longitud () (lambda (val) (if (string? val) (string-length val) (eopl:error 'longitud "Error, el valor no es una cadena de texto"))))
      (primitiva-add1 () (lambda (val) (if (number? val) (+ val 1) (eopl:error 'add1 "Error, el valor no es un numero"))))
      (primitiva-sub1 () (lambda (val) (if (number? val) (- val 1) (eopl:error 'sub1 "Error, el valor no es un numero"))))
      (else (eopl:error "ERROR"))
      )))
;******************************************************************************************* Ambientes
;Para cualquier valor de scheme retorna true
(define scheme-value? (lambda (v) #t))

;datatype de ambiente
(define-datatype environment environment?
  (empty-env)

  ;;Ambiente para constantes
  (extended-env (ids (list-of symbol?))
                (exps (list-of scheme-value?))
                (env environment?))
  ;;Ambiente para recursion
  (rec-env  (procNames (list-of symbol?))
            (procParams (list-of (list-of symbol?)))
            (procBodies (list-of expression?))
            (old-env environment?))
  ;;Ambiente para variables
  (var-env (ids (list-of symbol?))
           (exps vector?)
           (env environment?)))

;Ambiente vacío
(define empty-enviroment
  (lambda ()
    (empty-env)))

;Extender ambiente constantes
(define extend-env
  (lambda (syms vals env)
    (extended-env syms vals env)))

;Extender ambiente recursion
(define extend-env-rec
  (lambda (procNames procParams procBodies old-env)
    (rec-env procNames procParams procBodies old-env)))

;Extender ambiente variables
(define extend-env-var
  (lambda (ids exps env)
    (var-env ids (list->vector exps) env)))

;Buscar un identificador en un ambiente
(define find-var ;;apply-env
  (lambda (env id)
    (cases environment env
      (empty-env () (eopl:error 'find-var "Error, la variable ~s no existe" id))
      (extended-env (ids exps env)
                           (let ((pos (list-find-position id ids)))
                             (if (number? pos)
                                 (list-ref exps pos)
                                 (find-var env id))))
      (rec-env (procNames procParams procBodies old-env)
                             (let ((pos (list-find-position id procNames)))
                                         (if (number? pos)
                                             (cerradura (list-ref procParams pos)
                                                        (list-ref procBodies pos)
                                                         env)
                                             (find-var old-env id))))
      (var-env (ids exps env)
                           (let ((pos (list-find-position id ids)))
                             (if (number? pos)
                                 (deref (a-ref pos exps))
                                 (find-var env id)))))))
;;Buscar una variable para ser modificada
(define find-var-to-set ;;apply-env-ref
  (lambda (env id)
    (cases environment env
      (empty-env () (eopl:error 'find-var "Error, la variable ~s no existe " id))
      
      (extended-env (ids exps env)
                           (let ((pos (list-find-position id ids)))
                             (if (number? pos)
                                 (eopl:error 'find-var "Error, una constante no puede ser modificada ~s" id);; si la variable a modificar es una constante retorna un error
                                 (find-var-to-set env id))))
      (rec-env (procNames procParams procBodies old-env)
                             (let ((pos (list-find-position id procNames)))
                                         (if (number? pos)
                                             (eopl:error 'find-var "Error, un procemiento recursivo no puede ser modificado ~s" id);; si la variable a modificar es un procedimiento recursivo retorna un error
                                             (find-var old-env id))))
      (var-env (ids exps env)
                           (let ((pos (list-find-position id ids)))
                             (if (number? pos)
                                 (a-ref pos exps)
                                 (find-var-to-set env id)))))))
;*******************************************************************************************Referencias

;;Datatype referencia
(define-datatype reference reference?
  (a-ref (position integer?)
         (vec vector?)))

(define deref
  (lambda (ref)
    (primitive-deref ref)))

(define primitive-deref
  (lambda (ref)
    (cases reference ref
      (a-ref (pos vec)
             (vector-ref vec pos)))))

(define setref!
  (lambda (ref val)
    (primitive-setref! ref val)))

(define primitive-setref!
  (lambda (ref val)
    (cases reference ref
      (a-ref (pos vec)
             (vector-set! vec pos val)))))

;******************************************************************************************* Procedimientos
;Datatype Procedemiento
(define-datatype procVal procVal?
  (cerradura
   (lista-ID (list-of symbol?))
   (exp expression?)
   (amb environment?)))

;Evalua las expresiones de un procedimiento en el ambiente extendido correspondiente
(define aplicar-proc
  (lambda (proc args)
    (cases procVal proc
      (cerradura (ids body env)
               (eval-expression body (extend-env ids args env))))))


;****************************************************************************************  Funciones Auxiliares
; busca la posición de un símbolo en la lista de símbolos de un ambiente
(define list-find-position
  (lambda (sym los)
    (list-index (lambda (sym1) (eqv? sym1 sym)) los)))


(define list-index
  (lambda (pred ls)
    (cond
      ((null? ls) #f)
      ((pred (car ls)) 0)
      (else (let ((list-index-r (list-index pred (cdr ls))))
              (if (number? list-index-r)
                (+ list-index-r 1)
                #f))))))

;Recibe dos valores y retorna una string con su concatenacion
(define concat
  (lambda (val1 val2)
    (cond
      [(number? val1) (concat (number->string val1) val2)]
      [(number? val2) (concat val1 (number->string val2))]
      [(and (string? val1) (string? val2)) (string-append val1 val2)]
      [else (eopl:error 'concat "Error, los valores no son numeros o cadenas")] )))

;Validar si una expresion es verdadera o falsa
(define valor-verdad?
  (lambda (x)
    (not (zero? x))))

;Validar cada expresion en una lista
(define list-exps
  (lambda (exps env)
    (if(eqv? exps empty)
       '()
        (cons (eval-expression (car exps) env) (list-exps (cdr exps) env)))))


;------------------------------------------------Solucion taller------------------------------------------
;A)
;const (
;  @radio=2.5,
;  @areaCirculo= func (@r) { (@PI*(@r * @r)) }
;) in { 
;    resultOf @areaCirculo(@radio)
;}

;B)
;declararRec ( 
;             @factorial= (@n) => Si @n entonces (@n * evaluar @factorial((@n ~ 1)) finEval) sino 1 finSI;
;) {  
;    (("Factorial de 10 es " concat evaluar @factorial(10) finEval) concat ("y Factorial de 5 es " concat evaluar @factorial(5) finEval))
;}

;C)
;declararRec ( 
;        @sumar=(@n,@m) => Si @m entonces evaluar @sumar(add1(@n),sub1(@m)) finEval sino @n finSI;
;) {  
;    evaluar @sumar(4,5) finEval
;}

;D)
;declararRec ( 
;        @restar= (@a,@b) => Si (@b == 0) entonces @a sino evaluar @restar(sub1(@a),sub1(@b)) finEval finSI;
;        @multiplicar= (@a,@b) => Si (@b == 0) entonces 0 sino  (@a + evaluar @multiplicar(@a,sub1(@b)) finEval) finSI;
;) {  
;    (("Restar " concat evaluar @restar(10, 3) finEval) concat ("Multiplicar " concat evaluar @multiplicar(10, 3) finEval))
;}

;E)
;declarar (
;  @integrantes = procedimiento () haga "Cristian Medina" finProc;
;  @saludar = procedimiento (@proc) haga procedimiento () haga ("Hola " concat evaluar @proc() finEval ) finProc finProc
;) { 
;    declarar (
;         @decorate =  evaluar @saludar (@integrantes) finEval  
;    ) { 
;      evaluar @decorate () finEval
;    }
;}

;F)
;declarar (
;  @integrantes = procedimiento (@msf) haga ("Cristian Medina " concat @msf) finProc;
;  @saludar = procedimiento (@proc) haga procedimiento (@adc) haga ("Hola " concat evaluar @proc(@adc) finEval) finProc finProc
;) { 
;    declarar (
;         @decorate =  evaluar @saludar (@integrantes) finEval  
;    ) { 
;      evaluar @decorate ("estudiante de UNIVALLE") finEval
;    }
;}
(scan&parse "const (
  @radio=2.5,
  @areaCirculo= func (@r) { (@PI*(@r * @r)) }
) in { 
    resultOf @areaCirculo(@radio)
}")
(scan&parse "rec ( 
  @factorial=(@n)=> { if (==(@n,1)?) then {1} else {(@n * resultOf @factorial(sub1(@n)))} }
) in {  
    resultOf @factorial(10)
}")

(interpreter)