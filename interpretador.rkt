#lang eopl
;----------------------- Cristian Daniel Medina Ortiz - 2310117

;******************************************************************************************

;; La definición BNF para las expresiones del lenguaje:
;;
;;  <programa>      ::= <expresion>
;;                      un-programa (exp)
;;  <expresion>     ::= <numero>
;;                      numero-lit (datum)
;;                  ::= <identificador>
;;                      var-exp (id)
;;                  ::= (<expresion> <primitiva-binaria> <expresion>)
;;                       primapp-bin-exp (exp1 prim-binaria exp2)
;;
;;                  ::= <primitiva-unaria> (<expresion>)
;;                     primapp-un-exp (prim-unaria exp)
;;                  ::= Si <expresion> entonces <expresion> sino <expresion> finSI
;;                      si-exp (pred-exp true-exp false-exp)
;;                  ::= declarar (identifier = <expresion>)* { <expresion> }
;;                      variableLocal-exp (ids exps cuerpo)
;;                  ::= procedimiento (<identificador>*',') haga <expresion> finProc
;;                      procedimiento-ex (ids cuero)
;;                  ::=  "evaluar" expresion   (expresion ",")*  finEval
;;                        app-exp(exp exps)
;;                  ::= procRecursivo  {<identificador> "(" (<identificador>(,)) ")" "=>" <expresion>}* haga <expresion> finRec
;;                      procRec-exp (nombre ids cuerpo recursion)

;;  <primitiva-binaria> :=  + (primitiva-suma)
;;                      :=  ~ (primitiva-resta)
;;                      :=  / (primitiva-div)
;;                      :=  * (primitiva-multi)
;;                      :=  concat (primitiva-concat)

;;<primitiva-unaria>   :=  longitud (primitiva-longitud)
;;                     :=  add1 (primitiva-add1)
;;                     :=  sub1 (primitiva-sub1)



;****************************************************************************************** Lexica y la gramatica

; / 1. definir la lexica y la gramatica
;Especificación Léxica
(define scanner-spec
'((white-space (whitespace) skip)
  (comentario ("//" (arbno (not #\newline))) skip)
  
  (identificador ("@" letter (arbno (or letter digit "?"))) symbol)
  
  (texto (letter (arbno (or letter digit whitespace "_" "-" ":" "."))) string)
  (char ("'"(or letter digit)"'") string)
  
  (numero (digit (arbno digit)) number)
  (numero ("-" digit (arbno digit)) number)
  (numero (digit (arbno digit)) number)
  (numero (digit (arbno digit) "." digit (arbno digit)) number)
  (numero ("-" digit (arbno digit) "." digit (arbno digit)) number)))

;Especificación Sintáctica (gramática)

(define grammar
  '((programa (expresion) un-programa)

    ;;;Expresiones
    (expresion (numero) numero-lit)
    (expresion ("\""texto"\"") texto-lit)
    
    (expresion (identificador) var-exp)
    (expresion
     ("(" expresion primitiva-binaria expresion ")") primapp-bin-exp)
    (expresion
     (primitiva-unaria "(" expresion ")") primapp-un-exp)

    (expresion ("Si " expresion " entonces " expresion " sino " expresion " finSI") si-exp)
    (expresion ("declarar (" (separated-list identificador "=" expresion ";")  ")" "{" expresion "}") variableLocal-exp)
    (expresion ("procedimiento ("  (separated-list identificador ",") ")" " haga " expresion " finProc") procedimiento-exp)
    (expresion ("evaluar " expresion "(" (separated-list expresion ",") ")" " finEval") app-exp)
    (expresion ("declararRec (" (arbno identificador "=" "(" (separated-list identificador ",") ")" "=>" expresion ";") ")" "{" expresion "}") procRec-exp)

    ;;;;;;booleanos
    (expresion ("FALSE") bool-false)
    (expresion ("TRUE") bool-true)

    ;;;;;;Primitivas
    (primitiva-binaria ("+") primitiva-suma)
    (primitiva-binaria ("~") primitiva-resta)
    (primitiva-binaria ("*") primitiva-multi)
    (primitiva-binaria ("/") primitiva-div)
    (primitiva-binaria (" concat ") primitiva-concat)
    (primitiva-unaria ("longitud") primitiva-longitud)
    (primitiva-unaria ("add1") primitiva-add1)
    (primitiva-unaria ("sub1") primitiva-sub1)

    ;;;adicional
    (primitiva-binaria ("==") primitiva-igualdad)
    (primitiva-binaria ("!=") primitiva-diferencia)
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
(define interpretador
  (sllgen:make-rep-loop  "--> "
    (lambda (pgm) (eval-program  pgm))
    (sllgen:make-stream-parser scanner-spec grammar)))

;******************************************************************************************* Interprete

;;Ambiente inicial
(define init-env
  (lambda ()
    (extender-ambiente
     '(@a @b @c @d @e @PI)
     '(1 2 3 "hola" "FLP" 3.14159265359)
     (empty-env))))

;;Evaluar programa
(define eval-program
  (lambda (pgm)
    (cases programa pgm
      (un-programa (body)
                   (eval-expression body (init-env)))
      (else (eopl:error "ERROR")))))

;;Evaluar expresion
(define eval-expression
  (lambda (exp env)
    (cases expresion exp
      (numero-lit (num) num)
      (texto-lit (txt) txt)

      (var-exp (id) (buscar-variable env id));; buscar el valor en el ambiente
      (primapp-bin-exp (exp1 prim-binaria exp2) ((eval-binPrim prim-binaria) (eval-expression exp1 env) (eval-expression exp2 env)))
      (primapp-un-exp (prim-unaria exp) ((eval-unaPrim prim-unaria) (eval-expression exp env)))
      
      (si-exp (pred-exp true-exp false-exp)
              (if (valor-verdad? (eval-expression pred-exp env))
                  (eval-expression true-exp env)
                  (eval-expression false-exp env)))
      (variableLocal-exp (ids exps cuerpo)
                         (let ((args (list-exps exps env)))
                              (eval-expression cuerpo (extender-ambiente ids args env))))
      (procedimiento-exp (ids cuerpo) (cerradura ids cuerpo env))
      (app-exp (exp exps)
               (let ((proc (eval-expression exp env))
                     (args (list-exps exps env)))
                 (if (procVal? proc)
                     (aplicar-proc proc args)
                     (eopl:error 'eval-expression
                                 "Attempt to apply non-procedure ~s"))))
      (procRec-exp (nombres ids cuerpos recursion)
                   (eval-expression recursion
                                   (extender-ambiente-recursivo nombres ids cuerpos env)))
      (bool-false () #f)
      (bool-true () #t)
                     
      (else (eopl:error "ERROR"))
      )))

;******* primitivas
  
;obtener la operacion de  primitiva binaria
(define eval-binPrim 
  (lambda (prim)
    (cases primitiva-binaria prim
      (primitiva-suma () (lambda (val1 val2) (if (and (number? val1) (number? val2)) (+ val1 val2) (eopl:error 'primitiva-suma "Error, esta operacion solo permite numeros"))))
      (primitiva-resta () (lambda (val1 val2) (if (and (number? val1) (number? val2)) (- val1 val2) (eopl:error 'primitiva-resta "Error, esta operacion solo permite numeros"))))
      (primitiva-div () (lambda (val1 val2) (if (and (number? val1) (number? val2)) (/ val1 val2) (eopl:error 'primitiva-div "Error, esta operacion solo permite numeros"))))
      (primitiva-multi () (lambda (val1 val2) (if (and (number? val1) (number? val2)) (* val1 val2) (eopl:error 'primitiva-multi "Error, esta operacion solo permite numeros"))))
      (primitiva-concat () concat)

      (primitiva-igualdad () (lambda (val1 val2) (if (equal? val1 val2) 1 0)))
      (primitiva-diferencia () (lambda (val1 val2) (if (not (equal? val1 val2)) 1 0)))
      (else (eopl:error "ERROR")))))

;obtener la operacion de  primitiva unaria
(define eval-unaPrim 
  (lambda (prim)
    (cases primitiva-unaria prim
      (primitiva-longitud () (lambda (val) (if (string? val) (string-length val) (eopl:error 'longitud "Error, el valor no es una cadena de texto"))))
      (primitiva-add1 () (lambda (val) (if (number? val) (+ val 1) (eopl:error 'add1 "Error, el valor no es un numero"))))
      (primitiva-sub1 () (lambda (val) (if (number? val) (- val 1) (eopl:error 'sub1 "Error, el valor no es un numero"))))
      (else (eopl:error "ERROR"))
      )))
;******************************************************************************************* Ambientes
;Para cualquier valor de scheme retorna true
(define scheme-value? (lambda (v) #t))

;datatype de ambiente
(define-datatype ambiente ambiente?
  (vacio)
  (extendido
   (syms (list-of symbol?))
   (vec (list-of scheme-value?))
   (env ambiente?))
  (recursivo (nombres (list-of symbol?))
             (ids (list-of (list-of symbol?)))
             (cuerpo (list-of expresion?))
             (old-env ambiente?)))

;Ambiente vacío
(define empty-env  
  (lambda ()
    (vacio)))

;Extender ambiente
(define extender-ambiente
  (lambda (syms vals env)
    (extendido syms vals env)))

;Buscar un identificador en un ambiente
(define buscar-variable
  (lambda (env sym)
    (cases ambiente env
      (vacio () (eopl:error 'buscar-variable "Error, la variable no existe ~s" sym))
      (extendido (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (buscar-variable env sym))))
      (recursivo (nombres ids cuerpos old-env)
                             (let ((pos (list-find-position sym nombres)))
                                         (if (number? pos)
                                             (cerradura (list-ref ids pos)
                                                        (list-ref cuerpos pos)
                                                         env)
                                             (buscar-variable old-env sym)))))))

;Crea un ambiente extendido para procedimientos recursivos
(define extender-ambiente-recursivo
  (lambda (nombres ids cuerpos old-env)
    (recursivo nombres ids cuerpos old-env)))

;******************************************************************************************* Procedimientos
;Datatype Procedemiento
(define-datatype procVal procVal?
  (cerradura
   (lista-ID (list-of symbol?))
   (exp expresion?)
   (amb ambiente?)))

;Evalua las expresiones de un procedimiento en el ambiente extendido correspondiente
(define aplicar-proc
  (lambda (proc args)
    (cases procVal proc
      (cerradura (ids body env)
               (eval-expression body (extender-ambiente ids args env))))))


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
;declarar (
;  @radio=2.5;
;  @areaCirculo=procedimiento (@r) haga (@PI*(@r * @r)) finProc
;) { 
;    evaluar @areaCirculo (@radio) finEval  
;}

;B)
;declararRec ( 
;             @factorial=(@n) => Si @n entonces (@n * evaluar @factorial((@n ~ 1)) finEval) sino 1 finSI;
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


(interpretador)