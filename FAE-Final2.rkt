#lang play
;(print-only-errors #f) ; Para ver solo los errores.

#|
<FAE-L> ::=   <num> | <bool> | <id>
            | (+ <FAE> <FAE>)
            | (- <FAE> <FAE>)
            | (if-tf <FAE> <FAE> <FAE>)
            | (with <id> <FAE> <FAE>)
            | (app <FAE> <FAE>) ; puedo aplicar una funcion a otra funcion / puedo usar una funcion como argumento. 
            | (fun <id> <FAE>) ; fun(que es una lambda) nombre-arg body
|#


(deftype Expr
  [num n]                                 ; <num>
  [bool b]                                ; <bool>
  [str s]
  [zero n]
  [if-tf c et ef]                         ; (if-tf <FAE> <FAE> <FAE>)
  [array expr]
; [with id-name named-expr body-expr]     ; (with <id> <FAE> <FAE>) "syntax sugar"
  [id name]                               ; <id> 
  [app fname arg-expr]                    ; (app <FAE> <FAE>) ; ahora podemos aplicar una funcion a otra
  [prim name args]
  [fun arg body]
  [delay expr]
  [force expr]
  [seqn expr-list]
)

(define primitives
  (list (cons '+ +)
        (cons '- -)
        (cons '* *)
        (cons '/ /)
        (cons '< <)
        (cons '> >)
        (cons '== eq?)
        (cons '!= (λ (h t) (not (eq? h t))))
        (cons '<= <=)
        (cons '>= >=)
        (cons '&&  (λ (h t) (and  h t)))
        (cons '|| (λ (h t) (or  h t)))
        (cons 'kar (λ (h t) (car h t)))
        (cons 'qdr (λ (h t) (cdr h t)))
        )
  )

;prim-ops: name args -> val
(define (prim-ops name args)
  (let ([vals (map (λ (x) (valV-v x)) args)])
    (valV (apply (cdr (assq name primitives)) vals ))
    )
  )

#|
<env> ::= (mtEnv)
          | (aEnv <id> <val> <env>)
|#
(deftype Env
  (mtEnv)
  (aEnv id val env)
  )

; empty-env -> (mtEnv)
(define empty-env (mtEnv))

; extend-env:: <id> <val> <env> -> <env>
(define extend-env aEnv)
; env-lookup :: <id> <env> -> <val>
; buscar el valor de una variable dentro del ambiete
(define (env-lookup x env)
  (match env
    [(mtEnv) (error "undefined: " x)]
    [(aEnv id val tail)(if (eq? id x) val (env-lookup x tail))]
    )
  )


; transform-fundef
(define (transform-fundef arg-names body)
  (if (= 1 (length arg-names))
      (fun (first arg-names) body)
      (fun (first arg-names) (transform-fundef (cdr arg-names) body)))
  )
; (transform-fundef '{a b} (add (id 'a) (id 'b)))


; transform-funapp
(define (transform-funapp fun args)
  (if (= 1 (length args))
      (app fun (first args))
      (app (transform-funapp fun (cdr args)) (car args)))
  )

; parse: Src -> Expr
; parsea codigo fuente
(define (parse src)
  (match src
    [(? number?) (num src)]
    [(? boolean?) (bool src)]
    [(? symbol?) (id src)]
    [(? string? s) (str s)]
    [(list 'array expr)(array (map parse expr))]
    [(list 'zero?? n) (zero (parse n))]
    [(list 'if-tf c et ef) (if-tf (parse c) (parse et) (parse ef))]
    [(list 'with (cons (list x e) tail) body) (parse (list 'with (list x e)
                                                           (cond [(empty? tail) body]
                                                                 [(list 'with tail body)]
                                                                 )))]
    [(list 'with (list x e) b) (app (fun x (parse b)) (parse e))]
    [(list 'delay (cons h t)) (delay (parse (cons h t)))]
    [(list 'force (cons h t)) (force (parse (cons h t)))]
    [(list 'seqn expr-list) (seqn (map parse expr-list))]
    [(list 'rec (list x e) b)(parse `{with {,x {Y {fun {,x} ,e}}} ,b})]
    [(list 'fun arg-names body) (transform-fundef arg-names (parse body))] ; 1. Agregar el caso del fun
    [(list fun args) (match args
                       [(? number?) (app (parse fun) (parse args))]
                       [(? boolean?) (app (parse fun) (parse args))]
                       [(? symbol?) (app (parse fun) (parse args))]
                       [(cons head tail) (if (symbol? (first args))
                                             (app (parse fun) (parse args))         
                                             (transform-funapp (parse fun) (reverse (map parse args))))]
                       )
     ]
    [(cons prim-name args)(prim prim-name (map parse args))]
 
    [(list arg e) (app (parse arg) (parse e))]; 2. Subir de nivel nuestras funciones
    )
  )


(deftype Val
  (valV v) ; numero, booleano, string, byte, etc.
  (closureV arg body env) ; closure = fun + env
  (promiseV expr env cache) ; promise = expr-L + env + cache
  )

; interp :: Expr  Env -> Val
; interpreta una expresion
(define (interp expr env)
  (match expr
    [(num n) (valV n)]
    [(bool b) (valV b)]
    [(str s) (valV s)]
    [(id x) (env-lookup x env)]; buscar el valor de x en env
    [(zero n) (zeroV (interp n env))]
    [(array expr) (map (λ (x) (interp x env)) expr)]
    [(prim prim-name args)(prim-ops prim-name (map (λ (x) (strict (interp x env))) args))]
    [(if-tf c et ef) (if (valV-v (interp c env))
                         (interp et env)
                         (interp ef env))]
    [(delay (prim prim-name args)) (promiseV (prim prim-name args) env (box #f))]
    [(force expr) (strict (interp expr env))]
    ;[(with x e b) (interp b (extend-env x (interp e env) env))] ; Si asociamos una funcion a una variable, la funcion entra al env
    [(fun arg body) (closureV arg body env)] ; Por ahora, devolvemos la misma expresion que nos llego
    [(seqn expr-list) (interpSeveral expr-list env)]
    [(app f e)
     (def (closureV arg body fenv) (strict (interp f env))) ; Esto permite encontrar (fun 'x (add (id 'x) (id 'x))) por ejemplo y tomar arg y body
    
     (interp body (extend-env arg
                              (promiseV e env (box #f)) ; lazy eval
                              ;(interp e env) ; eager eval
                              fenv)) ; parece que no funciona ni con estatico ni dinamico
     ]
    
))

(define (interpSeveral expr-list env)
  (cond
    [(empty? expr-list) (error "Empty sequence")]
    [(= 1 (length expr-list)) (interp (first expr-list) env)]
    [else (interpSeveral (rest expr-list) env)]
  )
)



;Necesita del force
(define (zeroV n)
  (valV (eq? 0 (valV-v n))))


(deftype Type
  (Num)
  (Bool)
  (String))

;all-nums:: (List nums) -> bool
(define (all-nums lst)
  (match lst
  ['() #t]
  [(cons h t)(if (Num? h) (all-nums t) #f)])
  )


;typeof: expr -> type/error
#|
(cons '+ +)
        (cons '- -)
        (cons '* *)
        (cons '/ /)
        (cons '< <)
        (cons '> >)
|#

(define (typeof expr)
  (match expr
    [(num n)(Num)]
    [(bool b)(Bool)]
     [(str s) (String)]
    [(app (fun x (prim '* (cons h t))) body) (if (Bool? (typeof body))
                                                 (error "error: type error")
                                                 (typeof (prim '* (cons h t)))
                                                 )]
    [(prim '* (list x ...)) (let ([l (map typeof x)])
                              (if (all-nums (cdr l)) (Num) (error "error: type error")))]
    [else expr]
    )
  )

; strict -> Val(valV/closureV/promiseV) -> Val (valV/closureV))
; destructor de promesas - cumplidor de promesas
(define (strict val)
  (match val
    [(promiseV e env cache)
     (if (unbox cache)
         (begin
           ;(printf "Using cached value~n")
           (unbox cache)
           )
         (let ([interp-val (strict (interp e env))])
           (begin (set-box! cache interp-val)
                  ;(printf "Forcing: ~a~n " interp-val)
                  interp-val))
         )]
    [else val]
    )
  )



(define (Y-combinator arg func enviroment)
  (extend-env arg (interp func enviroment) enviroment))


; run: Src -> Src
; corre un programa
(define (run prog) 
  (let* (
         [expr (parse prog)]
         [t (typeof expr)]
         [res (interp expr (Y-combinator 'Y (parse '{fun {f} {with {h {fun {g} {fun {n} {{f {g g}} n}}}} {h h}}}) empty-env))])
    (match res
      [(valV v) v]
      [(closureV arg body env) res]
      [(list expr ...) (map (λ (v) (valV-v v)) res)]
      [(promiseV e env cache)(promiseV e env cache)]
      )
    )
  )

(test (run '{+ 3 4}) 7)
(test (run '{- 5 1}) 4)

(test (run '{with {x 3} 2}) 2)
(test (run '{with {x 3} x}) 3)
(test (run '{with {x 3} {with {y 4} x}}) 3)
(test (run '{with {x 3} {+ x 4}}) 7)
(test (run '{with {x 3} {with {x 10} {+ x x}}}) 20)
(test (run '{with {x 3} {with {x x} {+ x x}}}) 6)
(test (run '{with {x 3} {with {y 2} {+ x y}}}) 5)
(test (run '{with {x 3} {+ 1 {with {y 2} {+ x y}}}}) 6)
(test (run '{with {x 3} {with {y {+ 2 x}} {+ x y}}}) 8)
(test (run '{with {x 3} {if-tf {+ x 1} {+ x 3} {+ x 9}}}) 6)


; Adaptando las pruebas previas
;(test/exn (run '{f 10}) "undefined function") - el error partia de fundef-lookup
(test/exn (run '{f 10}) "undefined")

;(test (run '{f 10} (list '{define {f x} {+ x x}})) 20)
; 1. Asociar la funcion a un identificador
(test (run '{with {f {fun {x} {+ x x}}}{f 10}}) 20)
; 2. Usar la funcion directamente, como un lambda
(test (run '{{fun {x} {+ x x}} 10}) 20)

;(test (run '{add1 {add1 {add1 10}}}(list '{define {add1 x} {+ x 1}})) 13)
(test (run '{with {add1 {fun {x} {+ x 1}}} {add1 {add1 {add1 10}}}}) 13)

; Prueba fallida
(test (run '{with {add1 {fun {x} {+ x 1}}}
                  {with {foo {fun {x} {+ {add1 x} {add1 x}}}}
                        {foo 10}}}) 22)

(test (run '{with {add1 {fun {x} {+ x 1}}}
                  {with {foo {fun {f} {+ {f 10} {f 10}}}}
                        {foo add1}}}) 22)


; Pruebas para casos basicos
(test (run '{{fun {x}{+ x 1}} {+ 2 3}}) 6)
(test (run '{with {apply10 {fun {f} {f 10}}}
                  {with {add1 {fun {x} {+ x 1}}}
                        {apply10 add1}}}) 11)


(test (run '{with {addN {fun {n}
                       {fun {x} {+ x n}}}}
            {{addN 10} 20}}) 30)

; Tests para laziness
(test (run '{with {x y} 1}) 1)

; Tests para comprombar eval strict
(test (run '{with {x 3} {with {y x} y}}) 3)
(test (run '{with {x 3} {with {y {+ x x}} y}}) 6)


(test (run '{with {z {+ 2 2}}
              {with {y {+ z z}}
                    {with {x {+ y y}}
                          {+ x x}}}}) 32)


(test (run '{{fun (a b) {+ a b}} {3 2}}) 5)
(test (run '{{fun (a b c) {+ a {- b c}}} {3 2 1}}) 4)


;PRUEBAS FINALES
(test (run '{+ 3 4}) 7)
(test (run '{- 5 1}) 4)
(test (run '{+ 3 4}) 7)
(test (run '{- 5 1}) 4)
(test (run '{+ 1 2 3 4}) 10)
(test (run '{* 2 3 4}) 24)
(test (run '{/ 12 2 2}) 3)
(test (run '{< 12 3}) #f)
(test (run '{<= 12 3}) #f)
(test (run '{< 12 12}) #f)
(test (run '{<= 12 12}) #t)
(test (run '{> 12 3}) #t)
(test (run '{>= 12 3}) #t)
(test (run '{> 12 12}) #f)
(test (run '{>= 12 12}) #t)
(test (run '{>= 12 12}) #t)
(test (run '{== 12 12}) #t)
(test (run '{== 12 11}) #f)
(test (run '{!= 12 12}) #f)
(test (run '{!= 12 11}) #t)
(test (run '{&& 12 11}) 11)
(test (run '{&& #f #t}) #f)
(test (run '{|| #f #t}) #t)
(test (run '{|| 12 11}) 12)
(test (run '{with {x 3} 2}) 2)
;Deberia usar force
(test (run '{with {x 3} x}) 3)
(test (run '{with {x 3} {with {y 4} x}}) 3)
;Usando Force
(test (run '{force {with {x 3} x}}) 3)
(test (run '{force {with {x 3} {with {y 4} x}}}) 3)

(test (run '{with {x 3} {+ x 4}}) 7)
(test (run '{with {x 3} {with {x 10} {+ x x}}}) 20)
(test (run '{with {x 3} {with {x x} {+ x x}}}) 6)
(test (run '{with {x 3} {with {y 2} {+ x y}}}) 5)
(test (run '{with {x 3} {+ 1 {with {y 2} {+ x y}}}}) 6)
(test (run '{with {x 3} {with {y {+ 2 x}} {+ x y}}}) 8)
(test (run '{* 1 1 1 1}) 1)
(test/exn (run '{* 1 #t 1 1}) "type error")
(test/exn (run '{with {x 1} {* #t x x x}}) "type error")
(test/exn (run '{with {x #t} {* 1 x x x}}) "type error")
(test/exn (run '{with {x #t} {* x x x x}}) "type error")
(test (run '{with {x 3} {+ x x}}) 6)
(test (run '{with {x 3} {with {y 2} {+ x y}}}) 5)
(test (run '{with {{x 3} {y 2}} {+ x y}}) 5)
(test (run '{with {{x 3} {x 5}} {+ x x}}) 10)
(test (run '{with {{x 3} {y {+ x 3}}} {+ x y}}) 9)
(test (run '{with {{x 10} {y 2} {z 3}} {+ x {+ y z}}}) 15)
(test (run '{with {x 3} {if-tf {+ x 1} {+ x 3} {+ x 9}}}) 6)
(test/exn (run '{f 10}) "undefined")
(test (run '{with {f {fun {x} {+ x x}}}{f 10}}) 20)
(test (run '{{fun {x} {+ x x}} 10}) 20)
(test (run '{with {add1 {fun {x} {+ x 1}}}{add1 {add1 {add1 10}}}}) 13)
(test (run '{with {add1 {fun {x} {+ x 1}}}
                  {with {foo {fun {x} {+ {add1 x} {add1 x}}}}
                        {foo 10}}}) 22)
(test (run '{with {add1 {fun {x} {+ x 1}}}
                  {with {foo {fun {f} {+ {f 10} {f 10}}}}
                        {foo add1}}}) 22)
(test (run '{{fun {x}{+ x 1}} {+ 2 3}}) 6)
(test (run '{with {apply10 {fun {f} {f 10}}}
                  {with {add1 {fun {x} {+ x 1}}}
                        {apply10 add1}}}) 11)
(test (run '{with {addN {fun {n}
                       {fun {x} {+ x n}}}}
            {{addN 10} 20}}) 30)

(run '{with {addN {fun {n}
                       {fun {x} {+ x n}}}}
            {{addN 10} 20}})

(run '{with {{x 3} {y 2}} {+ x y}})
(run '{with {{x 3} {x 5}} {+ x x}})
(run '{with {{x 3} {y {+ x 3}}} {+ x y}})
(run '{with {{x 10} {y 2} {z 3}} {+ x {+ y z}}})

(test (run '{with {{x 2}{y 3}{z 1}} {+ x {+ y z}}})6)
(test (run '{with {{x 2}{y 3}} {+ x {+ y 4}}})9)
(test (run '{with {{t 10}{s 20}{u 30}{x 2}{y 3}{z 1}} {+ x {+ y {+ s {+ u 1}}}}})56)
(test (run '{with {{x 3} {y 2}} {+ x y}}) 5)
(test (run '{with {{x 3} {x 5}} {+ x x}}) 10)
(test (run '{with {{x 3} {y {+ x 3}}} {+ x y}}) 9)
(test (run '{with {{x 10} {y 2} {z 3}} {+ x {+ y z}}}) 15)

(test (run '{with {x 3} {if-tf {+ x 1} {+ x 3} {+ x 9}}}) 6)

(run '{rec {sum {fun {n}
                        {if-tf {== n 0} 0 {+ n {sum {- n 1}}}}}} {sum 0}})

(test (run '{rec {sum {fun {n}
                        {if-tf {== n 0} 0 {+ n {sum {- n 1}}}}}} {sum 0}})0)

(test (run '{rec {sum {fun {n}
                        {if-tf {== n 0} 0 {+ n {sum {- n 1}}}}}} {sum 3}})6)

#|(test (run '{rec {mult {fun {n}
                      {if-tf {zero?? n}
                             1
                             {* n {mult {- n 1}}}
                             }
                      }
                 }
            {mult 6}
            })720)

(test (run '{rec {mult {fun {n}
                      {if-tf {zero?? n}
                             0
                             {- n {mult {- n 1}}}
                             }
                      }
                 }
            {mult 10}
            })5)|#

(test (run '{delay {+ 1 1}}) (promiseV
                              (prim '+ (list (num 1) (num 1)))
                              (aEnv 'Y (closureV 'f (app (fun 'h (app (id 'h) (id 'h))) (fun 'g (fun 'n (app (app (id 'f) (app (id 'g) (id 'g))) (id 'n))))) (mtEnv)) (mtEnv))
                              '#&#f))

(test (run '{force {delay {+ 1 1}}})2)

(run '{seqn
       {
        {+ 1 1}
        {+ 2 2}
        }
       })

(test(run "hola")"hola")

(run '{array {1 2 3 4}})

;arreglar para que kar funcione primero
(run '{qdr {array {1 2 3 4}}})

(test (run '{+ 3 4}) 7)
(test (run '{- 5 1}) 4)