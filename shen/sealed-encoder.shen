\\ Trusted construction only. The returned procedure has no Shen global reads.
\\ Its authority is still supplied by translation validation of the records.
(tc -)
(define buri.sealed-imports ->
 [lambda let let* letrec if and or quote
  eq? eqv? equal? null? pair? car cdr + - * / >= <
  string-append string-ref string substring string-length char->integer
  integer? exact? number? inexact floor boolean? symbol? symbol->string number->string error])
(define buri.sealed-helpers ->
 [[(intern "non-rational-/") [lambda [x y]
    [let [[r [/ x y]]] [if [integer? r] r [inexact r]]]]]
  [(intern "kl:floor") [lambda [x] [floor x]]]
  [(intern "kl:=") [lambda [x y] [equal? x y]]]
  [(intern "kl:_scm.assert-boolean") [lambda [x]
    [if [boolean? x] x [error [quote sealed-encoder] "Expected boolean"]]]]
  [(intern "kl:buri.exact-integer?") [lambda [x]
    [and [number? x] [integer? x] [exact? x]]]]
  [(intern "kl:symbol?") [lambda [x] [symbol? x]]]
  [(intern "kl:str") [lambda [x]
    [if [symbol? x] [symbol->string x] [number->string x 10]]]]])
(define buri.sealed-definition
 [define [Name | Args] Body] -> [Name [lambda Args Body]]
 _ -> (simple-error "Sealed encoder requires a procedure definition"))
(define buri.sealed-targets
 [[_ A] [_ B] [_ C]] ->
  [(buri.sealed-definition A) (buri.sealed-definition B) (buri.sealed-definition C)]
 _ -> (simple-error "Sealed encoder requires exactly three observed pairs"))
(define buri.sealed-program Records ->
 [letrec (append (buri.sealed-helpers) (buri.sealed-targets Records)) (intern "kl:buri.wire")])
(define buri.sealed-eval Program ->
 ((foreign scm.eval)
  [eval [quote Program]
    [environment [quote [only [chezscheme] | (buri.sealed-imports)]]]]))
(define buri.make-sealed-encoder Records -> (buri.sealed-eval (buri.sealed-program Records)))
(define buri.export-sealed Records Path ->
 (let Program (buri.sealed-program Records)
  (do (write-to-file Path (buri.wire [buri-sealed-1 (buri.kl-node [Program Records (buri.sealed-imports)])]))
      (write-to-file (cn Path ".sexp") (make-string "~S~%" Program)))))
