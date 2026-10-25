\\ Build a private checker from controlled compiler records, not certificates.
\\ Certificate data never goes through native eval. Chez activation is trusted.
(tc -)
(define buri.eq2-seal-definition [define [Name | Args] Body] -> [Name [lambda Args Body]]
 _ -> (simple-error "EQ2 capsule requires a procedure definition"))
(define buri.eq2-seal-program [[_ A] [_ B] [_ C] [_ D]] ->
 [letrec [[(intern "kl:=") [lambda [x y] [equal? x y]]]
          (buri.eq2-seal-definition A) (buri.eq2-seal-definition B)
          (buri.eq2-seal-definition C) (buri.eq2-seal-definition D)]
  (intern "kl:buri.eq2-derive")]
 _ -> (simple-error "EQ2 capsule requires four observed definitions"))
(define buri.eq2-seal-request Program ->
 [eval [quote Program]
  [environment [quote [only [chezscheme] lambda let let* letrec if cond and or quote
    eq? equal? null? pair? car cdr cons list]]]])
(define buri.make-sealed-eq2 Records ->
 ((foreign scm.eval) (buri.eq2-seal-request (buri.eq2-seal-program Records))))
