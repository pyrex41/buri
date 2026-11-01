\\ Exact upstream defines from tizoc/shen-scheme src/compiler.shen,
\\ commit 8d261518db17fbfec32d1b268b40ed216b925c74, blob 42ac753b8f305c578998b74693fc85b28112a814.
\\ Copyright (c) 2012-2021 Bruno Deferrari. BSD-3-Clause.
\\ Read inside the exact upstream package header: Shen itself qualifies names.
(tc -)
(package _scm [begin quote string->symbol null? car cdr pair? else
                     vector-ref vector-set! make-vector string non-rational-/
                     string-append integer->char char->integer shen-string->unicode
                     string-ref string-length substring list kl
                     eq? eqv? equal? scm. scm.import import *sterror* *toplevel*
                     letrec let* scm.letrec scm.with-input-from-string scm.read
                     scm.define scm.goto-label scm.begin
                     compatible sealed app
                     scm.dynamic-wind
                     scm.value/or scm.get/or scm.<-vector/or scm.<-address/or]

(define yields-boolean?
  true -> true
  false -> true
  [let _ _ Exp] -> (yields-boolean? Exp)
  [do _ Exp] -> (yields-boolean? Exp)
  [X _ _] -> (element? X (value *yields-boolean2*))
  [X _] -> (element? X (value *yields-boolean1*))
  _ -> false)

(define force-boolean
  X -> X where (yields-boolean? X)
  X -> [assert-boolean X])

(define emit-symbol
  S -> [quote S])

(define emit-let
  Var Value Body Scope
  -> [let [[Var (compile-expression Value Scope)]]
       (compile-expression Body [Var | Scope])])

(define emit-if
  true Then _ Scope  -> (compile-expression Then Scope)
  false _ Else Scope -> (compile-expression Else Scope)
  Test Then Else Scope
  -> [if (compile-expression (force-boolean Test) Scope)
         (compile-expression Then Scope)
         (compile-expression Else Scope)])

(define emit-cond
  Clauses Scope -> [cond | (emit-cond-clauses Clauses Scope)])

(define emit-cond-clauses
  [] _ -> []
  [[Test Body] | Rest] Scope
  -> (let CompiledTest (compile-expression (force-boolean Test) Scope)
          CompiledBody (compile-expression Body Scope)
          CompiledRest (emit-cond-clauses Rest Scope)
       [[CompiledTest CompiledBody]
        | CompiledRest]))

(define emit-equality-check
  V1 V2 Scope -> (order-call [eq? (compile-expression V1 Scope)
                                  (compile-expression V2 Scope)])
      where (or (unbound-symbol? V1 Scope)
                (unbound-symbol? V2 Scope)
                (= [fail] V1)
                (= [fail] V2))
  V1 V2 Scope -> (order-call [eqv? (compile-expression V1 Scope)
                                   (compile-expression V2 Scope)])
      where (or (number? V1) (number? V2))
  V1 V2 Scope -> (order-call [equal? (compile-expression V1 Scope)
                                     (compile-expression V2 Scope)])
      where (or (string? V1) (string? V2))
  [] V2 Scope -> [null? (compile-expression V2 Scope)]
  V1 [] Scope -> [null? (compile-expression V1 Scope)]
  V1 V2 Scope -> (emit-static-application-fallback
                  (native-mode)
                  =
                  [V1 V2]
                  Scope))

)
