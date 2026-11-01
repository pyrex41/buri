\\ SAMPLED regressions for the composed Shen-Scheme let/order pipeline and the
\\ captured binding, conditional and equality emitters (E2E-15). These finite
\\ checks are not proofs; the universal statements are SchemeBranches.v and
\\ SchemeCompose.v. Two tests record CONFIRMED port disagreements (counterexamples).
(load "tests/support.shen")
(load "ports/compiler-branches.shen")
(load "ports/kernel-element.shen")
(tc -)

\\ The Shen reader splits kl:f into three tokens, so prefixed names are interned.
(define buri.k S -> (intern (cn "kl:" S)))
(define buri.ab -> (intern "_scm.assert-boolean"))
\\ Replace the generated argument name by a fixed symbol.
(define buri.compose-normal R -> (buri.swap (hd (hd (tl (hd (tl R))))) lifted R))

\\ Composition as invoked: compile-expression [let X V Body] is
\\ (merge-nested-lets (emit-let ...)), and the body call was ordered first.
(buri.test compose-let-order-merge
 (buri.compose-normal (_scm.kl->scheme [let x 1 [f [g x] [h x]]]))
 [let* [[x 1] [lifted [(buri.k "g") x]]] [(buri.k "f") lifted [(buri.k "h") x]]])
(buri.test compose-let-no-lift-no-star
 (_scm.kl->scheme [let x 1 [f x [g x]]]) [let [[x 1]] [(buri.k "f") x [(buri.k "g") x]]])

\\ emit-let: the value is compiled in the outer scope, the body in the extended one.
(buri.test emit-let-shape (_scm.emit-let x 1 [+ x 2] []) [let [[x 1]] [+ x 2]])

\\ emit-if: literal tests compile only the selected branch.
(buri.test emit-if-literal-true (_scm.kl->scheme [if true 1 [f]]) 1)
(buri.test emit-if-literal-false (_scm.kl->scheme [if false [f] 2]) 2)
(buri.test emit-if-asserts (_scm.kl->scheme [if [f] 1 2]) [if [(buri.k "_scm.assert-boolean") [(buri.k "f")]] 1 2])
(buri.test emit-if-boolean-head (_scm.kl->scheme [if [not [f]] 1 2]) [if [(buri.k "not") [(buri.k "f")]] 1 2])
(buri.test force-boolean-wraps (_scm.force-boolean [f]) [(buri.ab) [f]])
(buri.test yields-boolean-let (_scm.yields-boolean? [let x 1 [not x]]) true)
(buri.test yields-boolean-do (_scm.yields-boolean? [do [f] [g]]) false)

\\ emit-cond: clauses in order, each test forced boolean.
(buri.test emit-cond-clauses-order (_scm.emit-cond-clauses [[[f] 1] [true 2]] [])
 [[[(buri.k "_scm.assert-boolean") [(buri.k "f")]] 1] [true 2]])
(buri.test emit-cond-exhaustive (_scm.kl->scheme [cond [[f] 1] [true 2]])
 [cond [[(buri.k "_scm.assert-boolean") [(buri.k "f")]] 1] [true 2]])
\\ COUNTEREXAMPLE (confirmed port disagreement): the formal profile raises
\\ XCondFail when no clause is true; the emitted Scheme cond has no else and
\\ Shen-Scheme returns (#<void>) without raising.
(buri.test cond-no-true-clause-falls-through
 (trap-error (do (eval-kl [cond [false 1]]) returned) (/. E raised)) returned)
(buri.test cond-no-true-clause-emitted (_scm.kl->scheme [cond [false 1]]) [cond [false 1]])

\\ emit-equality-check branch selection.
(buri.test equality-numeric-eqv (_scm.kl->scheme [let x 2 [= 1 x]]) [let [[x 2]] [eqv? 1 x]])
(buri.test equality-string-equal (_scm.kl->scheme [= "a" [g]]) [equal? "a" [(buri.k "g")]])
(buri.test equality-empty-null (_scm.kl->scheme [= [] [g]]) [null? [(buri.k "g")]])
(buri.test equality-symbol-eq (_scm.kl->scheme [= a [g]]) [eq? [quote a] [(buri.k "g")]])
\\ COUNTEREXAMPLE (confirmed port disagreement): the same KLambda = on the same
\\ values gives different answers depending on whether a literal number occurs.
\\ (* 2 (/ 1 2)) is the inexact 1.0; the literal path emits eqv?, the variable
\\ path calls kl:=, which compares numbers with =.
(buri.test eqv-literal-mixed-exactness-counterexample
 [(eval-kl [= 1 [* 2 [/ 1 2]]]) (eval-kl [let y 1 [let x [* 2 [/ 1 2]] [= y x]]])] [false true])
(buri.test eqv-literal-emitted (_scm.kl->scheme [= 1 [* 2 [/ 1 2]]]) [eqv? 1 [* 2 [non-rational-/ 1 2]]])
(buri.done)
