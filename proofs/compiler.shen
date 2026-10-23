\\ Explicit universally quantified certificates, not finite test tables.
\\ The kernel checks every rewrite, substitution, and induction hypothesis.
(tc -)
(define buri.compiler-theorem ->
 [theorem compiler-continuation [[e expr] [k code] [s stack]]
  [run [compile [v e] [v k]] [v s]]
  [run [v k] [cons [eval [v e]] [v s]]]
  [induct e
   [[lit [n]
     [[rewrite [0] forward [definition compile-lit] [[n [v n]] [k [v k]]]]
      [rewrite [] forward [definition run-push] [[n [v n]] [k [v k]] [s [v s]]]]
      [rewrite [1 0] reverse [definition eval-lit] [[n [v n]]]]]]
    [add [a b]
     [[rewrite [0] forward [definition compile-add] [[a [v a]] [b [v b]] [k [v k]]]]
      [rewrite [] forward [hypothesis a] [[k [compile [v b] [plus [v k]]]] [s [v s]]]]
      [rewrite [] forward [hypothesis b] [[k [plus [v k]]] [s [cons [eval [v a]] [v s]]]]]
      [rewrite [] forward [definition run-plus] [[k [v k]] [x [eval [v a]]] [y [eval [v b]]] [s [v s]]]]
      [rewrite [1 0] reverse [definition eval-add] [[a [v a]] [b [v b]]]]]]
    [mul [a b]
     [[rewrite [0] forward [definition compile-mul] [[a [v a]] [b [v b]] [k [v k]]]]
      [rewrite [] forward [hypothesis a] [[k [compile [v b] [times [v k]]]] [s [v s]]]]
      [rewrite [] forward [hypothesis b] [[k [times [v k]]] [s [cons [eval [v a]] [v s]]]]]
      [rewrite [] forward [definition run-times] [[k [v k]] [x [eval [v a]]] [y [eval [v b]]] [s [v s]]]]
      [rewrite [1 0] reverse [definition eval-mul] [[a [v a]] [b [v b]]]]]]]]])
(define buri.halt-theorem ->
 [theorem compiler-result [[e expr] [s stack]]
  [run [compile [v e] [halt]] [v s]] [ok [cons [eval [v e]] [v s]]]
  [direct
   [[rewrite [] forward [lemma compiler-continuation] [[e [v e]] [k [halt]] [s [v s]]]]
    [rewrite [] forward [definition run-halt] [[s [cons [eval [v e]] [v s]]]]]]]])
(define buri.compiler-bundle -> [(buri.compiler-theorem) (buri.halt-theorem)])
(define buri.prove -> (buri.check-bundle (buri.theory) (buri.compiler-bundle) 100))
