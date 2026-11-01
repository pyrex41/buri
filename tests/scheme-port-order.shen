\\ SAMPLED regressions for the actual source-linked Shen-Scheme ordering pass
\\ and the captured kernel list helpers. These finite checks are not proofs;
\\ the universal statements are OrderCallPass.v and OrderCallPreserve.v.
(tc -)
(load "ports/compiler-order.shen")
(load "ports/kernel-list.shen")

(define buri.order-assert
  _ true -> true
  Name false -> (error "Scheme order regression failed: ~A" Name))

\\ The result spine: (let ((V X)) ...) / (let* ((V X) ...) ...) / the final call.
(define buri.order-final
  [let [[_ _]] Body] -> (buri.order-final Body)
  [let* _ Body] -> Body
  Call -> Call)
(define buri.order-bindings
  [let [[V X]] Body] -> [[V X] | (buri.order-bindings Body)]
  [let* Bindings _] -> Bindings
  _ -> [])

\\ Every bound name is fresh for the input and for every earlier bound name,
\\ and substituting the bound computations back gives the input call.
(define buri.order-fresh?
  Input [] _ -> true
  Input [[V _] | Bindings] Used -> (and (= 0 (occurrences V Input))
                                        (not (element? V Used))
                                        (buri.order-fresh? Input Bindings [V | Used])))
(define buri.order-restore
  Call [] -> Call
  Call [[V X] | Bindings] -> (buri.order-restore (subst X V Call) Bindings))
(define buri.order-check
  Name Input -> (let Output (_scm.order-call Input)
                     Bindings (buri.order-bindings Output)
                  (do (buri.order-assert Name (buri.order-fresh? Input Bindings []))
                      (buri.order-assert Name (= Input (buri.order-restore (buri.order-final Output) Bindings)))
                      Bindings)))

\\ Empty and single-argument calls are unchanged.
(buri.order-assert empty (= [f] (_scm.order-call [f])))
(buri.order-assert single (= [f [g]] (_scm.order-call [f [g]])))
(buri.order-assert simple-only (= [f x [quote y] 1 "s"] (_scm.order-call [f x [quote y] 1 "s"])))
\\ The last computation stays in place; earlier computations are bound in order.
(buri.order-assert two (= 1 (length (buri.order-check two [f [g] [h]]))))
(buri.order-assert nested (= 1 (length (buri.order-check nested [f [g [h a]] [k]]))))
(buri.order-assert effects
  (= [[a] [b]] (map (/. B (hd (tl B))) (buri.order-check effects [f [a] x [b] y [c]]))))
(buri.order-assert raise-mid
  (= [[raise first] [g]] (map (/. B (hd (tl B))) (buri.order-check raise-mid [f [raise first] [g] [raise last]]))))
\\ A gensym candidate that already occurs in the call is skipped (collision branch).
(set shen.*gensym* 900)
(buri.order-assert collision
  (not (= arg901 (hd (hd (buri.order-check collision [f [g arg901] [h]]))))))

\\ Captured kernel helpers agree with the running kernel on samples.
(buri.order-assert occurrences
  (and (= (occurrences a [a [b a] [[a]]]) (buri.kernel.occurrences a [a [b a] [[a]]]))
       (= 0 (buri.kernel.occurrences z [a [b a]]))
       (= 1 (buri.kernel.occurrences a a))))
(buri.order-assert reverse (= (reverse [1 2 3]) (buri.kernel.reverse [1 2 3])))
(buri.order-assert not (and (= false (buri.kernel.not true)) (= true (buri.kernel.not false))))

(output "BURI_TESTS_OK 12~%")
