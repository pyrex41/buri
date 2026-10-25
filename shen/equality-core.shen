\\ BURI/EQ-CORE-1: axiom-free congruence derivation. No artifact rules or eval.
\\ Returns inert candidate equations; typed admission and interpretation are
\\ checked independently by the Rocq bridge before a semantic claim is made.
(tc -)
(define buri.eq2-derive
 [refl A] -> [some [A A]]
 [sym P] -> (buri.eq2-sym (buri.eq2-derive P))
 [trans P Q] -> (buri.eq2-trans (buri.eq2-derive P) (buri.eq2-derive Q))
 [cong P Q] -> (buri.eq2-cong (buri.eq2-derive P) (buri.eq2-derive Q))
 _ -> none)
(define buri.eq2-sym [some [A B]] -> [some [B A]] _ -> none)
(define buri.eq2-trans [some [A B]] [some [C D]] ->
 (if (= B C) [some [A D]] none)
 _ _ -> none)
(define buri.eq2-cong [some [A B]] [some [C D]] ->
 [some [[app A C] [app B D]]]
 _ _ -> none)
