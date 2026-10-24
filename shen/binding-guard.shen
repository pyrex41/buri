\\ Trusted live execution guard; never imported by inert artifact checkers.
(tc -)
(define buri.binding-names ->
 (map (/. N (intern N)) ["kl:buri.wire-byte" "kl:buri.wire-string" "kl:buri.wire" "kl:buri.exact-integer?" "kl:buri.integer-spelling?" "kl:buri.unsigned-spelling?" "kl:buri.digits?" "kl:buri.member?" "kl:floor" "kl:symbol?" "kl:str" "kl:_scm.assert-boolean" "non-rational-/" "string-append" "string-ref" "string" "substring" "string-length" "char->integer" "eqv?" "equal?" "null?" "pair?" "car" "cdr" "+" "-" "*" ">=" "<"]))
(define buri.live-binding Name -> ((foreign scm.eval) Name))
(define buri.binding-snapshot [] -> []
 [Name | Names] -> [[Name (buri.live-binding Name)] | (buri.binding-snapshot Names)])
(define buri.bindings-current? [] [] -> true
 [[Name Value] | Bindings] [Name | Names] ->
  (and (= Value (buri.live-binding Name)) (buri.bindings-current? Bindings Names))
 _ _ -> false)
(define buri.seal-encoder -> (buri.binding-snapshot (buri.binding-names)))
(define buri.guarded-wire Bindings X ->
 (if (buri.bindings-current? Bindings (buri.binding-names))
   (let Output (buri.wire X)
     (if (buri.bindings-current? Bindings (buri.binding-names)) Output
       (simple-error "Encoder binding changed during call")))
   (simple-error "Encoder bindings changed; revalidate before execution")))
