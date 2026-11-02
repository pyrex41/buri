(load "buri.shen")
(load "shen/ledger.shen")
(load "shen/primitive-inventory.shen")
(load "shen/primitive-table.shen")
(load "shen/primitive-json.shen")
(load "shen/primitive-matrix.shen")
(load "tests/support.shen")
\\ E2E-17 primitive coverage matrix: regeneration, acceptance and hostile
\\ variants. A consistent matrix is bookkeeping, not proof acceptance; the
\\ theorems it cites are checked by `make prove`.

\\ Regeneration from the pinned source bytes is byte-identical.
(buri.pj-write "_build/primitives.json")
(buri.test matrix-regenerates (= (read-file-as-bytelist "_build/primitives.json") (read-file-as-bytelist "spec/primitives.json")) true)

\\ The real matrix is accepted.
(set buri.pt-matrix (buri.lread-json "spec/primitives.json"))
(set buri.pt-env (buri.pm-env))
(define buri.pt-verdict M -> (buri.pm-decide-env M (value buri.pt-env)))
(define buri.pt-show [rejected Vs] -> (do (map (/. V (output "VIOLATION ~S~%" V)) Vs) [rejected (length Vs)])  V -> V)
(buri.test real-matrix-consistent (buri.pt-show (buri.pt-verdict (value buri.pt-matrix))) [primitive-matrix-consistent 114 123])
(buri.test kl-primitives-are-36 (length (hd (value buri.pt-env))) 36)

\\ Hostile variants of the parsed matrix.
(define buri.pt-put Key V [obj Pairs] -> [obj (buri.pt-put-h Key V Pairs)])
(define buri.pt-put-h Key V [] -> [[Key V]]  Key V [[Key _] | Ps] -> [[Key V] | Ps]  Key V [P | Ps] -> [P | (buri.pt-put-h Key V Ps)])
(define buri.pt-map-entries F M -> (buri.pt-put "entries" [arr (map F (buri.la (buri.lf "entries" M)))] M))
(define buri.pt-drop-entry Id M -> (buri.pt-put "entries" [arr (buri.lfilter (/. E (not (= (buri.lfs "id" E) Id))) (buri.la (buri.lf "entries" M)))] M))
(define buri.pt-edit Id F M -> (buri.pt-map-entries (/. E (if (= (buri.lfs "id" E) Id) (F E) E)) M))
(define buri.pt-evidence Key V E -> (buri.pt-put "evidence" (buri.pt-put Key V (buri.lf "evidence" E)) E))
(define buri.pt-has? V [rejected Vs] -> (buri.member? V Vs)  _ _ -> false)
(define buri.pt-m -> (value buri.pt-matrix))
(buri.test missing-kl-primitive-rejected
  (buri.pt-has? [missing-kl-primitive "shen-cl:="] (buri.pt-verdict (buri.pt-drop-entry "shen-cl:=" (buri.pt-m)))) true)
(buri.test missing-port-primitive-rejected
  (buri.pt-has? [missing-port-primitive "shen-scheme:_scm.assert-boolean"]
    (buri.pt-verdict (buri.pt-drop-entry "shen-scheme:_scm.assert-boolean" (buri.pt-m)))) true)
(buri.test missing-cl-helper-rejected
  (buri.pt-has? [missing-port-primitive "shen-cl:shen-cl.numeric-equal"]
    (buri.pt-verdict (buri.pt-drop-entry "shen-cl:shen-cl.numeric-equal" (buri.pt-m)))) true)
(buri.test unaudited-theorem-rejected
  (buri.pt-has? [unaudited-theorem "shen-cl:* CLWrappers.CLWrappers.multiply_is_fine"]
    (buri.pt-verdict (buri.pt-edit "shen-cl:*" (/. E (buri.pt-evidence "theorems" [arr [[str "CLWrappers.CLWrappers.multiply_is_fine"]]] E)) (buri.pt-m)))) true)
(buri.test proved-without-theorem-rejected
  (buri.pt-has? [proved-without-theorem "shen-scheme:="]
    (buri.pt-verdict (buri.pt-edit "shen-scheme:=" (/. E (buri.pt-evidence "theorems" [arr []] E)) (buri.pt-m)))) true)
(buri.test upgraded-evidence-rejected
  (buri.pt-has? [proved-without-theorem "shen-scheme:+"]
    (buri.pt-verdict (buri.pt-edit "shen-scheme:+" (/. E (buri.pt-evidence "kind" [str "proved"] E)) (buri.pt-m)))) true)
(buri.test unknown-evidence-kind-rejected
  (buri.pt-has? [unknown-evidence-kind "shen-cl:pos"]
    (buri.pt-verdict (buri.pt-edit "shen-cl:pos" (/. E (buri.pt-evidence "kind" [str "runtime-behaves-correctly"] E)) (buri.pt-m)))) true)
(define buri.pt-reown E -> (let C (buri.lf "closure" E)
  (buri.pt-put "closure" (buri.pt-put "host_ops" [arr (map (/. O (buri.pt-put "owner" [str "E2E-99"] O)) (buri.la (buri.lf "host_ops" C)))] C) E)))
(buri.test unowned-host-op-rejected
  (buri.pt-has? [unowned-host-op "shen-scheme:= chez:eq?"] (buri.pt-verdict (buri.pt-edit "shen-scheme:=" (function buri.pt-reown) (buri.pt-m)))) true)
(buri.test missing-contract-rejected
  (buri.pt-has? [missing-contract "SchemeWrappers.chez_equality_ops.chez_eq"]
    (buri.pt-verdict (buri.pt-put "contracts" [arr (buri.lfilter (/. C (not (= (buri.lfs "id" C) "SchemeWrappers.chez_equality_ops.chez_eq")))
                                                          (buri.la (buri.lf "contracts" (buri.pt-m))))] (buri.pt-m)))) true)
\\ The named SBCL host contracts left by CLContracts.captured_contracts cannot
\\ be dropped from the matrix, and a lane theorem must be in its audit module.
(buri.test missing-host-op-contract-rejected
  (buri.pt-has? [missing-contract "CLContracts.cl_host_ops.host_eq"]
    (buri.pt-verdict (buri.pt-put "contracts" [arr (buri.lfilter (/. C (not (= (buri.lfs "id" C) "CLContracts.cl_host_ops.host_eq")))
                                                          (buri.la (buri.lf "contracts" (buri.pt-m))))] (buri.pt-m)))) true)
(buri.test unaudited-lane-theorem-rejected
  (buri.pt-has? [unaudited-theorem "shen-cl:shen-cl.numeric-equal CLContracts.CLContracts.numeric_equal_always_true"]
    (buri.pt-verdict (buri.pt-edit "shen-cl:shen-cl.numeric-equal"
      (/. E (buri.pt-evidence "theorems" [arr [[str "CLContracts.CLContracts.numeric_equal_always_true"]]] E)) (buri.pt-m)))) true)
(buri.test aggregate-contract-rejected
  (buri.pt-has? [unknown-contract-reference "shen-cl:= runtime-behaves-correctly"]
    (buri.pt-verdict (buri.pt-edit "shen-cl:=" (/. E (buri.pt-evidence "contracts" [arr [[str "runtime-behaves-correctly"]]] E)) (buri.pt-m)))) true)
(buri.test duplicate-entry-rejected
  (buri.pt-has? [duplicate-entry "shen-cl:pos"]
    (buri.pt-verdict (buri.pt-put "entries" [arr (append (buri.la (buri.lf "entries" (buri.pt-m)))
      (buri.lfilter (/. E (= (buri.lfs "id" E) "shen-cl:pos")) (buri.la (buri.lf "entries" (buri.pt-m)))))] (buri.pt-m)))) true)

\\ The inventory lexer is inert and honours SBCL read-time conditionals.
(define buri.pt-bytes S -> (map (/. C (string->n C)) (explode S)))
(define buri.pt-defs D S -> (map (/. Def [(buri.pi-def-name Def) (buri.pi-free Def D)])
  (buri.pi-defs D (buri.pi-features D (buri.pi-parse-all (buri.pi-lex D (buri.pt-bytes S)))))))
(buri.test scheme-refs-conservative (buri.pt-defs scheme "(define (f x) (let ((y (car x))) (g y 'z)))")
  [["f" ["let" "car" "g"]]])
(buri.test cl-feature-filter (buri.pt-defs cl "#-sbcl (defun |a| () (bad)) #+sbcl (defun |b| (x) (consp x))")
  [["b" ["CONSP"]]])
(buri.test eval-is-data (buri.pt-defs scheme "(define (h e) (eval e))") [["h" ["eval"]]])
(buri.test closure-reaches-host (hd (tl (buri.pt-closure "shen-scheme" (buri.pt-db "shen-scheme") ["kl:_scm.assert-boolean"])))
  [[host "chez:if"] [host "chez:boolean?"] [host "chez:syntax-rules"] [host "chez:error"]])

\\ SAMPLED native observations on the Shen-Scheme host (not proofs). The
\\ compiled literal path of = emits eqv?, which differs from the stock kl:=
\\ on mixed exactness; eval-kl takes the same literal path.
(define buri.pt-eqv-one X -> (= X 1))
(define buri.pt-eq-generic X Y -> (= X Y))
(set buri.pt-inexact-one (* 2 (/ 1 2)))
(buri.test sample-inexact-one-is-integral (integer? (value buri.pt-inexact-one)) true)
(buri.test sample-literal-path-eqv (buri.pt-eqv-one (value buri.pt-inexact-one)) false)
(buri.test sample-generic-path-kl-eq (buri.pt-eq-generic (value buri.pt-inexact-one) 1) true)
(buri.test sample-eval-kl-literal-path (eval-kl [= [* 2 [/ 1 2]] 1]) false)
(buri.test sample-zero-times-symbol-raises (trap-error (do (* 0 true) returned) (/. E raised)) raised)
(buri.done)
