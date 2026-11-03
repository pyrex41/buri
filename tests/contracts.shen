(load "shen/base.shen")
(load "shen/contract-cert.shen")
(load "tests/support.shen")
\\ E2E-08: the Shen BURI/KL-CONTRACT-1 checker on the certificate of the
\\ transported map example and on mutated certificates. The literal
\\ fingerprints and verdicts are those computed by the Rocq checker
\\ (rocq/ContractCertExample.v); agreement here is sampled, not a proof.

(set buri.ct-body
 [if [call "cons?" [[var "xs"]]]
  [let "h" [call "hd" [[var "xs"]]]
   [let "t" [call "tl" [[var "xs"]]]
    [let "y" [app [var "f"] [[var "h"]]]
     [let "r" [app [app [call "user:map" []] [[var "f"]]] [[var "t"]]]
      [call "cons" [[var "y"] [var "r"]]]]]]]
  [nil]])
(define buri.ct-lit [] -> [nil] [Z | Zs] -> [call "cons" [[num Z] (buri.ct-lit Zs)]])
(define buri.ct-main L -> [app [app [call "user:map" []] [[lambda "x" [call "+" [[var "x"] [var "x"]]]]]] [(buri.ct-lit L)]])
(define buri.ct-program L -> [program [["user:map" ["f" "xs"] (value buri.ct-body)]] (buri.ct-main L)])

(define buri.ct-sv -> [rule r_val []])
(define buri.ct-pc P Args -> [rule r_call [[rule aj_ctx [[prim P]]] | Args]])
(define buri.ct-pm -> [rule r_app [[rule r_call0 [[rule aj_partial [[side "map-bound"]]]]]
                                   [rule aj_partial [[side "map-bound"]]] (buri.ct-sv)]])
(set buri.ct-body-sk
 [rule r_if [(buri.ct-pc "cons?" [(buri.ct-sv)])
  [rule r_let [(buri.ct-pc "hd" [(buri.ct-sv)])
   [rule r_let [(buri.ct-pc "tl" [(buri.ct-sv)])
    [rule r_let [[rule r_app [(buri.ct-sv) [rule aj_sem [[side "map-fspec"]]] (buri.ct-sv)]]
     [rule r_let [[rule r_app [(buri.ct-pm) [rule aj_ctx [[rec "user:map"] [side "map-measure-decreases"]]] (buri.ct-sv)]]
      [rule r_conseq [(buri.ct-pc "cons" [(buri.ct-sv) (buri.ct-sv)])]]]]]]]]]]
  [rule r_conseq [(buri.ct-sv)]]]])
(define buri.ct-lit-sk [] -> (buri.ct-sv) [_ | L] -> (buri.ct-pc "cons" [(buri.ct-sv) (buri.ct-lit-sk L)]))
(define buri.ct-main-sk L -> [rule r_conseq [[rule r_app [(buri.ct-pm) [rule aj_ctx [[rec "user:map"] [side "dbl-fspec"]]] (buri.ct-lit-sk L)]]]])
(define buri.ct-cert Theory Evaluator Mode Hyps Ms Bodies Main FP ->
 [contract-certificate "buri-contract-1" Theory [program "map-example" FP] Evaluator
  [statement "contract_verdict_sound" Mode] [hypotheses Hyps] [measures Ms] [bodies Bodies] [main Main]])
(define buri.ct-std Mode Ms FP ->
 (buri.ct-cert (buri.cc-theory) (buri.cc-evaluator) Mode [] Ms [["user:map" (value buri.ct-body-sk)]] (buri.ct-main-sk [1 2 3]) FP))
(set buri.ct-fp (buri.cc-fingerprint (buri.ct-program [1 2 3])))
(set buri.ct-measures [["user:map" "map_meas"]])
(set buri.ct-good (buri.ct-std total (value buri.ct-measures) (value buri.ct-fp)))
(set buri.ct-host-main
 [rule r_conseq [[rule r_app [(buri.ct-pm) [rule aj_ctx [[rec "user:map"] [side "dbl-fspec"]]]
                               [rule r_call [[rule aj_ctx [[hyp "host:cons"]]] (buri.ct-sv) (buri.ct-lit-sk [2 3])]]]]]])
(define buri.ct-with-main Hyps Main ->
 (buri.ct-cert (buri.cc-theory) (buri.cc-evaluator) total Hyps (value buri.ct-measures)
   [["user:map" (value buri.ct-body-sk)]] Main (value buri.ct-fp)))

\\ Identities agree with the Rocq checker's computed values.
(buri.test program-fingerprint (value buri.ct-fp) 987574484711662929)
(buri.test theory-identity (buri.cc-theory) [theory "BURI/KL-CONTRACT-1" 825557597746994086])
(buri.test evaluator-capture-identity (buri.cc-hash-file "ports/e2e07-klambda.bits") 1927390069043521096)
(buri.test evaluator-pin-is-capture (buri.cc-evaluator) [evaluator "e2e07_klambda" (buri.cc-hash-file "ports/e2e07-klambda.bits")])

\\ The example certificate (rocq example_accepted).
(buri.test example-accepted (buri.contract-check (buri.ct-program [1 2 3]) (value buri.ct-good))
 [accepted ["contract_verdict_sound" total] []
  ["cons" "cons" "cons" "cons?" "hd" "tl" "cons"]
  ["map-bound" "map-bound" "dbl-fspec" "map-fspec" "map-bound" "map-bound" "map-measure-decreases"]])
(buri.test partial-needs-no-measure
 (hd (buri.contract-check (buri.ct-program [1 2 3]) (buri.ct-std partial [] (value buri.ct-fp)))) accepted)
(buri.test total-needs-measure
 (buri.contract-check (buri.ct-program [1 2 3]) (buri.ct-std total [] (value buri.ct-fp))) [rejected missing-measure])
(buri.test stale-program (buri.contract-check (buri.ct-program [1 2 4]) (value buri.ct-good)) [rejected stale-program])
(buri.test stale-theory
 (buri.contract-check (buri.ct-program [1 2 3])
  (buri.ct-cert [theory "BURI/KL-CONTRACT-1" 1] (buri.cc-evaluator) total [] (value buri.ct-measures)
   [["user:map" (value buri.ct-body-sk)]] (buri.ct-main-sk [1 2 3]) (value buri.ct-fp)))
 [rejected stale-theory])
(buri.test stale-evaluator
 (buri.contract-check (buri.ct-program [1 2 3])
  (buri.ct-cert (buri.cc-theory) [evaluator "e2e07_klambda" 0] total [] (value buri.ct-measures)
   [["user:map" (value buri.ct-body-sk)]] (buri.ct-main-sk [1 2 3]) (value buri.ct-fp)))
 [rejected stale-evaluator])
(buri.test undeclared-host-contract
 (buri.contract-check (buri.ct-program [1 2 3]) (buri.ct-with-main [] (value buri.ct-host-main)))
 [rejected undeclared-hypothesis])
(buri.test declared-host-contract-is-premise
 (hd (tl (tl (buri.contract-check (buri.ct-program [1 2 3]) (buri.ct-with-main ["host:cons"] (value buri.ct-host-main))))))
 ["host:cons"])
(buri.test duplicate-host-contract
 (buri.contract-check (buri.ct-program [1 2 3]) (buri.ct-with-main ["host:cons" "host:cons"] (value buri.ct-host-main)))
 [rejected duplicate-hypothesis])
(buri.test unknown-primitive
 (buri.contract-check (buri.ct-program [1 2 3])
  (buri.ct-with-main [] [rule r_conseq [[rule r_app [(buri.ct-pm) [rule aj_ctx [[rec "user:map"]]]
                                                      (buri.ct-pc "launch" [(buri.ct-sv) (buri.ct-lit-sk [2 3])])]]]]))
 [rejected unknown-primitive])
(buri.test body-shape
 (buri.contract-check (buri.ct-program [1 2 3])
  (buri.ct-cert (buri.cc-theory) (buri.cc-evaluator) total [] (value buri.ct-measures)
   [["user:map" [rule r_if [(buri.ct-pc "cons?" [(buri.ct-sv)])
                            [rule r_if [(buri.ct-sv) (buri.ct-sv) (buri.ct-sv)]] [rule r_conseq [(buri.ct-sv)]]]]]]
   (buri.ct-main-sk [1 2 3]) (value buri.ct-fp)))
 [rejected body-shape])
\\ Shen-only input hazards (the typed Rocq input cannot express them).
(buri.test forged-label
 (buri.contract-check (buri.ct-program [1 2 3]) (buri.ct-with-main [accepted] (value buri.ct-host-main)))
 [rejected forged-label])
(buri.test malformed-certificate (buri.contract-check (buri.ct-program [1 2 3]) [contract-certificate]) [rejected malformed-certificate])
(buri.test malformed-program
 (buri.contract-check [program [] [while [bool true]]] (value buri.ct-good)) [rejected malformed-certificate])
(buri.test unknown-mode
 (buri.contract-check (buri.ct-program [1 2 3]) (buri.ct-std eventually (value buri.ct-measures) (value buri.ct-fp)))
 [rejected unknown-mode])
(buri.done)
