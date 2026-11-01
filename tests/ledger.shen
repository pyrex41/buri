(load "buri.shen")
(load "shen/ledger.shen")
(load "tests/support.shen")
\\ Ledger bookkeeping regressions. A consistent ledger is not proof acceptance.

\\ Enforcement tests for charter provisional exclusions (reference admission only).
(buri.test enforce-no-and-form (buri.evaluate [] [and [literal [bool true]] [literal [bool true]]] 10) [rejected unsupported-or-malformed-program])
(buri.test enforce-no-cond-form (buri.evaluate [] [cond [[literal [bool true]] [literal [int 1]]]] 10) [rejected unsupported-or-malformed-program])
(buri.test enforce-no-type-form (buri.evaluate [] [type [literal [int 1]] number] 10) [rejected unsupported-or-malformed-program])
(buri.test enforce-no-intern (buri.evaluate [] [primitive intern [[literal [str "a"]]]] 10) [rejected unsupported-or-malformed-program])
(buri.test enforce-no-absvector (buri.evaluate [] [primitive absvector [[literal [int 1]]]] 10) [rejected unsupported-or-malformed-program])
(buri.test enforce-no-write-byte (buri.evaluate [] [primitive write-byte [[literal [int 65]] [literal [int 0]]]] 10) [rejected unsupported-or-malformed-program])
(buri.test enforce-no-get-time (buri.evaluate [] [primitive get-time [[literal [sym run]]]] 10) [rejected unsupported-or-malformed-program])

\\ Inert JSON reader.
(define buri.lt-bytes S -> (buri.lt-bytes-h S))
(define buri.lt-bytes-h "" -> [] S -> [(string->n (pos S 0)) | (buri.lt-bytes-h (tlstr S))])
(define buri.lt-parse S -> (trap-error (buri.lj-parse (buri.lt-bytes S)) (/. E (buri.ledger-error-verdict (error-to-string E)))))
(buri.test json-object (buri.lt-parse "{c#34;ac#34;: [1, -2, true, null, c#34;xc#92;nyc#34;]}")
 [obj [["a" [arr [[int 1] [int -2] [bool true] null [str (cn "x" (cn (n->string 10) "y"))]]]]]])
(buri.test json-duplicate-key-malformed (buri.lt-parse "{c#34;ac#34;: 1, c#34;ac#34;: 2}") [malformed "ledger: json: duplicate key a"])
(buri.test json-float-malformed (buri.lt-parse "[1.5]") [malformed "ledger: json: only integer numbers are admitted"])
(buri.test json-trailing-malformed (buri.lt-parse "[] []") [malformed "ledger: json: trailing data"])
(buri.test json-unterminated-malformed (buri.lt-parse "[c#34;abc") [malformed "ledger: json: unterminated string"])
\\ Ledger text is data: a Shen form inside a string stays an inert string.
(buri.test json-code-is-inert (buri.lt-parse "[c#34;(simple-error boom)c#34;]") [arr [[str "(simple-error boom)"]]])
(buri.test fingerprint-order-independent (buri.ledger-fingerprint ["a" "b" "c"]) (buri.ledger-fingerprint ["c" "a" "b"]))
(buri.test fingerprint-detects-removal (= (buri.ledger-fingerprint ["a" "b" "c"]) (buri.ledger-fingerprint ["a" "b"])) false)

\\ Real ledger.
(set buri.lt-charter (buri.lread-json "spec/release-charter.json"))
(set buri.lt-plan (buri.lread-json "spec/end-to-end-plan.json"))
(set buri.lt-graph (buri.lread-json "spec/obligations.json"))
(set buri.lt-env (buri.ledger-env (value buri.lt-charter) (value buri.lt-plan) (value buri.lt-graph) "rocq/Audit.v"))
(define buri.lt-show [rejected Vs] -> (do (map (/. V (output "VIOLATION ~S~%" V)) Vs) [rejected (length Vs)])
  V -> V)
(define buri.lt-head [ledger-consistent | Rest] -> [ledger-consistent (hd Rest) (hd (tl Rest))]
  V -> (buri.lt-show V))
(buri.test real-ledger-consistent (buri.lt-head (buri.ledger-check))
 [ledger-consistent [charter-version 1] [fingerprint "lh61:95:414996911908889189"]])
(buri.test real-fingerprint-frozen (buri.ledger-fingerprint (buri.lcharter-required-ids (value buri.lt-charter))) "lh61:95:414996911908889189")

\\ Tree editing helpers for hostile variants.
(define buri.lt-put Key V [obj Pairs] -> [obj (buri.lt-put-h Key V Pairs)])
(define buri.lt-put-h Key V [] -> [[Key V]]
  Key V [[Key _] | Ps] -> [[Key V] | Ps]
  Key V [P | Ps] -> [P | (buri.lt-put-h Key V Ps)])
(define buri.lt-del Key [obj Pairs] -> [obj (buri.remove Key Pairs)])
(define buri.lt-edit-in Field Id F Obj ->
  (buri.lt-put Field [arr (map (/. X (if (= (buri.lfs "id" X) Id) (F X) X)) (buri.la (buri.lf Field Obj)))] Obj))
(define buri.lt-drop-in Field Id Obj ->
  (buri.lt-put Field [arr (buri.lfilter (/. X (not (= (buri.lfs "id" X) Id))) (buri.la (buri.lf Field Obj)))] Obj))
(define buri.lt-ob Id F -> (buri.lt-edit-in "obligations" Id F (value buri.lt-graph)))
(define buri.lt-strs Xs -> [arr (map (/. X [str X]) Xs)])
(define buri.lt-decide Charter Plan Graph -> (buri.ledger-decide Charter Plan Graph (value buri.lt-env)))
(define buri.lt-graph-verdict Graph -> (buri.lt-decide (value buri.lt-charter) (value buri.lt-plan) Graph))
(define buri.lt-charter-verdict Charter -> (buri.lt-decide Charter (value buri.lt-plan) (value buri.lt-graph)))
(define buri.lt-plan-verdict Plan -> (buri.lt-decide (value buri.lt-charter) Plan (value buri.lt-graph)))
(define buri.lt-has? Violation [rejected Vs] -> (buri.member? Violation Vs)
  _ _ -> false)
(define buri.lt-ev Kind Ref Est -> [obj [["kind" [str Kind]] ["ref" [str Ref]] ["establishes" [str Est]]]])
(define buri.lt-discharge Evidence O -> (buri.lt-put "evidence" [arr Evidence] (buri.lt-put "status" [str "discharged"] O)))

\\ Missing owner and unknown owner.
(buri.test hostile-missing-owner
 (buri.lt-has? [missing-owner "OB-NORMALIZER"] (buri.lt-graph-verdict (buri.lt-ob "OB-NORMALIZER" (/. O (buri.lt-del "owner" O))))) true)
(buri.test hostile-unknown-owner
 (buri.lt-has? [unknown-owner "OB-NORMALIZER E2E-77"]
  (buri.lt-graph-verdict (buri.lt-ob "OB-NORMALIZER" (/. O (buri.lt-put "owner" [str "E2E-77"] O))))) true)
(buri.test hostile-feature-missing-owner
 (buri.lt-has? [missing-owner "feature kl-let"]
  (buri.lt-charter-verdict (buri.lt-edit-in "features" "kl-let" (/. F (buri.lt-del "owner" F)) (value buri.lt-charter)))) true)

\\ Dangling dependencies.
(buri.test hostile-dangling-dependency
 (buri.lt-has? [dangling-dependency "OB-NORMALIZER -> OB-DOES-NOT-EXIST"]
  (buri.lt-graph-verdict (buri.lt-ob "OB-NORMALIZER" (/. O (buri.lt-put "depends_on" (buri.lt-strs ["OB-DOES-NOT-EXIST"]) O))))) true)
(buri.test hostile-dangling-package-dependency
 (buri.lt-has? [dangling-package-dependency "E2E-05 -> E2E-99"]
  (buri.lt-plan-verdict (buri.lt-edit-in "work_packages" "E2E-05" (/. P (buri.lt-put "depends_on" (buri.lt-strs ["E2E-04" "E2E-99"]) P)) (value buri.lt-plan)))) true)
(buri.test hostile-package-cycle
 (buri.lt-has? [package-cycle "E2E-01"]
  (buri.lt-plan-verdict (buri.lt-edit-in "work_packages" "E2E-01" (/. P (buri.lt-put "depends_on" (buri.lt-strs ["E2E-36"]) P)) (value buri.lt-plan)))) true)

\\ Cycles: unjustified, mixed joint tags, and joint cycles counted discharged.
(set buri.lt-cycle (buri.lt-ob "OB-NUMERIC-PROFILE" (/. O (buri.lt-put "depends_on" (buri.lt-strs ["OB-INT-REPRESENTATION"]) O))))
(buri.test hostile-unjustified-cycle (buri.lt-has? [unjustified-cycle "OB-NUMERIC-PROFILE"] (buri.lt-graph-verdict (value buri.lt-cycle))) true)
(buri.test hostile-unjustified-cycle-other-member (buri.lt-has? [unjustified-cycle "OB-INT-REPRESENTATION"] (buri.lt-graph-verdict (value buri.lt-cycle))) true)
(buri.test hostile-mixed-joint-cycle
 (buri.lt-has? [mixed-joint-invariant-cycle "OB-NUMERIC-PROFILE"]
  (buri.lt-graph-verdict (buri.lt-edit-in "obligations" "OB-NUMERIC-PROFILE" (/. O (buri.lt-put "joint_invariant" [str "JI-HEAP"] O)) (value buri.lt-cycle)))) true)
(buri.test hostile-joint-cycle-member-discharged
 (buri.lt-has? [cycle-member-discharged "OB-GC-CORRECTNESS"]
  (buri.lt-graph-verdict (buri.lt-ob "OB-GC-CORRECTNESS"
   (buri.lt-discharge [(buri.lt-ev "universal-theorem" "NativeReverse.divergence_equivalence" "implementation-correspondence")])))) true)
(buri.test hostile-joint-invariant-discharged
 (buri.lt-has? [joint-invariant-counted-discharged "JI-HEAP"]
  (buri.lt-graph-verdict (buri.lt-edit-in "joint_invariants" "JI-HEAP" (/. J (buri.lt-put "status" [str "discharged"] J)) (value buri.lt-graph)))) true)
(buri.test hostile-unknown-joint-invariant
 (buri.lt-has? [unknown-joint-invariant "OB-GC-CORRECTNESS JI-NOPE"]
  (buri.lt-graph-verdict (buri.lt-ob "OB-GC-CORRECTNESS" (/. O (buri.lt-put "joint_invariant" [str "JI-NOPE"] O))))) true)

\\ Evidence kinds: sampled/ground evidence cannot discharge a universal obligation.
(buri.test hostile-sampled-claims-universal
 (buri.lt-has? [insufficient-discharge-evidence "OB-READER-CANONICALIZATION"]
  (buri.lt-graph-verdict (buri.lt-ob "OB-READER-CANONICALIZATION" (/. O (buri.lt-put "status" [str "discharged"] O))))) true)
(buri.test hostile-exhaustive-host-test-claims-universal
 (buri.lt-has? [insufficient-discharge-evidence "OB-NORMALIZER"]
  (buri.lt-graph-verdict (buri.lt-ob "OB-NORMALIZER"
   (buri.lt-discharge [(buri.lt-ev "exhaustive-host-test" "tests/trust.shen" "implementation-correspondence")])))) true)
(buri.test hostile-ground-claims-universal
 (buri.lt-has? [insufficient-discharge-evidence "OB-NORMALIZER"]
  (buri.lt-graph-verdict (buri.lt-ob "OB-NORMALIZER"
   (buri.lt-discharge [(buri.lt-ev "ground-derivation" "compiler_result" "implementation-correspondence")])))) true)
(buri.test hostile-model-theorem-claims-implementation
 (buri.lt-has? [insufficient-discharge-evidence "OB-NORMALIZER"]
  (buri.lt-graph-verdict (buri.lt-ob "OB-NORMALIZER"
   (buri.lt-discharge [(buri.lt-ev "universal-theorem" "compiler_continuation" "model-proof")])))) true)

\\ Forged discharged labels: unaudited theorem, or discharge over open premises.
(buri.test hostile-forged-discharged-label
 (buri.lt-has? [unaudited-theorem "OB-SCHEME-EMIT-IF Forged.emit_if_correct"]
  (buri.lt-graph-verdict (buri.lt-ob "OB-SCHEME-EMIT-IF"
   (buri.lt-discharge [(buri.lt-ev "universal-theorem" "Forged.emit_if_correct" "implementation-correspondence")])))) true)
(buri.test hostile-discharged-over-open-dependency
 (buri.lt-has? [discharged-over-open-dependency "OB-SCHEME-MERGE-LETS"]
  (buri.lt-graph-verdict (buri.lt-ob "OB-SCHEME-MERGE-LETS" (/. O (buri.lt-put "status" [str "discharged"] O))))) true)
(buri.test hostile-refuted-without-counterexample
 (buri.lt-has? [refuted-without-counterexample "OB-NORMALIZER"]
  (buri.lt-graph-verdict (buri.lt-ob "OB-NORMALIZER" (/. O (buri.lt-put "replaced_by" [str "OB-BYTE-DOMAIN"] (buri.lt-put "status" [str "refuted"] O)))))) true)
(buri.test hostile-forged-status-word
 (buri.lt-has? [unknown-status "OB-NORMALIZER"]
  (buri.lt-graph-verdict (buri.lt-ob "OB-NORMALIZER" (/. O (buri.lt-put "status" [str "proved"] O))))) true)
(buri.test hostile-forged-package-complete
 (buri.lt-has? [complete-package-with-open-obligation "E2E-01"]
  (buri.lt-plan-verdict (buri.lt-edit-in "work_packages" "E2E-01" (/. P (buri.lt-put "status" [str "complete"] P)) (value buri.lt-plan)))) true)
(buri.test hostile-forged-plan-complete
 (buri.lt-has? [forged-plan-completion "full_plan_complete"]
  (buri.lt-plan-verdict (buri.lt-put "full_plan_complete" [bool true] (value buri.lt-plan)))) true)
(buri.test hostile-orphan-package
 (buri.lt-has? [package-owns-no-obligation "E2E-13"]
  (buri.lt-graph-verdict (buri.lt-ob "OB-LIBRARY-SURFACE" (/. O (buri.lt-put "owner" [str "E2E-12"] O))))) true)

\\ Charter: silently dropped features, properties and pins.
(set buri.lt-dropped (buri.lt-drop-in "features" "prim-vectors" (value buri.lt-charter)))
(buri.test hostile-feature-silently-dropped
 (buri.lt-has? [required-set-differs-from-history "latest"] (buri.lt-charter-verdict (value buri.lt-dropped))) true)
(set buri.lt-dropped-fp (buri.ledger-fingerprint (buri.lcharter-required-ids (value buri.lt-dropped))))
\\ Rewriting history and the recorded fingerprint does not help: the frozen registry disagrees.
(set buri.lt-forged-history
 (buri.lt-put "required_feature_fingerprint" [str (value buri.lt-dropped-fp)]
  (buri.lt-put "history" [arr [[obj [["version" [int 1]] ["removed" [arr []]]
     ["required" (buri.lt-strs (buri.lcharter-required-ids (value buri.lt-dropped)))]]]]] (value buri.lt-dropped))))
(buri.test hostile-feature-dropped-with-forged-history
 (buri.lt-has? [required-feature-set-changed-without-version-change (value buri.lt-dropped-fp)]
  (buri.lt-charter-verdict (value buri.lt-forged-history))) true)
(buri.test hostile-feature-dropped-forged-history-only-violation
 (buri.lt-charter-verdict (value buri.lt-forged-history))
 [rejected [[required-feature-set-changed-without-version-change (value buri.lt-dropped-fp)]]])
\\ A version bump that omits the removal record is a silent removal.
(buri.test hostile-version-bump-without-removal-record
 (buri.lt-has? [silent-feature-removal "feature:prim-vectors"]
  (buri.lt-charter-verdict
   (buri.lt-put "charter_version" [int 2]
    (buri.lt-put "history" [arr [(hd (buri.la (buri.lf "history" (value buri.lt-charter))))
       [obj [["version" [int 2]] ["removed" [arr []]] ["required" (buri.lt-strs (buri.lcharter-required-ids (value buri.lt-dropped)))]]]]]
     (value buri.lt-dropped))))) true)
\\ Even a recorded removal is a charter change: it needs a new frozen row in shen/ledger.shen.
(buri.test version-bump-with-removal-record-needs-frozen-row
 (buri.lt-charter-verdict
  (buri.lt-put "required_feature_fingerprint" [str (value buri.lt-dropped-fp)]
   (buri.lt-put "charter_version" [int 2]
    (buri.lt-put "history" [arr [(hd (buri.la (buri.lf "history" (value buri.lt-charter))))
       [obj [["version" [int 2]] ["removed" [arr [[obj [["id" [str "feature:prim-vectors"]] ["reason" [str "test"]]]]]]]
             ["required" (buri.lt-strs (buri.lcharter-required-ids (value buri.lt-dropped)))]]]]]
     (value buri.lt-dropped)))))
 [rejected [[required-feature-set-changed-without-version-change (value buri.lt-dropped-fp)]
            [stale-charter-reference "obligation graph"]]])
(buri.test hostile-legacy-inventory-unmapped
 (buri.lt-has? [unmapped-legacy-obligation "gc-and-memory"]
  (buri.lt-graph-verdict (buri.lt-put "legacy_inventory_map"
   [arr (buri.lfilter (/. E (not (= (buri.lfs "legacy" E) "gc-and-memory"))) (buri.la (buri.lf "legacy_inventory_map" (value buri.lt-graph))))]
   (value buri.lt-graph)))) true)
(buri.test hostile-joint-member-mismatch
 (buri.lt-has? [joint-invariant-member-mismatch "JI-HEAP"]
  (buri.lt-graph-verdict (buri.lt-edit-in "joint_invariants" "JI-HEAP" (/. J (buri.lt-put "members" (buri.lt-strs ["OB-GC-CORRECTNESS"]) J)) (value buri.lt-graph)))) true)
(buri.test hostile-property-kind-dropped
 (buri.lt-has? [missing-property-kind "confidentiality"]
  (buri.lt-charter-verdict (buri.lt-drop-in "properties" "confidentiality" (value buri.lt-charter)))) true)
(buri.test hostile-pin-record-dropped
 (buri.lt-has? [missing-pin-record "arm-architecture"]
  (buri.lt-charter-verdict (buri.lt-drop-in "pins" "arm-architecture" (value buri.lt-charter)))) true)
(buri.test hostile-invented-pin
 (buri.lt-has? [invented-pin-value "arm-abi"]
  (buri.lt-charter-verdict (buri.lt-edit-in "pins" "arm-abi" (/. P (buri.lt-put "value" [str "AAPCS64"] P)) (value buri.lt-charter)))) true)
(buri.test hostile-exclusion-without-enforcement
 (buri.lt-has? [exclusion-without-enforcement-test "num-floats"]
  (buri.lt-charter-verdict (buri.lt-edit-in "features" "num-floats"
   (/. F (buri.lt-put "exclusion" (buri.lt-put "enforcement_tests" [arr []] (buri.lf "exclusion" F)) F)) (value buri.lt-charter)))) true)
(buri.test hostile-exclusion-unregistered-test
 (buri.lt-has? [unregistered-enforcement-test "num-floats no-such-test"]
  (buri.lt-charter-verdict (buri.lt-edit-in "features" "num-floats"
   (/. F (buri.lt-put "exclusion" (buri.lt-put "enforcement_tests"
     [arr [[obj [["file" [str "tests/evaluator.shen"]] ["test" [str "no-such-test"]]]]]] (buri.lf "exclusion" F)) F)) (value buri.lt-charter)))) true)
(buri.test hostile-stale-charter-reference
 (buri.lt-has? [stale-charter-reference "obligation graph"]
  (buri.lt-graph-verdict (buri.lt-put "charter_version" [int 2] (value buri.lt-graph)))) true)

\\ Distinct non-policy outcomes.
(buri.test hostile-unsupported-schema
 (buri.lt-graph-verdict (buri.lt-put "schema" [str "buri-obligation-graph-9"] (value buri.lt-graph)))
 [unsupported-schema ["buri-release-charter-1" "buri-end-to-end-plan-1" "buri-obligation-graph-9"]])
(buri.test hostile-shape-malformed
 (buri.lt-graph-verdict (buri.lt-ob "OB-NORMALIZER" (/. O (buri.lt-put "evidence" [str "trust me"] O))))
 [malformed "ledger: shape: array expected"])
(buri.test missing-ledger-file-is-not-rejection
 (hd (buri.ledger-check-files "spec/no-such-charter.json" "spec/end-to-end-plan.json" "spec/obligations.json" "rocq/Audit.v"))
 unknown)
(buri.done)
