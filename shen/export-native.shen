\\ Translation validation captures the ACTUAL _scm compiler output.
\\ The decoders/source correspondence are not yet proved; see TRUST.md.
(tc -)
(define buri.position X [X | _] -> 0 X [_ | Xs] -> (+ 1 (buri.position X Xs))
  _ [] -> (simple-error "Unbound compiler-schema variable"))
(define buri.native-coq Prefix N Scope -> (cn "(" (cn Prefix (cn "Lit (" (cn (str N) "))")))) where (buri.exact-integer? N)
  Prefix X Scope -> (cn "(" (cn Prefix (cn "Var " (cn (str (buri.position X Scope)) ")")))) where (symbol? X)
  Prefix [+ A B] Scope -> (buri.native-coq-binary Prefix "Add" A B Scope)
  Prefix [- A B] Scope -> (buri.native-coq-binary Prefix "Sub" A B Scope)
  Prefix [* A B] Scope -> (buri.native-coq-binary Prefix "Mul" A B Scope)
  "K" [let X A B] Scope -> (buri.native-coq-let "K" X A B Scope)
  "S" [let [[X A]] B] Scope -> (buri.native-coq-let "S" X A B Scope)
  "S" [let* Bindings B] Scope -> (buri.native-coq-let-star Bindings B Scope)
  _ _ _ -> (simple-error "Unsupported actual compiler output"))
(define buri.native-coq-binary P Op A B Scope ->
  (cn "(" (cn P (cn Op (cn " " (cn (buri.native-coq P A Scope)
    (cn " " (cn (buri.native-coq P B Scope) ")"))))))))
(define buri.native-coq-let P X A B Scope ->
  (cn "(" (cn P (cn "Let " (cn (buri.native-coq P A Scope)
    (cn " " (cn (buri.native-coq P B [X | Scope]) ")")))))))
(define buri.native-coq-let-star [] B Scope -> (buri.native-coq "S" B Scope)
  [[X A] | Rest] B Scope ->
    (cn "(SLet " (cn (buri.native-coq "S" A Scope)
      (cn " " (cn (buri.native-coq-let-star Rest B [X | Scope]) ")")))))
(define buri.export-schema [Name Scope Source] N Stream Transcript ->
  (let Target (_scm.compile-expression Source Scope)
       TheoremName (cn "native_schema_" (str N))
       Text (cn "Theorem " (cn TheoremName
        (cn " : forall rho, keval rho " (cn (buri.native-coq "K" Source Scope)
         (cn " = seval rho " (cn (buri.native-coq "S" Target Scope)
          (cn ".
Proof. reflexivity. Qed.
Print Assumptions " (cn TheoremName ".
"))))))))
    (do (pr (make-string "~S~%" [schema Name inputs Scope source Source emitted Target]) Transcript)
        (pr Text Stream))))
(define buri.export-schemas [] _ _ _ -> done
  [Schema | Schemas] N Out Transcript ->
    (do (buri.export-schema Schema N Out Transcript)
        (buri.export-schemas Schemas (+ N 1) Out Transcript)))
(define buri.export-native Path Log ->
  (let Out (open Path out) Transcript (open Log out)
    (do (pr "(* Generated from pinned Shen-Scheme compiler output. *)
From Coq Require Import ZArith.
From Buri Require Import NativeArithmetic.
Open Scope Z_scope.
" Out)
      (do (buri.export-schemas (buri.compiler-schemas) 0 Out Transcript)
        (do (close Out) (close Transcript))))))
