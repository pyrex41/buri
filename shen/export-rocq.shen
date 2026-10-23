\\ Untrusted exporter. Rocq checks each emitted proposition. The byte/source
\\ correspondence of this exporter remains in the bridge trust boundary.
(tc -)
(define buri.coq-name
  zero -> "O" succ -> "S" lit -> "Lit" add -> "Add" mul -> "Mul"
  nil -> "nil" cons -> "cons" halt -> "Halt" push -> "Push"
  plus -> "Plus" times -> "Times" ok -> "Ok" fault -> "Fault"
  nadd -> "nadd" nmul -> "nmul" eval -> "eval" compile -> "compile" run -> "run"
  _ -> (simple-error "Unsupported Rocq symbol"))
(define buri.coq-sort nat -> "nat" expr -> "expr" code -> "code" stack -> "stack" outcome -> "outcome"
  _ -> (simple-error "Unsupported Rocq sort"))
(define buri.coq-term [v X] -> (cn "v_" (str X))
  [F] -> (buri.coq-name F)
  [F | As] -> (cn "(" (cn (buri.coq-name F) (cn (buri.coq-args As) ")"))))
(define buri.coq-args [] -> ""
  [A | As] -> (cn " " (cn (buri.coq-term A) (buri.coq-args As))))
(define buri.coq-vars [] -> ""
  [[X S] | Vs] -> (cn " (" (cn "v_" (cn (str X) (cn " : " (cn (buri.coq-sort S) (cn ")" (buri.coq-vars Vs))))))))
(define buri.coq-statement Vars L R ->
  (cn (if (= Vars []) "" (cn "forall" (cn (buri.coq-vars Vars) ", ")))
      (cn (buri.coq-term L) (cn " = " (buri.coq-term R)))))
(define buri.coq-rule [_ Vs L R] N ->
  (cn "Lemma equation_" (cn (str N) (cn " : " (cn (buri.coq-statement Vs L R)
    ".
Proof. reflexivity. Qed.
")))))
(define buri.coq-rules [] _ -> ""
  [R | Rs] N -> (cn (buri.coq-rule R N) (buri.coq-rules Rs (+ N 1))))
(define buri.coq-claim [theorem Name Vs L R _] ->
  (cn "Theorem exported_" (cn (buri.coq-theorem Name)
   (cn " : " (cn (buri.coq-statement Vs L R)
    (cn ".
Proof. apply " (cn (buri.coq-theorem Name) ". Qed.
")))))))
(define buri.coq-theorem compiler-continuation -> "compiler_continuation"
  compiler-result -> "compiler_result" _ -> (simple-error "Unsupported theorem export"))
(define buri.export-rocq Path ->
  (let Stream (open Path out)
       Text (cn "(* Generated from the loaded Shen equation theory and theorem statements. *)
From Buri Require Import Arithmetic.
"
              (cn (buri.coq-rules (buri.rules) 0)
                (cn (buri.coq-claim (buri.compiler-theorem))
                    (buri.coq-claim (buri.halt-theorem)))))
    (do (pr Text Stream) (close Stream))))
