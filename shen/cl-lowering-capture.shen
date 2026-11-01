\\ Inert capture of Shen-CL conditional lowering source (src/compiler.shen).
\\ This is a port adapter, not a checker: it lexes bytes, never calls Shen's
\\ reader, macroexpander, package expander, EVAL, or host loading. Rocq admits
\\ the emitted AST against a reviewed expected AST; this file decides nothing.
\\ Supported token classes: ( ) [ ] | "strings" atoms, \\ line and \* *\ block
\\ comments. Non-ASCII bytes outside comments are rejected, not decoded.

(define buri.cll-space? B -> (element? B [9 10 12 13 32]))
(define buri.cll-delim? B -> (or (buri.cll-space? B) (element? B [34 40 41 91 93 124])))

(define buri.cll-lex Bytes -> (reverse (buri.cll-lex-h Bytes 0 [])))
(define buri.cll-lex-h
  [] _ Acc -> Acc
  [92 92 | R] P Acc -> (buri.cll-skip-line R (+ P 2) Acc)
  [92 42 | R] P Acc -> (buri.cll-skip-block R (+ P 2) Acc)
  [B | R] P Acc -> (buri.cll-lex-h R (+ P 1) Acc) where (buri.cll-space? B)
  [40 | R] P Acc -> (buri.cll-lex-h R (+ P 1) [[open P] | Acc])
  [41 | R] P Acc -> (buri.cll-lex-h R (+ P 1) [[close (+ P 1)] | Acc])
  [91 | R] P Acc -> (buri.cll-lex-h R (+ P 1) [[lbrack P] | Acc])
  [93 | R] P Acc -> (buri.cll-lex-h R (+ P 1) [[rbrack P] | Acc])
  [124 | R] P Acc -> (buri.cll-lex-h R (+ P 1) [[bar P] | Acc])
  [34 | R] P Acc -> (buri.cll-string R (+ P 1) [] Acc)
  Bytes P Acc -> (buri.cll-atom Bytes P [] Acc))
(define buri.cll-skip-line
  [] P Acc -> Acc
  [10 | R] P Acc -> (buri.cll-lex-h R (+ P 1) Acc)
  [_ | R] P Acc -> (buri.cll-skip-line R (+ P 1) Acc))
(define buri.cll-skip-block
  [] _ _ -> (simple-error "unterminated block comment")
  [42 92 | R] P Acc -> (buri.cll-lex-h R (+ P 2) Acc)
  [_ | R] P Acc -> (buri.cll-skip-block R (+ P 1) Acc))
(define buri.cll-ascii B -> (if (and (>= B 32) (< B 127)) (n->string B)
                               (simple-error "unsupported byte in token")))
(define buri.cll-text Rev -> (buri.cll-text-h (reverse Rev) ""))
(define buri.cll-text-h [] S -> S [B | Bs] S -> (buri.cll-text-h Bs (cn S (buri.cll-ascii B))))
(define buri.cll-string
  [] _ _ _ -> (simple-error "unterminated string")
  [34 | R] P Chars Acc -> (buri.cll-lex-h R (+ P 1) [[str (buri.cll-text Chars)] | Acc])
  [B | R] P Chars Acc -> (buri.cll-string R (+ P 1) [B | Chars] Acc))
(define buri.cll-atom
  [B | R] P Chars Acc -> (buri.cll-atom R (+ P 1) [B | Chars] Acc)
      where (not (buri.cll-delim? B))
  Bytes P Chars Acc -> (buri.cll-lex-h Bytes P [[atom (buri.cll-text Chars)] | Acc]))

\\ Numerals: optional "-", decimal digits, optional "." digits. Everything
\\ else is a symbol spelling; package resolution is left to the Rocq model.
(define buri.cll-digit? C -> (element? C ["0" "1" "2" "3" "4" "5" "6" "7" "8" "9"]))
(define buri.cll-digits? "" -> false S -> (buri.cll-digits-h? S))
(define buri.cll-digits-h? "" -> true
  S -> (and (buri.cll-digit? (pos S 0)) (buri.cll-digits-h? (tlstr S))))
(define buri.cll-numeral? "" -> false
  S -> (buri.cll-unsigned? (tlstr S)) where (= (pos S 0) "-")
  S -> (buri.cll-unsigned? S))
(define buri.cll-unsigned? S -> (buri.cll-unsigned-h S ""))
(define buri.cll-unsigned-h
  "" Int -> (buri.cll-digits? Int)
  (@s "." Frac) Int -> (and (buri.cll-digits? Int) (buri.cll-digits? Frac))
  (@s C Rest) Int -> (buri.cll-unsigned-h Rest (cn Int C)))
(define buri.cll-atom-node S -> (if (buri.cll-numeral? S) [num S] [sym S]))

\\ Parse returns [Node | RemainingTokens]; parens carry [Start End] spans.
(define buri.cll-parse-all Tokens -> (buri.cll-parse-all-h Tokens []))
(define buri.cll-parse-all-h
  [] Acc -> (reverse Acc)
  Tokens Acc -> (let R (buri.cll-parse Tokens) (buri.cll-parse-all-h (tl R) [(hd R) | Acc])))
(define buri.cll-parse
  [[open P] | R] -> (buri.cll-items R close P [])
  [[lbrack P] | R] -> (buri.cll-items R rbrack P [])
  [[bar _] | R] -> [[bar] | R]
  [[str S] | R] -> [[str S] | R]
  [[atom S] | R] -> [(buri.cll-atom-node S) | R]
  _ -> (simple-error "unbalanced source"))
(define buri.cll-items
  [] _ _ _ -> (simple-error "unterminated list")
  [[close E] | R] close P Acc -> [[paren (reverse Acc) P E] | R]
  [[rbrack _] | R] rbrack _ Acc -> [[brack (reverse Acc)] | R]
  [[close _] | _] _ _ _ -> (simple-error "mismatched close")
  [[rbrack _] | _] _ _ _ -> (simple-error "mismatched bracket")
  Tokens Close P Acc -> (let R (buri.cll-parse Tokens) (buri.cll-items (tl R) Close P [(hd R) | Acc])))

\\ Spans are provenance only; admitted ASTs never contain them.
(define buri.cll-strip
  [paren Items _ _] -> [paren (map (/. X (buri.cll-strip X)) Items)]
  [brack Items] -> [brack (map (/. X (buri.cll-strip X)) Items)]
  X -> X)

(define buri.cll-wanted -> ["emit-boolean" "optimise-boolean-check" "optimise-boolean-sequence" "emit-if"])

\\ Select the unique (package Name External ...) form and, inside it, each
\\ wanted top-level define exactly once.
(define buri.cll-package
  [[paren [[sym "package"] Name External | Body] _ _]] -> [Name External Body]
  _ -> (simple-error "expected exactly one top-level package form"))
(define buri.cll-defines Name [] -> []
  Name [[paren [[sym "define"] [sym Name] | Rest] S E] | Forms]
  -> [[paren [[sym "define"] [sym Name] | Rest] S E] | (buri.cll-defines Name Forms)]
  Name [_ | Forms] -> (buri.cll-defines Name Forms))
(define buri.cll-select Body Name ->
  (let Found (buri.cll-defines Name Body)
    (if (= (length Found) 1) (hd Found)
        (simple-error (cn "definition not unique: " Name)))))

\\ Mutations exist only to test that Rocq admission rejects changed sources.
(define buri.cll-subst Old New X -> New where (= X Old)
  Old New [paren Items] -> [paren (map (/. Y (buri.cll-subst Old New Y)) Items)]
  Old New [brack Items] -> [brack (map (/. Y (buri.cll-subst Old New Y)) Items)]
  _ _ X -> X)
(define buri.cll-ce V -> [paren [[sym "compile-expression"] [sym V] [sym "Scope"]]])
(define buri.cll-mutate
  none _ X -> X
  dropped-guard "optimise-boolean-check" X
  -> (buri.cll-subst [brack [[sym "true?"] [sym "Exp"]]] [sym "Exp"] X)
  cl-truthiness "emit-if" X
  -> (buri.cll-subst [paren [[sym "optimise-boolean-check"] (buri.cll-ce "Test")]] (buri.cll-ce "Test") X)
  swapped-branches "emit-if" X
  -> (buri.cll-subst [sym "Swap"] (buri.cll-ce "Else")
      (buri.cll-subst (buri.cll-ce "Else") (buri.cll-ce "Then")
       (buri.cll-subst (buri.cll-ce "Then") [sym "Swap"] X)))
  eq-for-equal "optimise-boolean-check" X
  -> (buri.cll-subst [paren [[sym "kl"] [sym "absequal"]]] [paren [[sym "cl"] [sym "eq"]]] X)
  _ _ X -> X)

\\ Rocq rendering: strings are emitted with doubled quotes.
(define buri.cll-coq-string S -> (cn (n->string 34) (cn (buri.cll-coq-esc S) (n->string 34))))
(define buri.cll-coq-esc "" -> ""
  (@s C Rest) -> (cn (if (= C (n->string 34)) (cn C C) C) (buri.cll-coq-esc Rest)))
(define buri.cll-coq
  [sym S] -> (cn "(SSym " (cn (buri.cll-coq-string S) ")"))
  [str S] -> (cn "(SStr " (cn (buri.cll-coq-string S) ")"))
  [num S] -> (cn "(SNum " (cn (buri.cll-coq-string S) ")"))
  [bar] -> "SBar"
  [paren Items] -> (cn "(SParen " (cn (buri.cll-coq-items Items) ")"))
  [brack Items] -> (cn "(SBrack " (cn (buri.cll-coq-items Items) ")"))
  _ -> (simple-error "unsupported capture node"))
(define buri.cll-coq-items [] -> "SNil"
  [X | Xs] -> (cn "(SCons " (cn (buri.cll-coq X) (cn " " (cn (buri.cll-coq-items Xs) ")")))))
(define buri.cll-nl -> (n->string 10))
(define buri.cll-span-line Name [paren _ S E] ->
  (make-string "(* span ~A bytes [~A, ~A) *)~A" Name S E (buri.cll-nl)))
(define buri.cll-def-line Coq Node ->
  (cn "Definition " (cn Coq (cn " : src := " (cn (buri.cll-coq Node) (cn "." (buri.cll-nl)))))))

\\ Source and Blob are provenance strings supplied by the orchestrating gate.
(define buri.cll-capture Source Blob Out Mode ->
  (let Forms (buri.cll-parse-all (buri.cll-lex (read-file-as-bytelist Source)))
       Pkg (buri.cll-package Forms)
       Header [paren [[sym "package"] (hd Pkg) (hd (tl Pkg))]]
       Defs (map (/. N (buri.cll-select (hd (tl (tl Pkg))) N)) (buri.cll-wanted))
       Names ["captured_emit_boolean" "captured_optimise" "captured_sequence" "captured_emit_if"]
       Stripped (map (/. D (buri.cll-strip D)) Defs)
       Mutated (buri.cll-mutate-all Mode (buri.cll-wanted) Stripped)
       Sys (buri.cll-sysfuncs Stripped)
       Text (buri.cll-module Blob Header (buri.cll-wanted) Names Defs Mutated Sys)
    (do (write-to-file Out Text) captured)))
(define buri.cll-mutate-all _ [] [] -> []
  Mode [N | Ns] [D | Ds] -> [(buri.cll-mutate Mode N D) | (buri.cll-mutate-all Mode Ns Ds)])
(define buri.cll-spans [] [] -> ""
  [N | Ns] [D | Ds] -> (cn (buri.cll-span-line N D) (buri.cll-spans Ns Ds)))
(define buri.cll-defs [] [] -> ""
  [N | Ns] [D | Ds] -> (cn (buri.cll-def-line N D) (buri.cll-defs Ns Ds)))
\\ Host observation recorded as capture data: which captured spellings the
\\ capture host's kernel table reports as system functions. Rocq compares it
\\ with a reviewed table; it is an environment contract, not a proof.
(define buri.cll-symbols
  [sym S] Acc -> (if (element? S Acc) Acc [S | Acc])
  [paren Items] Acc -> (buri.cll-symbols-list Items Acc)
  [brack Items] Acc -> (buri.cll-symbols-list Items Acc)
  _ Acc -> Acc)
(define buri.cll-symbols-list [] Acc -> Acc
  [X | Xs] Acc -> (buri.cll-symbols-list Xs (buri.cll-symbols X Acc)))
(define buri.cll-sysfuncs Defs ->
  (reverse (buri.cll-sysfunc-filter (buri.cll-symbols-list Defs []))))
(define buri.cll-sysfunc-filter [] -> []
  [S | Ss] -> [S | (buri.cll-sysfunc-filter Ss)] where (shen.sysfunc? (intern S))
  [_ | Ss] -> (buri.cll-sysfunc-filter Ss))
(define buri.cll-coq-strings [] -> "[]"
  [S | Ss] -> (cn "[" (cn (buri.cll-coq-string S) (cn (buri.cll-coq-strings-h Ss) "]"))))
(define buri.cll-coq-strings-h [] -> ""
  [S | Ss] -> (cn "; " (cn (buri.cll-coq-string S) (buri.cll-coq-strings-h Ss))))
(define buri.cll-module Blob Header Wanted Names Spanned Defs Sys ->
  (cn (make-string "(* Generated by shen/cl-lowering-capture.shen. Inert reader-level capture.~A   Shen-CL 4844072dde0208c3e4b99dcbfea58e4fdfd812e8 src/compiler.shen blob ~A *)~A" (buri.cll-nl) Blob (buri.cll-nl))
  (cn (buri.cll-spans Wanted Spanned)
  (cn (make-string "From Coq Require Import String List.~AImport ListNotations.~AFrom Buri Require Import CLLowering.~AOpen Scope string_scope.~A" (buri.cll-nl) (buri.cll-nl) (buri.cll-nl) (buri.cll-nl))
  (cn (buri.cll-def-line "captured_package" Header)
  (cn (buri.cll-defs Names Defs)
  (cn (make-string "Definition captured_sysfuncs : list string := ~A.~A" (buri.cll-coq-strings Sys) (buri.cll-nl))
  (cn (make-string "Definition captured_lowering : lowering_source := mk_lowering_source captured_package captured_emit_boolean captured_optimise captured_sequence captured_emit_if captured_sysfuncs.~A" (buri.cll-nl))
  (buri.cll-module-tail)))))))))
\\ The generated module also instantiates the universal theorems at the capture.
(define buri.cll-module-tail ->
  (buri.cll-lines
   ["Theorem captured_lowering_admitted : admitted_lowering captured_lowering = true."
    "Proof. vm_compute. reflexivity. Qed."
    "Theorem captured_optimise_sound : forall St prim other ce n v r,"
    " primitive_contracts St prim -> run n (lowering_defs captured_lowering) ce OPT [v] = LOk r ->"
    " qsafe v = true -> OptEquiv St prim other v r."
    "Proof. intros. eapply admitted_optimise_sound; eauto. exact captured_lowering_admitted. Qed."
    "Theorem captured_emit_if_refines : forall St prim other ce n t th el sc r,"
    " primitive_contracts St prim -> run n (lowering_defs captured_lowering) ce EMIT_IF [t; th; el; sc] = LOk r ->"
    " (t = VSym c#34;truec#34; /\ ce th sc = LOk r) \/ (t = VSym c#34;falsec#34; /\ ce el sc = LOk r) \/"
    " (exists c a b, ce t sc = LOk c /\ ce th sc = LOk a /\ ce el sc = LOk b /\"
    "   (qsafe c = true -> forall e s o, ev St prim other e r s o <-> shen_if St prim other e c a b s o))."
    "Proof. intros. eapply admitted_emit_if_refines; eauto. exact captured_lowering_admitted. Qed."]))
(define buri.cll-lines [] -> ""
  [L | Ls] -> (cn L (cn (buri.cll-nl) (buri.cll-lines Ls))))
