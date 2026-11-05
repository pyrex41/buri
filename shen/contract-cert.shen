\\ E2E-08: the BURI/KL-CONTRACT-1 certificate checker (executable acceptance).
\\ Certificates are inert data: this file performs no proof search, no eval,
\\ no loading and no host callback. It decides identity binding (theory,
\\ program fingerprint, captured evaluator), declaration discipline for named
\\ host contracts, the measure discipline of total-correctness certificates,
\\ and the exact rule-to-syntax fit of every derivation skeleton. Semantic side
\\ conditions are returned as named obligations, never decided.
\\
\\ Rocq counterpart: rocq/ContractCert.v (check). That this file computes the
\\ same function is NOT proved (obligation CONTRACT-CERT-SHEN); the
\\ correspondence is sampled agreement on the cases of tests/contracts.shen.
\\
\\ Data formats (names are Shen strings):
\\   Expr  ::= [num Z] | [float N] | [str S] | [sym S] | [bool B] | [nil] | [var X]
\\           | [lambda X E] | [let X E E] | [if E E E] | [and E E] | [or E E]
\\           | [cond [[E E] ...]] | [trap E E] | [freeze E] | [type E]
\\           | [defun F [X ...] E] | [app E [E ...]] | [call F [E ...]]
\\   Program ::= [program [[F [X ...] E] ...] E]
\\   Skel  ::= [rule R [Skel ...]] | [hyp S] | [prim S] | [rec S] | [side S]
\\   Cert  ::= [contract-certificate Format [theory S N] [program S N] [evaluator S N]
\\              [statement S Mode] [hypotheses [S ...]] [measures [[S S] ...]]
\\              [bodies [[S Skel] ...]] [main Skel]]
\\   Mode  ::= partial | total | always
\\   Verdict ::= [accepted [S Mode] Premises Prims Obligations] | [rejected Reason]
(tc -)

\\ ---------------------------------------------------------------------------
\\ Fingerprint: Horner hash base 257 modulo 2^61-1 from 7, each code point c
\\ contributing c + 1 (rocq/ContractCert.v lh). Exact integer +, *, - only.
(define buri.cc-prime -> 2305843009213693951)
(define buri.cc-multiples M 0 Acc -> [M | Acc]
  M K Acc -> (buri.cc-multiples (+ M M) (- K 1) [M | Acc]))
(define buri.cc-reduce A [] -> A
  A [D | Ds] -> (buri.cc-reduce (if (>= A D) (- A D) A) Ds))
(define buri.cc-mod A -> (buri.cc-reduce A (buri.cc-multiples (buri.cc-prime) 9 [])))
(define buri.cc-step H C -> (buri.cc-mod (+ (* H 257) (+ C 1))))
(define buri.cc-hash-codes H [] -> H
  H [C | Cs] -> (buri.cc-hash-codes (buri.cc-step H C) Cs))
(define buri.cc-hash-string S -> (buri.cc-hash-codes 7 (map (/. Ch (string->n Ch)) (explode S))))
\\ The captured evaluator identity is the same hash over the bytes of its capture.
(define buri.cc-hash-file Path -> (buri.cc-hash-codes 7 (read-file-as-bytelist Path)))

\\ ---------------------------------------------------------------------------
\\ Canonical serialization (rocq/ContractCert.v ser, ser_program).
(define buri.cc-len S -> (length (explode S)))
(define buri.cc-lp X -> (cn (str (buri.cc-len X)) (cn ":" X)))
(define buri.cc-ser
  [num Z] -> (cn "(n " (cn (str Z) ")"))
  [float B] -> (cn "(f " (cn (str B) ")"))
  [str S] -> (cn "(s " (cn (buri.cc-lp S) ")"))
  [sym X] -> (cn "(y " (cn (buri.cc-lp X) ")"))
  [bool true] -> "(b true)"
  [bool false] -> "(b false)"
  [nil] -> "(nil)"
  [var X] -> (cn "(v " (cn (buri.cc-lp X) ")"))
  [lambda X B] -> (cn "(lambda " (cn (buri.cc-lp X) (cn " " (cn (buri.cc-ser B) ")"))))
  [let X A B] -> (cn "(let " (cn (buri.cc-lp X) (cn " " (cn (buri.cc-ser A) (cn " " (cn (buri.cc-ser B) ")"))))))
  [if C A B] -> (cn "(if " (cn (buri.cc-ser C) (cn " " (cn (buri.cc-ser A) (cn " " (cn (buri.cc-ser B) ")"))))))
  [and A B] -> (cn "(and " (cn (buri.cc-ser A) (cn " " (cn (buri.cc-ser B) ")"))))
  [or A B] -> (cn "(or " (cn (buri.cc-ser A) (cn " " (cn (buri.cc-ser B) ")"))))
  [cond Cs] -> (cn "(cond" (cn (buri.cc-ser-clauses Cs) ")"))
  [trap A H] -> (cn "(trap " (cn (buri.cc-ser A) (cn " " (cn (buri.cc-ser H) ")"))))
  [freeze A] -> (cn "(freeze " (cn (buri.cc-ser A) ")"))
  [type A] -> (cn "(type " (cn (buri.cc-ser A) ")"))
  [defun F Ps B] -> (cn "(defun " (cn (buri.cc-lp F) (cn " (" (cn (buri.cc-ser-params Ps) (cn ") " (cn (buri.cc-ser B) ")"))))))
  [app H Args] -> (cn "(app " (cn (buri.cc-ser H) (cn (buri.cc-ser-args Args) ")")))
  [call F Args] -> (cn "(call " (cn (buri.cc-lp F) (cn (buri.cc-ser-args Args) ")")))
  E -> (simple-error "contract-cert: malformed expression"))
(define buri.cc-ser-clauses [] -> ""
  [[C B] | Cs] -> (cn " (" (cn (buri.cc-ser C) (cn " " (cn (buri.cc-ser B) (cn ")" (buri.cc-ser-clauses Cs))))))
  _ -> (simple-error "contract-cert: malformed cond"))
(define buri.cc-ser-params [] -> ""
  [P | Ps] -> (cn (buri.cc-lp P) (cn " " (buri.cc-ser-params Ps)))
  _ -> (simple-error "contract-cert: malformed parameters"))
(define buri.cc-ser-args [] -> ""
  [A | As] -> (cn " " (cn (buri.cc-ser A) (buri.cc-ser-args As)))
  _ -> (simple-error "contract-cert: malformed arguments"))
(define buri.cc-ser-def [F Ps B] -> (cn "(def " (cn (buri.cc-lp F) (cn " (" (cn (buri.cc-ser-params Ps) (cn ") " (cn (buri.cc-ser B) ")"))))))
  _ -> (simple-error "contract-cert: malformed definition"))
(define buri.cc-ser-defs [] -> ""
  [D | Ds] -> (cn " " (cn (buri.cc-ser-def D) (buri.cc-ser-defs Ds)))
  _ -> (simple-error "contract-cert: malformed definitions"))
(define buri.cc-ser-program [program Defs Main] -> (cn "(program" (cn (buri.cc-ser-defs Defs) (cn " (main " (cn (buri.cc-ser Main) "))"))))
  _ -> (simple-error "contract-cert: malformed program"))
(define buri.cc-fingerprint Program -> (buri.cc-hash-string (buri.cc-ser-program Program)))

\\ ---------------------------------------------------------------------------
\\ Pinned identities (rocq/ContractCert.v pinned_theory, pinned_evaluator).
(define buri.cc-rules ->
  ["r_val" "r_unbound" "r_let" "r_if" "r_type" "r_defun" "r_defun_bad" "r_trap" "r_app" "r_app0"
   "r_call" "r_call0" "r_conseq" "r_exists" "r_frame" "aj_sem" "aj_ctx" "aj_partial" "aj_lam" "aj_frozen"])
(define buri.cc-theory-text [] -> "" [R | Rs] -> (cn R (cn " " (buri.cc-theory-text Rs))))
(define buri.cc-theory -> [theory "BURI/KL-CONTRACT-1" (buri.cc-hash-string (buri.cc-theory-text (buri.cc-rules)))])
(define buri.cc-evaluator -> [evaluator "e2e07_klambda" 1927390069043521096])
(define buri.cc-format -> "buri-contract-1")
(define buri.cc-prim-names ->
  ["intern" "pos" "tlstr" "cn" "str" "string?" "n->string" "string->n" "set" "value" "simple-error"
   "error-to-string" "cons" "hd" "tl" "cons?" "=" "eval-kl" "absvector" "address->" "<-address" "absvector?"
   "write-byte" "read-byte" "open" "close" "get-time" "+" "-" "*" "/" ">" "<" ">=" "<=" "number?"])

\\ ---------------------------------------------------------------------------
\\ Skeleton fit (rocq/ContractCert.v fits). E is [some Expr] or none.
(define buri.cc-atomic?
  [num _] -> true [float _] -> true [str _] -> true [sym _] -> true [bool _] -> true [nil] -> true
  [var _] -> true [lambda _ _] -> true [freeze _] -> true _ -> false)
(define buri.cc-structural? R -> (buri.member? R [r_conseq r_exists r_frame]))
(define buri.cc-fits
  Bs [rule r_val []] [some E] -> (buri.cc-atomic? E)
  Bs [rule r_unbound []] [some [var _]] -> true
  Bs [rule r_let [D1 D2]] [some [let _ A B]] -> (and (buri.cc-fits Bs D1 [some A]) (buri.cc-fits Bs D2 [some B]))
  Bs [rule r_if [D1 D2 D3]] [some [if C A B]] ->
    (and (buri.cc-fits Bs D1 [some C]) (and (buri.cc-fits Bs D2 [some A]) (buri.cc-fits Bs D3 [some B])))
  Bs [rule r_type [D]] [some [type A]] -> (buri.cc-fits Bs D [some A])
  Bs [rule r_defun []] [some [defun _ _ _]] -> true
  Bs [rule r_defun_bad []] [some [defun _ _ _]] -> true
  Bs [rule r_trap [D1 D2 D3]] [some [trap A H]] ->
    (and (buri.cc-fits Bs D1 [some A]) (and (buri.cc-fits Bs D2 [some H]) (buri.cc-fits Bs D3 none)))
  Bs [rule r_app [D1 D2 | Ds]] [some [app H [A | As]]] ->
    (and (buri.cc-fits Bs D1 [some H]) (and (buri.cc-fits Bs D2 none) (buri.cc-fits-args Bs Ds [A | As])))
  Bs [rule r_app0 [D1 D2]] [some [app H []]] -> (and (buri.cc-fits Bs D1 [some H]) (buri.cc-fits Bs D2 none))
  Bs [rule r_call [D1 | Ds]] [some [call _ [A | As]]] -> (and (buri.cc-fits Bs D1 none) (buri.cc-fits-args Bs Ds [A | As]))
  Bs [rule r_call0 [D1]] [some [call _ []]] -> (buri.cc-fits Bs D1 none)
  Bs [rule R [D]] [some E] -> (buri.cc-fits Bs D [some E]) where (buri.cc-structural? R)
  _ [rule aj_sem [[side _]]] none -> true
  _ [rule aj_ctx [[hyp _] | Sides]] none -> (buri.cc-sides? Sides)
  _ [rule aj_ctx [[prim _] | Sides]] none -> (buri.cc-sides? Sides)
  _ [rule aj_ctx [[rec _] | Sides]] none -> (buri.cc-sides? Sides)
  _ [rule aj_partial [[side _]]] none -> true
  Bs [rule aj_lam [D]] none -> (buri.cc-fits-some Bs D Bs)
  Bs [rule aj_frozen [D]] none -> (buri.cc-fits-some Bs D Bs)
  _ _ _ -> false)
(define buri.cc-sides? [] -> true [[side _] | Xs] -> (buri.cc-sides? Xs) _ -> false)
(define buri.cc-fits-args _ [] [] -> true
  Bs [D | Ds] [A | As] -> (and (buri.cc-fits Bs D [some A]) (buri.cc-fits-args Bs Ds As))
  _ _ _ -> false)
(define buri.cc-fits-some _ _ [] -> false
  Bs D [B | More] -> (or (buri.cc-fits Bs D [some B]) (buri.cc-fits-some Bs D More)))

\\ Closure bodies of the program (rocq/ContractCert.v bodies_of, closure_bodies).
(define buri.cc-bodies
  [lambda _ B] -> [B | (buri.cc-bodies B)]
  [freeze B] -> [B | (buri.cc-bodies B)]
  [let _ A B] -> (buri.append (buri.cc-bodies A) (buri.cc-bodies B))
  [and A B] -> (buri.append (buri.cc-bodies A) (buri.cc-bodies B))
  [or A B] -> (buri.append (buri.cc-bodies A) (buri.cc-bodies B))
  [trap A B] -> (buri.append (buri.cc-bodies A) (buri.cc-bodies B))
  [if C A B] -> (buri.append (buri.cc-bodies C) (buri.append (buri.cc-bodies A) (buri.cc-bodies B)))
  [type A] -> (buri.cc-bodies A)
  [defun _ _ A] -> (buri.cc-bodies A)
  [cond Cs] -> (buri.cc-bodies-clauses Cs)
  [app H Args] -> (buri.append (buri.cc-bodies H) (buri.cc-bodies-list Args))
  [call _ Args] -> (buri.cc-bodies-list Args)
  _ -> [])
(define buri.cc-bodies-clauses [] -> []
  [[C B] | Cs] -> (buri.append (buri.cc-bodies C) (buri.append (buri.cc-bodies B) (buri.cc-bodies-clauses Cs)))
  _ -> [])
(define buri.cc-bodies-list [] -> [] [A | As] -> (buri.append (buri.cc-bodies A) (buri.cc-bodies-list As)) _ -> [])
(define buri.cc-bodies-defs [] -> [] [[_ _ B] | Ds] -> (buri.append (buri.cc-bodies B) (buri.cc-bodies-defs Ds)))
(define buri.cc-closure-bodies [program Defs Main] -> (buri.append (buri.cc-bodies-defs Defs) (buri.cc-bodies Main)))

\\ Leaves of skeletons (rocq/ContractCert.v leaves).
(define buri.cc-leaves [rule _ Subs] -> (buri.cc-leaves-list Subs)
  X -> [X])
(define buri.cc-leaves-list [] -> [] [D | Ds] -> (buri.append (buri.cc-leaves D) (buri.cc-leaves-list Ds)))
(define buri.cc-select _ [] -> []
  Tag [[Tag S] | Xs] -> [S | (buri.cc-select Tag Xs)]
  Tag [_ | Xs] -> (buri.cc-select Tag Xs))
(define buri.cc-dups? [] -> false [X | Xs] -> (or (buri.member? X Xs) (buri.cc-dups? Xs)))
(define buri.cc-all-in? [] _ -> true [X | Xs] Ys -> (and (buri.member? X Ys) (buri.cc-all-in? Xs Ys)))
(define buri.cc-skel-of _ [] -> missing F [[F Sk] | _] -> [found Sk] F [_ | More] -> (buri.cc-skel-of F More))
(define buri.cc-body-fits? _ _ [] -> true
  Bs Bodies [[F _ B] | Ds] -> (and (buri.cc-body-fits-h Bs (buri.cc-skel-of F Bodies) B)
                                   (buri.cc-body-fits? Bs Bodies Ds)))
(define buri.cc-body-fits-h Bs [found Sk] B -> (buri.cc-fits Bs Sk [some B])
  _ _ _ -> false)

\\ A raw input that carries a verdict label is a forgery attempt.
(define buri.cc-forged? accepted -> true
  [X | Xs] -> (or (buri.cc-forged? X) (buri.cc-forged? Xs))
  _ -> false)

\\ ---------------------------------------------------------------------------
\\ The checker. Order of checks as in rocq/ContractCert.v check.
(define buri.contract-check Program Cert ->
  (if (or (buri.cc-forged? Program) (buri.cc-forged? Cert))
      [rejected forged-label]
      (trap-error (buri.cc-check Program Cert) (/. E [rejected malformed-certificate]))))
(define buri.cc-check
  [program Defs Main]
  [contract-certificate Format Theory [program PName PHash] Evaluator [statement SName Mode]
                        [hypotheses Hyps] [measures Measures] [bodies Bodies] [main MainSk]] ->
  (let L (buri.cc-leaves-list [MainSk | (map (/. B (hd (tl B))) Bodies)])
       Bs (buri.cc-closure-bodies [program Defs Main])
       Recs (buri.cc-select rec L)
       Names (map (/. D (hd D)) Defs)
    (cond ((not (= Format (buri.cc-format))) [rejected unknown-format])
          ((not (= Theory (buri.cc-theory))) [rejected stale-theory])
          ((not (= PHash (buri.cc-fingerprint [program Defs Main]))) [rejected stale-program])
          ((not (= Evaluator (buri.cc-evaluator))) [rejected stale-evaluator])
          ((not (buri.member? Mode [partial total always])) [rejected unknown-mode])
          ((buri.cc-dups? Hyps) [rejected duplicate-hypothesis])
          ((not (buri.cc-all-in? (buri.cc-select hyp L) Hyps)) [rejected undeclared-hypothesis])
          ((not (buri.cc-all-in? (buri.cc-select prim L) (buri.cc-prim-names))) [rejected unknown-primitive])
          ((not (buri.cc-all-in? Recs Names)) [rejected unknown-recursive-function])
          ((and (= Mode total) (not (buri.cc-all-in? Recs (map (/. M (hd M)) Measures)))) [rejected missing-measure])
          ((not (buri.cc-body-fits? Bs Bodies Defs)) [rejected body-shape])
          ((not (buri.cc-fits Bs MainSk [some Main])) [rejected main-shape])
          (true [accepted [SName Mode] Hyps (buri.cc-select prim L) (buri.cc-select side L)])))
  _ _ -> [rejected malformed-certificate])
