\\ E2E-17 primitive inventory: an inert capture of the pinned port sources.
\\ It lexes the vendored source bytes itself (never Shen's reader, a host
\\ reader, macroexpansion or eval), extracts top-level definitions with byte
\\ spans, computes each definition's free references conservatively, and
\\ follows them to a dependency closure that ends in individually named host
\\ operations. The implementation roots and evidence labels are a reviewed
\\ table below; the closure is computed. The output (spec/primitives.json) is
\\ data: shen/primitive-matrix.shen checks it, and Rocq checks the theorems it
\\ cites. Nothing here decides theorem validity.

\\ ---------- Lexer: bytes -> tokens with byte offsets ----------
\\ Dialects: scheme (Chez), cl (Common Lisp, |bar| symbols, #| |# comments),
\\ shen (\\ and \* *\ comments). Strings keep backslash escapes inert.
(define buri.pi-space? B -> (element? B [9 10 12 13 32]))
(define buri.pi-delim? cl B -> (or (buri.pi-space? B) (element? B [34 39 40 41 44 59 91 93 96 124]))
  shen B -> (or (buri.pi-space? B) (element? B [34 40 41 91 93]))
  _ B -> (or (buri.pi-space? B) (element? B [34 39 40 41 44 59 91 93 96])))
(define buri.pi-lex D Bytes -> (reverse (buri.pi-lex-h D Bytes 0 [])))
(define buri.pi-lex-h
  _ [] _ Acc -> Acc
  shen [92 92 | R] P Acc -> (buri.pi-line shen R (+ P 2) Acc)
  shen [92 42 | R] P Acc -> (buri.pi-block shen R (+ P 2) Acc [42 92])
  cl [35 124 | R] P Acc -> (buri.pi-block cl R (+ P 2) Acc [124 35])
  D [59 | R] P Acc -> (buri.pi-line D R (+ P 1) Acc) where (not (= D shen))
  D [B | R] P Acc -> (buri.pi-lex-h D R (+ P 1) Acc) where (buri.pi-space? B)
  D [B | R] P Acc -> (buri.pi-lex-h D R (+ P 1) [[o P] | Acc]) where (element? B [40 91])
  D [B | R] P Acc -> (buri.pi-lex-h D R (+ P 1) [[c (+ P 1)] | Acc]) where (element? B [41 93])
  D [39 | R] P Acc -> (buri.pi-lex-h D R (+ P 1) [[q] | Acc]) where (not (= D shen))
  D [96 | R] P Acc -> (buri.pi-lex-h D R (+ P 1) [[qq] | Acc]) where (not (= D shen))
  D [44 64 | R] P Acc -> (buri.pi-lex-h D R (+ P 2) [[uq] | Acc]) where (not (= D shen))
  D [44 | R] P Acc -> (buri.pi-lex-h D R (+ P 1) [[uq] | Acc]) where (not (= D shen))
  cl [35 39 | R] P Acc -> (buri.pi-lex-h cl R (+ P 2) [[fq] | Acc])
  cl [124 | R] P Acc -> (buri.pi-bar R (+ P 1) [] Acc)
  D [35 92 C | R] P Acc -> (buri.pi-atom D R (+ P 3) [C 92 35] Acc) where (not (= D shen))
  D [34 | R] P Acc -> (buri.pi-string D R (+ P 1) [] Acc)
  D Bytes P Acc -> (buri.pi-atom D Bytes P [] Acc))
(define buri.pi-line
  D [] P Acc -> Acc
  D [10 | R] P Acc -> (buri.pi-lex-h D R (+ P 1) Acc)
  D [_ | R] P Acc -> (buri.pi-line D R (+ P 1) Acc))
(define buri.pi-block
  _ [] _ _ _ -> (simple-error "primitive inventory: unterminated block comment")
  D [X Y | R] P Acc [X Y] -> (buri.pi-lex-h D R (+ P 2) Acc)
  D [_ | R] P Acc End -> (buri.pi-block D R (+ P 1) Acc End))
(define buri.pi-text Rev -> (buri.pi-text-h (reverse Rev) ""))
(define buri.pi-text-h [] S -> S
  [B | Bs] S -> (buri.pi-text-h Bs (cn S (n->string B))) where (and (>= B 32) (< B 127))
  _ _ -> (simple-error "primitive inventory: non-ASCII token"))
(define buri.pi-string
  _ [] _ _ _ -> (simple-error "primitive inventory: unterminated string")
  D [92 B | R] P Cs Acc -> (buri.pi-string D R (+ P 2) [B 92 | Cs] Acc) where (not (= D shen))
  D [34 | R] P Cs Acc -> (buri.pi-lex-h D R (+ P 1) [[s (buri.pi-text Cs)] | Acc])
  D [10 | R] P Cs Acc -> (buri.pi-string D R (+ P 1) [32 | Cs] Acc)
  D [B | R] P Cs Acc -> (buri.pi-string D R (+ P 1) [B | Cs] Acc))
(define buri.pi-bar
  [] _ _ _ -> (simple-error "primitive inventory: unterminated |symbol|")
  [124 | R] P Cs Acc -> (buri.pi-lex-h cl R (+ P 1) [[b (buri.pi-text Cs)] | Acc])
  [B | R] P Cs Acc -> (buri.pi-bar R (+ P 1) [B | Cs] Acc))
(define buri.pi-atom
  D [B | R] P Cs Acc -> (buri.pi-atom D R (+ P 1) [B | Cs] Acc) where (not (buri.pi-delim? D B))
  D Bytes P Cs Acc -> (buri.pi-lex-h D Bytes P [[a (buri.pi-name D (buri.pi-text Cs))] | Acc]))
\\ CL symbols are upcased (the standard readtable); |bar| names keep case.
(define buri.pi-name cl S -> (buri.pi-upcase S)  _ S -> S)
(define buri.pi-upcase "" -> ""
  (@s C R) -> (cn (buri.pi-up C) (buri.pi-upcase R)))
(define buri.pi-up C -> (let N (string->n C) (if (and (>= N 97) (<= N 122)) (n->string (- N 32)) C)))

\\ ---------- Parser: tokens -> trees ----------
\\ [l Items Start End] | [y Name] | [t Text] | [quote X] | [qq X] | [uq X] | [fq X]
(define buri.pi-parse-all Ts -> (buri.pi-parse-all-h Ts []))
(define buri.pi-parse-all-h [] Acc -> (reverse Acc)
  Ts Acc -> (let R (buri.pi-parse Ts) (buri.pi-parse-all-h (tl R) [(hd R) | Acc])))
(define buri.pi-parse
  [[o P] | R] -> (buri.pi-items R P [])
  [[q] | R] -> (buri.pi-prefix quote R)
  [[qq] | R] -> (buri.pi-prefix qq R)
  [[uq] | R] -> (buri.pi-prefix uq R)
  [[fq] | R] -> (buri.pi-prefix fq R)
  [[a S] | R] -> [[y S] | R]
  [[b S] | R] -> [[y S] | R]
  [[s S] | R] -> [[t S] | R]
  _ -> (simple-error "primitive inventory: unbalanced source"))
(define buri.pi-prefix Tag R -> (let X (buri.pi-parse R) [[Tag (hd X)] | (tl X)]))
(define buri.pi-items
  [] _ _ -> (simple-error "primitive inventory: unterminated list")
  [[c E] | R] P Acc -> [[l (reverse Acc) P E] | R]
  Ts P Acc -> (let X (buri.pi-parse Ts) (buri.pi-items (tl X) P [(hd X) | Acc])))
(define buri.pi-read D Path -> (buri.pi-features D (buri.pi-parse-all (buri.pi-lex D (read-file-as-bytelist Path)))))

\\ CL read-time conditionals, honoured as the pinned SBCL reader would:
\\ #+F X keeps X and #-F X drops it when F holds. Both supported targets'
\\ architecture features hold, so per-architecture code is kept on either side.
(define buri.pi-sbcl-features -> ["SBCL" "LINUX" "UNIX" "64-BIT" "X86-64" "ARM64" "LITTLE-ENDIAN" "SB-THREAD" "SB-UNICODE"])
(define buri.pi-feature? [y F] -> (element? F (buri.pi-sbcl-features))
  [l [[y "OR"] | Fs] _ _] -> (buri.pi-some-feature? Fs)
  [l [[y "AND"] | Fs] _ _] -> (buri.pi-all-features? Fs)
  [l [[y "NOT"] F] _ _] -> (not (buri.pi-feature? F))
  _ -> false)
(define buri.pi-some-feature? [] -> false  [F | Fs] -> (or (buri.pi-feature? F) (buri.pi-some-feature? Fs)))
(define buri.pi-all-features? [] -> true  [F | Fs] -> (and (buri.pi-feature? F) (buri.pi-all-features? Fs)))
(define buri.pi-features cl Xs -> (buri.pi-feat-list Xs)  _ Xs -> Xs)
(define buri.pi-feat-list [] -> []
  [[y "#+"] F X | R] -> (buri.pi-feat-keep (buri.pi-feature? F) X R)
  [[y "#-"] F X | R] -> (buri.pi-feat-keep (not (buri.pi-feature? F)) X R)
  [[y S] X | R] -> (buri.pi-feat-keep (buri.pi-feature? [y (buri.pi-feat-name S)]) X R) where (buri.pt0-prefix? "#+" S)
  [[y S] X | R] -> (buri.pi-feat-keep (not (buri.pi-feature? [y (buri.pi-feat-name S)])) X R) where (buri.pt0-prefix? "#-" S)
  [X | R] -> [(buri.pi-feat-node X) | (buri.pi-feat-list R)])
(define buri.pi-feat-keep true X R -> [(buri.pi-feat-node X) | (buri.pi-feat-list R)]
  false _ R -> (buri.pi-feat-list R))
(define buri.pi-feat-node [l Xs S E] -> [l (buri.pi-feat-list Xs) S E]
  [Tag X] -> [Tag (buri.pi-feat-node X)] where (element? Tag [quote qq uq fq])
  X -> X)
(define buri.pi-feat-name S -> (tlstr (tlstr S)))
(define buri.pt0-prefix? Pre S -> (buri.pt0-prefix-h (explode Pre) (explode S)))
(define buri.pt0-prefix-h [] _ -> true  [C | R] [C | S] -> (buri.pt0-prefix-h R S)  _ _ -> false)

\\ ---------- Definitions and free references ----------
\\ A definition is [Name Kind Start End Params Body]; Kind is fn, macro or var.
(define buri.pi-defs D Forms -> (buri.pi-concat (map (/. F (buri.pi-def D F)) Forms)))
(define buri.pi-concat [] -> [] [X | Xs] -> (append X (buri.pi-concat Xs)))
(define buri.pi-def
  scheme [l [[y "define"] [l [[y N] | Ps] _ _] | Body] S E] -> [[N fn S E (buri.pi-syms Ps) Body]]
  scheme [l [[y "define"] [y N] | Body] S E] -> [[N var S E [] Body]]
  scheme [l [[y "define-syntax"] [y N] | Body] S E] -> [[N macro S E [] Body]]
  cl [l [[y "DEFUN"] [y N] [l Ps _ _] | Body] S E] -> [[N fn S E (buri.pi-syms Ps) Body]]
  cl [l [[y "DEFMACRO"] [y N] [l Ps _ _] | Body] S E] -> [[N macro S E (buri.pi-syms Ps) Body]]
  cl [l [[y K] [y N] | Body] S E] -> [[N var S E [] Body]] where (element? K ["DEFVAR" "DEFCONSTANT" "DEFPARAMETER"])
  cl [l [[y "PROGN"] | Fs] _ _] -> (buri.pi-defs cl Fs)
  shen [l [[y "define"] [y N] | Body] S E] -> [[N fn S E [] Body]]
  shen [l [[y "package"] _ _ | Fs] _ _] -> (buri.pi-defs shen Fs)
  _ _ -> [])
(define buri.pi-syms [] -> [] [[y S] | R] -> [S | (buri.pi-syms R)]
  [[l Xs _ _] | R] -> (append (buri.pi-syms Xs) (buri.pi-syms R))  [_ | R] -> (buri.pi-syms R))
(define buri.pi-def-name [N | _] -> N)
(define buri.pi-def-kind [_ K | _] -> K)

\\ Binders anywhere in a body (a conservative superset: a binder name is never
\\ reported as a host reference). Literal and quoted data are not references.
(define buri.pi-binder-heads -> ["let" "let*" "letrec" "letrec*" "do" "LET" "LET*" "DO" "DO*"])
(define buri.pi-binders
  [l [[y H] [y Name] [l Bs _ _] | R] _ _] -> (append [Name | (buri.pi-bound Bs)] (buri.pi-binders-list R))
      where (= H "let")
  [l [[y H] [l Bs _ _] | R] _ _] -> (append (buri.pi-bound Bs) (buri.pi-binders-list R))
      where (element? H (buri.pi-binder-heads))
  [l [[y H] [l Ps _ _] | R] _ _] -> (append (buri.pi-syms Ps) (buri.pi-binders-list R))
      where (element? H ["lambda" "LAMBDA" "MULTIPLE-VALUE-BIND" "DESTRUCTURING-BIND" "|lambda|"])
  [l [[y H] [l [[y V] | _] _ _] | R] _ _] -> [V | (buri.pi-binders-list R)]
      where (element? H ["DOLIST" "DOTIMES" "WITH-OPEN-FILE" "WITH-OUTPUT-TO-STRING" "WITH-INPUT-FROM-STRING"])
  [l [[y "guard"] [l [[y V] | Cl] _ _] | R] _ _] -> [V | (append (buri.pi-binders-list Cl) (buri.pi-binders-list R))]
  [l [[y "LOOP"] | R] _ _] -> (buri.pi-loop-binders R)
  [l [[y "syntax-rules"] _ | Rules] _ _] -> (buri.pi-concat (map (/. R (buri.pi-rule-binders R)) Rules))
  [l [[y "case-lambda"] | Cls] _ _] -> (buri.pi-concat (map (/. R (buri.pi-rule-binders R)) Cls))
  [l [[y "HANDLER-CASE"] X | Cls] _ _] -> (append (buri.pi-binders X) (buri.pi-handler-binders Cls))
  [l Xs _ _] -> (buri.pi-binders-list Xs)
  [uq X] -> (buri.pi-binders X)
  [qq X] -> (buri.pi-binders X)
  _ -> [])
(define buri.pi-binders-list Xs -> (buri.pi-concat (map (/. X (buri.pi-binders X)) Xs)))
(define buri.pi-rule-binders [l [[l Ps _ _] | Body] _ _] -> (append (buri.pi-syms Ps) (buri.pi-binders-list Body))
  _ -> [])
(define buri.pi-bound [] -> []
  [[l [[y V] | Init] _ _] | R] -> [V | (append (buri.pi-binders-list Init) (buri.pi-bound R))]
  [[l [[l Vs _ _] | Init] _ _] | R] -> (append (buri.pi-syms Vs) (append (buri.pi-binders-list Init) (buri.pi-bound R)))
  [[y V] | R] -> [V | (buri.pi-bound R)]
  [_ | R] -> (buri.pi-bound R))
(define buri.pi-loop-binders [] -> []
  [[y K] [y V] | R] -> [V | (buri.pi-loop-binders R)] where (element? K ["FOR" "WITH" "AS"])
  [X | R] -> (append (buri.pi-binders X) (buri.pi-loop-binders R)))
(define buri.pi-handler-binders [] -> []
  [[l [_ [l Vs _ _] | B] _ _] | R] -> (append (buri.pi-syms Vs) (append (buri.pi-binders-list B) (buri.pi-handler-binders R)))
  [_ | R] -> (buri.pi-handler-binders R))

\\ Symbols that are self-evaluating or reader notation, never references.
(define buri.pi-literal? S -> true where (element? S ["#t" "#f" "T" "NIL" "true" "false" "else" "&OPTIONAL" "&REST" "&KEY" "&BODY" "..." "_"])
  S -> true where (buri.pi-numeral? S)
  S -> true where (= (pos S 0) ":")
  S -> true where (and (> (length (explode S)) 1) (= (pos S 0) "#") (element? (pos S 1) [(n->string 92) "+" "-"]))
  _ -> false)
(define buri.pi-numeral? S -> (buri.pi-numeral-h (explode S) false))
(define buri.pi-numeral-h [] Seen -> Seen
  [C | R] Seen -> (buri.pi-numeral-h R true) where (element? C ["0" "1" "2" "3" "4" "5" "6" "7" "8" "9"])
  [C | R] Seen -> (buri.pi-numeral-h R Seen) where (element? C ["." "-" "+" "e" "d"])
  _ _ -> false)
\\ Declarations and type arguments are not evaluated references.
\\ LOOP clause keywords and CASE datum lists are syntax, not references.
(define buri.pi-loop-words -> ["FOR" "FROM" "BELOW" "TO" "DO" "IN" "ON" "ACROSS" "UNTIL" "WHILE" "COLLECT" "ALWAYS"
  "NEVER" "THEREIS" "OF-TYPE" "WITH" "AS" "AND" "=" "BY" "SUM" "FINALLY" "RETURN" "WHEN" "IF" "UNLESS" "UPTO"
  "DOWNTO" "INTO" "BEING" "EACH"])
(define buri.pi-refs
  [l [[y "LOOP"] | Xs] _ _] -> [[y "LOOP"] | (buri.pi-loop-refs Xs)]
  [l [[y "case"] K | Cls] _ _] -> [[y "case"] | (append (buri.pi-refs K) (buri.pi-case-refs Cls))]
  [l [[y H] | _] _ _] -> [[y H]] where (element? H ["file-options" "eol-style" "error-handling-mode" "buffer-mode"])
  [l [[y "FUNCTION"] [y F]] _ _] -> [[y "FUNCTION"] [y F]]
  [l [[y "FUNCTION"] [l Xs S E]] _ _] -> [[y "FUNCTION"] | (buri.pi-refs [l Xs S E])]
  [l [[y "FUNCTION"] | _] _ _] -> [[y "FUNCTION"]]
  [l [[y "DECLARE"] | _] _ _] -> []
  [l [[y "DECLAIM"] | _] _ _] -> []
  [l [[y "THE"] _ X] _ _] -> [[y "THE"] | (buri.pi-refs X)]
  [l Xs _ _] -> (buri.pi-concat (map (/. X (buri.pi-refs X)) Xs))
  [quote _] -> []
  [fq X] -> (buri.pi-refs X)
  [qq X] -> (buri.pi-refs X)
  [uq X] -> (buri.pi-refs X)
  [y S] -> (if (buri.pi-literal? S) [] [[y S]])
  _ -> [])
(define buri.pi-loop-refs [] -> []
  [[y "OF-TYPE"] _ | R] -> (buri.pi-loop-refs R)
  [[y K] | R] -> (buri.pi-loop-refs R) where (element? K (buri.pi-loop-words))
  [X | R] -> (append (buri.pi-refs X) (buri.pi-loop-refs R)))
(define buri.pi-case-refs [] -> []
  [[l [_ | Body] _ _] | R] -> (append (buri.pi-concat (map (/. X (buri.pi-refs X)) Body)) (buri.pi-case-refs R))
  [_ | R] -> (buri.pi-case-refs R))
(define buri.pi-free [N _ _ _ Ps Body] D ->
  (let Bound (append Ps (buri.pi-binders-list Body))
       Raw (map (/. R (buri.pi-ref-name R)) (buri.pi-concat (map (/. X (buri.pi-refs X)) Body)))
    (buri.pi-dedup (buri.pi-remove-all (buri.pi-filter-shen D (buri.pi-foreign-refs D Body Raw)) [N | Bound]))))
(define buri.pi-ref-name [y S] -> S)
\\ In Shen port sources only (foreign scm.X) escapes reach the host; every
\\ other lowercase name is a Shen function (uppercase names are variables).
(define buri.pi-foreign-refs shen Body _ -> (buri.pi-foreigns-list Body)
  _ _ Raw -> Raw)
(define buri.pi-foreigns-list Xs -> (buri.pi-concat (map (/. X (buri.pi-foreigns X)) Xs)))
(define buri.pi-foreigns
  [l [[y "foreign"] [y S]] _ _] -> [S]
  [l Xs _ _] -> (buri.pi-foreigns-list Xs)
  _ -> [])
(define buri.pi-filter-shen _ Xs -> Xs)
(define buri.pi-remove-all [] _ -> []
  [X | Xs] Ys -> (buri.pi-remove-all Xs Ys) where (element? X Ys)
  [X | Xs] Ys -> [X | (buri.pi-remove-all Xs Ys)])
(define buri.pi-dedup Xs -> (reverse (buri.pi-dedup-h Xs [])))
(define buri.pi-dedup-h [] Acc -> Acc
  [X | Xs] Acc -> (buri.pi-dedup-h Xs Acc) where (element? X Acc)
  [X | Xs] Acc -> (buri.pi-dedup-h Xs [X | Acc]))
(define buri.pi-sort Xs -> (buri.pi-sort-h Xs []))
(define buri.pi-sort-h [] Acc -> Acc  [X | Xs] Acc -> (buri.pi-sort-h Xs (buri.pi-insert X Acc)))
(define buri.pi-insert X [] -> [X]
  X [Y | Ys] -> [X Y | Ys] where (buri.pi-less? X Y)
  X [Y | Ys] -> [Y | (buri.pi-insert X Ys)])
(define buri.pi-less? A B -> (buri.pi-less-h (explode A) (explode B)))
(define buri.pi-less-h [] [] -> false  [] _ -> true  _ [] -> false
  [C | R] [C | S] -> (buri.pi-less-h R S)
  [C | _] [D | _] -> (< (string->n C) (string->n D)))
