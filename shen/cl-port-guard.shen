\\ Inert source-capture admission; no EVAL or host-language loading.
\\ Native reader/provenance is a separate trusted conformance operation.
(define buri.cl-list [] -> nil [X | Xs] -> [pair X (buri.cl-list Xs)])
(define buri.cl-call F Xs -> [pair F (buri.cl-list Xs)])
(define buri.cl-symbol S -> [symbol (cn "COMMON-LISP:" S)])
(define buri.cl-shen-symbol S -> [symbol (cn "SHEN:" S)])
(define buri.cl-quote X -> (buri.cl-call (buri.cl-symbol "QUOTE") [X]))
(define buri.cl-expected-guard ->
 (buri.cl-call (buri.cl-symbol "DEFUN")
  [(buri.cl-shen-symbol "shen-cl.true?")
   (buri.cl-list [(buri.cl-shen-symbol "X")])
   (buri.cl-call (buri.cl-symbol "COND")
    [(buri.cl-list
       [(buri.cl-call (buri.cl-symbol "EQ")
          [(buri.cl-quote (buri.cl-shen-symbol "true")) (buri.cl-shen-symbol "X")])
        (buri.cl-quote (buri.cl-symbol "T"))])
     (buri.cl-list
       [(buri.cl-call (buri.cl-symbol "EQ")
          [(buri.cl-quote (buri.cl-shen-symbol "false")) (buri.cl-shen-symbol "X")]) nil])
     (buri.cl-list [(buri.cl-symbol "T")
       (buri.cl-call (buri.cl-shen-symbol "simple-error")
        [(buri.cl-call (buri.cl-symbol "FORMAT")
          [nil [text "boolean expected: not ~A~%"] (buri.cl-shen-symbol "X")])])])])]))
(define buri.cl-admit-guard Root ->
 (if (= Root (buri.cl-expected-guard))
   [accepted cl-strict-boolean-guard-1]
   [rejected cl-guard-source-mismatch]))
(define buri.cl-guard-model [bool true] -> [returned host-true]
 [bool false] -> [returned host-nil]
 _ -> [raised boolean-error])
\\ Byte-exact capture admission avoids Shen's macroexpanding source reader.
\\ The fixed expected AST contains no quote/backslash characters in strings.
(define buri.cl-capture-text nil -> "nil"
 [symbol S] -> (cn "(symbol " (cn (n->string 34) (cn S (cn (n->string 34) ")"))))
 [text S] -> (cn "(text " (cn (n->string 34) (cn S (cn (n->string 34) ")"))))
 [pair A B] -> (cn "(pair " (cn (buri.cl-capture-text A)
  (cn " " (cn (buri.cl-capture-text B) ")"))))
 _ -> (simple-error "Unsupported capture datum"))
(define buri.cl-admit-capture S ->
 (if (= S (cn (buri.cl-capture-text (buri.cl-expected-guard)) (n->string 10)))
  [accepted cl-strict-boolean-guard-1]
  [rejected cl-guard-source-mismatch]))
