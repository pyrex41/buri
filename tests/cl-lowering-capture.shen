(load "shen/cl-lowering-capture.shen")
\\ Regression tests for the inert Shen-CL lowering capture adapter. They
\\ exercise lexing, parsing, selection, mutation and Rocq rendering on small
\\ inline sources; the pinned compiler.shen capture is checked by Rocq.
(define buri.cll-test Expect Actual ->
 (if (= Expect Actual) passed (simple-error "CL lowering capture regression")))
(define buri.cll-bytes S -> (map (/. C (string->n C)) (explode S)))
(define buri.cll-forms S -> (map (/. F (buri.cll-strip F)) (buri.cll-parse-all (buri.cll-lex (buri.cll-bytes S)))))
(define buri.cll-fails? F -> (trap-error (do (thaw F) false) (/. E true)))
(define buri.cll-bs -> (n->string 92))

(buri.cll-test [[paren [[sym "define"] [sym "f"] [brack [[sym "A"] [bar] [sym "B"]]] [sym "->"] [sym "c"]]]]
 (buri.cll-forms (cn "(define f [A | B] -> c) " (cn (buri.cll-bs) (cn (buri.cll-bs) (cn " trailing comment" (n->string 10)))))))
(buri.cll-test [[sym "x"] [paren [[str "a b"]]]]
 (buri.cll-forms (cn "x " (cn (buri.cll-bs) (cn "* block (not a form) *" (cn (buri.cll-bs) " (c#34;a bc#34;)"))))))
(buri.cll-test [[num "12"] [num "-3.5"] [sym "a1"] [sym "-"] [sym "->"] [brack []]]
 (buri.cll-forms "12 -3.5 a1 - -> []"))
(buri.cll-test [paren [[sym "define"] [sym "g"] [sym "X"] [sym "->"] [sym "X"]] 0 17]
 (buri.cll-select (buri.cll-parse-all (buri.cll-lex (buri.cll-bytes "(define g X -> X)"))) "g"))
(buri.cll-test true (buri.cll-fails? (freeze (buri.cll-forms "(define f"))))
(buri.cll-test true (buri.cll-fails? (freeze (buri.cll-forms "(a]"))))
(buri.cll-test true (buri.cll-fails? (freeze (buri.cll-lex [97 200 98]))))
(buri.cll-test true (buri.cll-fails? (freeze
 (buri.cll-select (buri.cll-parse-all (buri.cll-lex (buri.cll-bytes "(define g X -> X) (define g Y -> Y)"))) "g"))))
(buri.cll-test [paren [[sym "define"] [sym "h"] [sym "->"] [num "1"]] 18 33]
 (buri.cll-select (buri.cll-parse-all (buri.cll-lex (buri.cll-bytes "(define g X -> X) (define h -> 1)"))) "h"))
(buri.cll-test [brack [[sym "Exp"]]]
 (buri.cll-mutate dropped-guard "optimise-boolean-check" [brack [[brack [[sym "true?"] [sym "Exp"]]]]]))
(buri.cll-test [paren [[sym "f"] (buri.cll-ce "Test")]]
 (buri.cll-mutate cl-truthiness "emit-if" [paren [[sym "f"] [paren [[sym "optimise-boolean-check"] (buri.cll-ce "Test")]]]]))
(buri.cll-test [brack [(buri.cll-ce "Else") (buri.cll-ce "Then")]]
 (buri.cll-mutate swapped-branches "emit-if" [brack [(buri.cll-ce "Then") (buri.cll-ce "Else")]]))
(buri.cll-test [brack [[sym "x"]]] (buri.cll-mutate dropped-guard "emit-if" [brack [[sym "x"]]]))
(buri.cll-test "(SParen (SCons (SSym c#34;fc#34;) (SCons SBar (SCons (SStr c#34;qc#34;) SNil))))"
 (buri.cll-coq [paren [[sym "f"] [bar] [str "q"]]]))
(buri.cll-test "c#34;ac#34;c#34;bc#34;" (buri.cll-coq-string "ac#34;b"))
(output "BURI_TESTS_OK 15~%")
