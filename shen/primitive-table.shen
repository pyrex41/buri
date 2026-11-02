\\ E2E-17 primitive coverage matrix: reviewed roots, computed closures, JSON.
\\ Load after shen/primitive-inventory.shen. The table names, for every
\\ KLambda primitive (rocq/KLSyntax.v) and every registered port primitive,
\\ the exact implementation in the pinned sources: a definition, or the
\\ compiler clause that inlines host operations. Closures are computed from
\\ the source bytes. Evidence labels are reviewed claims that
\\ shen/primitive-matrix.shen checks against rocq/Audit.v.

(define buri.pt-ports -> ["shen-scheme" "shen-cl"])
(define buri.pt-sources "shen-scheme" ->
  [["ports/upstream/primitives.scm" "92b8875a276848b473c59879f075f429ba44a7a0" scheme]
   ["ports/upstream/chez-prelude.scm" "18d1ce9a8dc7073ec2be69fd9c53b9fb70d77ef3" scheme]
   ["ports/upstream/overrides.shen" "3f20b5f1b952c9c6aae3d32403da1f34095db433" shen]]
  "shen-cl" ->
  [["ports/upstream/shen-cl/primitives.lsp" "f9b11c8a0b57c8492e66094d5e236a8711983e7a" cl]
   ["ports/upstream/shen-cl/overwrite.lsp" "8108c9d4a70c61fb2e9d5ab6a59df08a9c9c5096" cl]])
(define buri.pt-compiler "shen-scheme" -> ["ports/upstream/compiler.shen" "42ac753b8f305c578998b74693fc85b28112a814"]
  "shen-cl" -> ["ports/upstream/shen-cl/compiler.shen" "2d624377c02030f9513769f7bad11e84330b8c5a"])
(define buri.pt-revision "shen-scheme" -> "tizoc/shen-scheme@8d261518db17fbfec32d1b268b40ed216b925c74"
  "shen-cl" -> "Shen-Language/shen-cl@4844072dde0208c3e4b99dcbfea58e4fdfd812e8")

\\ Definition database of a port: [[Path Blob Dialect Def] ...], read once.
(define buri.pt-db Port -> (buri.pt-db-h (buri.pt-sources Port)))
(define buri.pt-db-h [] -> []
  [[Path Blob D] | R] -> (append (map (/. Def [Path Blob D Def]) (buri.pi-defs D (buri.pi-read D Path))) (buri.pt-db-h R)))
(define buri.pt-lookup _ [] -> []
  N [[P B D Def] | R] -> [[P B D Def] | (buri.pt-lookup N R)] where (= N (buri.pi-def-name Def))
  N [_ | R] -> (buri.pt-lookup N R))
\\ Compiled code calls a Shen-level definition F of overrides.shen as kl:F.
(define buri.pt-resolve "shen-scheme" N Db -> (let Direct (buri.pt-host-only (buri.pt-lookup N Db))
  (if (and (= Direct []) (buri.pt-prefix? "kl:" N)) (buri.pt-shen-only (buri.pt-lookup (buri.pt-drop 3 N) Db)) Direct))
  _ N Db -> (buri.pt-lookup N Db))
(define buri.pt-host-only [] -> []
  [[P B shen Def] | R] -> (buri.pt-host-only R)
  [X | R] -> [X | (buri.pt-host-only R)])
(define buri.pt-shen-only [] -> []
  [[P B shen Def] | R] -> [[P B shen Def] | (buri.pt-shen-only R)]
  [_ | R] -> (buri.pt-shen-only R))
(define buri.pt-prefix? Pre S -> (buri.pt-prefix-h (explode Pre) (explode S)))
(define buri.pt-prefix-h [] _ -> true  [C | R] [C | S] -> (buri.pt-prefix-h R S)  _ _ -> false)
(define buri.pt-drop 0 S -> S  N S -> (buri.pt-drop (- N 1) (tlstr S)))
(define buri.pt-lower? S -> (buri.pt-lower-h (explode S)))
(define buri.pt-lower-h [] -> false
  [C | R] -> true where (let N (string->n C) (and (>= N 97) (<= N 122)))
  [_ | R] -> (buri.pt-lower-h R))

\\ An unresolved reference: Shen-level code compiled by the port, or a host op.
(define buri.pt-external "shen-scheme" shen N -> [host (cn "chez:" (buri.pt-strip-scm N))]
  "shen-scheme" _ N -> [shen N] where (buri.pt-prefix? "kl:" N)
  "shen-scheme" _ N -> [host (cn "chez:" N)]
  "shen-cl" _ N -> [shen N] where (buri.pt-lower? N)
  "shen-cl" _ N -> [host (cn "sbcl:" N)])
(define buri.pt-strip-scm N -> (if (buri.pt-prefix? "scm." N) (buri.pt-drop 4 N) N))

\\ Closure: [Defs Externals]; Defs are [Path Blob Name Start End].
(define buri.pt-closure Port Db Roots -> (buri.pt-close Port Db (map (/. R [none R]) Roots) [] []))
(define buri.pt-close _ _ [] Defs Ext -> [(reverse Defs) (reverse Ext)]
  Port Db [[D N] | Todo] Defs Ext ->
   (let Found (if (= D shen) [] (buri.pt-resolve Port N Db))
     (if (= Found [])
         (let X (buri.pt-external Port D N)
           (buri.pt-close Port Db Todo Defs (if (element? X Ext) Ext [X | Ext])))
         (buri.pt-close-defs Port Db Found Todo Defs Ext))))
(define buri.pt-close-defs Port Db [] Todo Defs Ext -> (buri.pt-close Port Db Todo Defs Ext)
  Port Db [[P B D Def] | R] Todo Defs Ext ->
   (let Key [P B (buri.pi-def-name Def) (buri.pt-start Def) (buri.pt-end Def)]
     (if (element? Key Defs)
         (buri.pt-close-defs Port Db R Todo Defs Ext)
         (buri.pt-close-defs Port Db R (append Todo (map (/. F [D F]) (buri.pi-free Def D))) [Key | Defs] Ext))))
(define buri.pt-start [_ _ S | _] -> S)
(define buri.pt-end [_ _ _ E | _] -> E)

\\ Owning package of each remaining host operation (E2E-21..27). E2E-24 owns
\\ every reachable host-language runtime routine not owned more specifically.
(define buri.pt-owner Op -> (buri.pt-owner-h (buri.pt-after-colon Op)))
(define buri.pt-after-colon S -> (buri.pt-after-colon-h (explode S)))
(define buri.pt-after-colon-h [":" | R] -> (buri.pt-implode R)  [_ | R] -> (buri.pt-after-colon-h R)  [] -> "")
(define buri.pt-implode [] -> ""  [C | R] -> (cn C (buri.pt-implode R)))
(define buri.pt-owner-h N -> "E2E-22" where (element? N ["if" "cond" "case" "and" "or" "let" "let*" "letrec" "do" "lambda"
    "define" "set!" "when" "unless" "guard" "parameterize" "quote" "begin" "syntax-rules" "define-syntax" "else"])
  N -> "E2E-23" where (element? N ["IF" "COND" "LET" "LET*" "AND" "OR" "LOOP" "PROGN" "LAMBDA" "FUNCTION" "QUOTE" "SETQ"
    "SETF" "WHEN" "UNLESS" "DOLIST" "DOTIMES" "MULTIPLE-VALUE-BIND" "DESTRUCTURING-BIND" "HANDLER-CASE" "HANDLER-BIND"
    "THE" "BLOCK" "RETURN" "RETURN-FROM" "TAGBODY" "GO" "LOCALLY" "FLET" "LABELS" "PUSH" "CASE" "INCF" "DECF"
    "IGNORE-ERRORS" "EVAL-WHEN" "ASSERT" "WITH-OUTPUT-TO-STRING" "WITH-INPUT-FROM-STRING" "WITH-OPEN-FILE" "VALUES"])
  N -> "E2E-26" where (element? N ["eval" "compile" "compile-file" "compile-to-file" "compile-program" "compile-whole-program"
    "load" "interaction-environment" "copy-environment" "EVAL" "COMPILE" "COMPILE-FILE" "LOAD"])
  N -> "E2E-27" where (buri.pt-io? N)
  N -> "E2E-25" where (element? N ["cons" "list" "make-vector" "make-string" "string-append" "substring" "string" "vector"
    "make-hashtable" "make-parameter" "string->list" "list->string" "append" "make-transcoder" "CONS" "LIST" "MAKE-ARRAY"
    "MAKE-STRING" "CONCATENATE" "SUBSEQ" "GENSYM" "ACONS" "APPEND" "REVERSE" "NREVERSE" "MAPCAR" "LIST*" "COPY-LIST" "COPY-SEQ"])
  N -> "E2E-21" where (element? N ["pair?" "car" "cdr" "cadr" "caadr" "null?" "eq?" "eqv?" "equal?" "vector?" "vector-ref"
    "vector-set!" "vector-length" "boolean?" "symbol?" "string?" "number?" "integer?" "char?" "procedure?" "string-ref"
    "string-length" "char->integer" "integer->char" "symbol->string" "string->symbol" "not" "zero?" "memq" "assq"
    "CONSP" "CAR" "CDR" "CDDR" "CDAR" "CDDDR" "CDDDDR" "NULL" "EQ" "EQL" "EQUAL" "EQUALP" "SVREF" "AREF" "ARRAYP"
    "STRINGP" "SYMBOLP" "NUMBERP" "INTEGERP" "FLOATP" "TYPEP" "SIMPLE-VECTOR-P" "FUNCTIONP" "CHARACTERP" "LISTP" "ATOM"
    "LENGTH" "SYMBOL-VALUE" "SYMBOL-NAME" "BOUNDP" "SET" "CHAR" "CHAR-CODE" "CODE-CHAR" "NOT" "SECOND" "THIRD" "FOURTH"
    "ASSOC" "MEMBER" "SB-SYS:%PRIMITIVE" "SB-C:FAST-SYMBOL-VALUE" "SB-INT:UNBOUND-MARKER-P" "CHAR-CODE-LIMIT"
    "ARRAY-TOTAL-SIZE-LIMIT" "parameter-object-call" "special-variable-read"])
  _ -> "E2E-24")
(define buri.pt-io? N -> (buri.pt-any-infix? N ["port" "file" "time" "directory" "stream" "STREAM" "FILE" "TIME" "u8"
  "BYTE" "byte" "OPEN" "CLOSE" "eof" "flush" "path" "mkdir" "STANDARD-" "ERROR-OUTPUT" "home" "TIME-UNITS"]))
(define buri.pt-any-infix? N Xs -> (buri.pt-any (/. X (buri.pt-infix? X N)) Xs))
(define buri.pt-any _ [] -> false  F [X | Xs] -> (or (F X) (buri.pt-any F Xs)))
(define buri.pt-infix? P S -> (buri.pt-infix-h (explode P) (explode S)))
(define buri.pt-infix-h P [] -> (= P [])
  P S -> true where (buri.pt-prefix-h P S)
  P [_ | S] -> (buri.pt-infix-h P S))

\\ ---------- Reviewed implementation roots and evidence ----------
\\ Entry: [Primitive Kind Rule Impls Evidence]. Kind: kl (one of the 36
\\ KLSyntax primitives) or extra (a registered port primitive). Impls:
\\ [def Name] or [inline Clause Ops]. Evidence: [Kind Theorems Contracts Note]
\\ with Kind proved (captured body proved in Rocq under the named host
\\ contracts), contract-assumed, sampled or none.
(define buri.pt-none -> [none [] [] ""])
(define buri.pt-host Note -> [contract-assumed [] [] Note])
(define buri.pt-scheme-entries ->
 [["intern" kl "rule_intern" [[inline "compile-expression [intern S] where (string? S): compile-time quote" ["quote"]] [def "kl:intern"]] (buri.pt-none)]
  ["pos" kl "rule_pos" [[inline "compile-expression [pos S N]" ["string" "string-ref"]]] (buri.pt-host "Inlined Chez string-ref; bounds errors are Chez conditions.")]
  ["tlstr" kl "rule_tlstr" [[inline "compile-expression [tlstr S]" ["let" "substring" "string-length"]]] (buri.pt-host "Inlined Chez substring.")]
  ["cn" kl "rule_cn" [[inline "binary-op-mapping cn" ["string-append"]]] (buri.pt-host "Mapped directly to Chez string-append.")]
  ["str" kl "rule_str" [[def "kl:str"]] (buri.pt-none)]
  ["string?" kl "rule_stringp" [[inline "unary-op-mapping string?" ["string?"]]] (buri.pt-host "Mapped directly to Chez string?.")]
  ["n->string" kl "rule_n_to_string" [[inline "compile-expression [n->string N]" ["string" "integer->char"]]] (buri.pt-host "Inlined Chez integer->char.")]
  ["string->n" kl "rule_string_to_n" [[inline "compile-expression [string->n S]" ["char->integer" "string-ref"]]] (buri.pt-host "Inlined Chez string-ref.")]
  ["set" kl "rule_set" [[inline "compile-expression [set Var Value] where (static-global? Var)" ["let" "parameter-object-call"]] [def "kl:set"]] (buri.pt-none)]
  ["value" kl "rule_value" [[inline "compile-expression [value Var] where (static-global? Var)" ["parameter-object-call"]] [def "kl:value"]] (buri.pt-none)]
  ["simple-error" kl "rule_simple_error" [[inline "compile-expression [simple-error Msg]" ["error" "shen-string->unicode"]]] (buri.pt-none)]
  ["error-to-string" kl "rule_error_to_string" [[def "kl:error-to-string"]] (buri.pt-none)]
  ["cons" kl "rule_cons" [[inline "binary-op-mapping cons, listify-conses" ["cons" "list"]]] (buri.pt-host "Mapped directly to Chez cons/list.")]
  ["hd" kl "rule_hd" [[inline "unary-op-mapping hd" ["car"]]] (buri.pt-host "Mapped directly to Chez car (domain error is a Chez condition).")]
  ["tl" kl "rule_tl" [[inline "unary-op-mapping tl" ["cdr"]]] (buri.pt-host "Mapped directly to Chez cdr.")]
  ["cons?" kl "rule_consp" [[inline "unary-op-mapping cons?" ["pair?"]]] (buri.pt-host "Mapped directly to Chez pair?.")]
  ["=" kl "rule_equal" [[def "kl:="] [inline "emit-equality-check" ["eq?" "eqv?" "equal?" "null?"]]]
   [proved ["SchemeWrappers.SchemeWrappers.kl_eq_data" "SchemeWrappers.SchemeWrappers.stock_equality_refines_rule"
            "SchemeWrappers.SchemeWrappers.stock_matches_replacement" "SchemeWrappers.SchemeWrappers.stock_mixed_exactness"
            "SchemeWrappers.SchemeWrappers.model_ops_satisfiable" "SchemeWrappers.SchemeWrappers.scheme_wrappers_admitted"]
    ["SchemeWrappers.chez_equality_ops"]
    "Captured kl:= proved on first-order data (integers, ASCII symbols/strings, Booleans, (), pairs) against rule_equal. Open: the vector branch (vector=?, a do loop), closures, inexact numbers. The compiled literal path emits eqv?, which differs from kl:= on mixed exactness (sampled in tests/primitives.shen)."]]
  ["eval-kl" kl "rule_eval_kl" [[def "kl:eval-kl"]] (buri.pt-none)]
  ["absvector" kl "rule_absvector" [[inline "compile-expression [absvector N]" ["make-vector" "kl:fail"]]] (buri.pt-host "Inlined Chez make-vector filled with (fail).")]
  ["address->" kl "rule_address_set" [[inline "compile-expression [address-> V N X]" ["let" "vector-set!"]]] (buri.pt-host "Inlined Chez vector-set!.")]
  ["<-address" kl "rule_address_get" [[inline "compile-expression [<-address V N]" ["vector-ref"]]] (buri.pt-host "Inlined Chez vector-ref.")]
  ["absvector?" kl "rule_absvectorp" [[inline "unary-op-mapping absvector?" ["vector?"]]] (buri.pt-host "Mapped directly to Chez vector?.")]
  ["write-byte" kl "rule_write_byte" [[def "kl:write-byte"]] (buri.pt-none)]
  ["read-byte" kl "rule_read_byte" [[def "kl:read-byte"]] (buri.pt-none)]
  ["open" kl "rule_open" [[def "kl:open"]] (buri.pt-none)]
  ["close" kl "rule_close" [[def "kl:close"]] (buri.pt-none)]
  ["get-time" kl "rule_get_time" [[def "kl:get-time"]] (buri.pt-none)]
  ["+" kl "rule_arith PAdd" [[inline "binary-op-mapping +" ["+"]]] (buri.pt-host "Mapped directly to Chez + (exact integers unbounded).")]
  ["-" kl "rule_arith PSub" [[inline "binary-op-mapping -" ["-"]]] (buri.pt-host "Mapped directly to Chez -.")]
  ["*" kl "rule_arith PMul" [[inline "binary-op-mapping *" ["*"]]] (buri.pt-host "Mapped directly to Chez *.")]
  ["/" kl "rule_div" [[inline "binary-op-mapping /" ["non-rational-/"]]]
   [proved ["StockDivision.wrapper_contract" "StockDivisionGeneral.all_value_wrapper_contract" "StockDivisionGeneral.signed_exact_wrapper"]
    ["StockDivisionGeneral.operation"] "Captured non-rational-/ proved for every value under named Chez /, integer? and inexact contracts; int_div_inexact is the Chez inexact slot."]]
  [">" kl "rule_cmp PGt" [[inline "binary-op-mapping >" [">"]]] (buri.pt-host "Mapped directly to Chez >.")]
  ["<" kl "rule_cmp PLt" [[inline "binary-op-mapping <" ["<"]]] (buri.pt-host "Mapped directly to Chez <.")]
  [">=" kl "rule_cmp PGe" [[inline "binary-op-mapping >=" [">="]]] (buri.pt-host "Mapped directly to Chez >=.")]
  ["<=" kl "rule_cmp PLe" [[inline "binary-op-mapping <=" ["<="]]] (buri.pt-host "Mapped directly to Chez <=.")]
  ["number?" kl "rule_numberp" [[inline "unary-op-mapping number?" ["number?"]]] (buri.pt-host "Mapped directly to Chez number?.")]
  ["_scm.assert-boolean" extra "if/and/or/cond Boolean check (XNotBoolean)" [[def "kl:_scm.assert-boolean"]]
   [proved ["SchemeWrappers.SchemeWrappers.assert_boolean_body" "SchemeWrappers.SchemeWrappers.guarded_if"
            "SchemeWrappers.SchemeWrappers.model_ops_satisfiable"] ["SchemeWrappers.chez_assert_ops"]
    "Captured wrapper and the (if (kl:_scm.assert-boolean T) A B) shape proved to be the KLambda if rule."]]
  ["non-rational-/" extra "rule_div helper" [[def "non-rational-/"]]
   [proved ["StockDivisionGeneral.all_value_wrapper_contract"] ["StockDivisionGeneral.operation"] "See /."]]
  ["value/or" extra "emit-trap-error-optimize (kernel sources only)" [[def "value/or"]] (buri.pt-none)]
  ["get/or" extra "emit-trap-error-optimize (kernel sources only)" [[def "get/or"]] (buri.pt-none)]
  ["<-address/or" extra "emit-trap-error-optimize (kernel sources only)" [[def "<-address/or"]] (buri.pt-none)]
  ["<-vector/or" extra "emit-trap-error-optimize (kernel sources only)" [[def "<-vector/or"]] (buri.pt-none)]
  ["not" extra "kernel not (overrides.shen)" [[def "kl:not"]] (buri.pt-none)]
  ["boolean?" extra "kernel boolean? (overrides.shen)" [[def "kl:boolean?"]] (buri.pt-none)]
  ["integer?" extra "kernel integer? (overrides.shen)" [[def "kl:integer?"]] (buri.pt-none)]
  ["symbol?" extra "kernel symbol? (overrides.shen)" [[def "kl:symbol?"]] (buri.pt-none)]])
(define buri.pt-cl-wrap Names -> (map (/. N (cn "CLWrappers.CLWrappers." N)) Names))
(define buri.pt-clc Names -> (map (/. N (cn "CLContracts.CLContracts." N)) Names))
(define buri.pt-cl-entries ->
 [["intern" kl "rule_intern" [[inline "compile-expression [intern S] where (string? S): compile-time quote" ["QUOTE"]] [def "intern"]] (buri.pt-none)]
  ["pos" kl "rule_pos" [[def "pos"]] (buri.pt-none)]
  ["tlstr" kl "rule_tlstr" [[def "tlstr"]] (buri.pt-none)]
  ["cn" kl "rule_cn" [[inline "binary-op-mapping cn -> (kl cn)" ["cn"]]] (buri.pt-none)]
  ["str" kl "rule_str" [[def "str"]] (buri.pt-none)]
  ["string?" kl "rule_stringp" [[inline "compile-expression [string? X] -> emit-boolean" ["IF" "STRINGP" "QUOTE"]] [def "string?"]]
   [proved (append (buri.pt-cl-wrap ["string_wrapper" "cl_wrappers_admitted"]) (buri.pt-clc ["captured_contracts"])) ["CLLowering.primitive_contracts.pc_string"]
    "Captured |string?| proved to be the Shen-test refinement of STRINGP at the emitted arity."]]
  ["n->string" kl "rule_n_to_string" [[def "n->string"]] (buri.pt-none)]
  ["string->n" kl "rule_string_to_n" [[def "string->n"]] (buri.pt-none)]
  ["set" kl "rule_set" [[inline "compile-expression [set Sym Exp] -> shen-cl.set-global" ["shen-cl.set-global"]] [def "set"]] (buri.pt-none)]
  ["value" kl "rule_value" [[inline "compile-expression [value Sym] -> Sym" ["special-variable-read"]] [def "value"]] (buri.pt-none)]
  ["simple-error" kl "rule_simple_error" [[def "simple-error"]] (buri.pt-none)]
  ["error-to-string" kl "rule_error_to_string" [[def "error-to-string"]] (buri.pt-none)]
  ["cons" kl "rule_cons" [[inline "binary-op-mapping cons, optimise-static-application" ["CONS" "LIST"]] [def "cons"]] (buri.pt-host "Mapped directly to CL CONS/LIST.")]
  ["hd" kl "rule_hd" [[inline "unary-op-mapping hd" ["CAR"]] [def "hd"]] (buri.pt-host "Mapped directly to CL CAR (CAR of NIL is NIL: domain divergence, owner E2E-16/21).")]
  ["tl" kl "rule_tl" [[inline "unary-op-mapping tl" ["CDR"]] [def "tl"]] (buri.pt-host "Mapped directly to CL CDR.")]
  ["cons?" kl "rule_consp" [[inline "compile-expression [cons? X] -> emit-boolean" ["IF" "CONSP" "QUOTE"]] [def "cons?"]]
   [proved (append (buri.pt-cl-wrap ["cons_wrapper" "cl_wrappers_admitted"]) (buri.pt-clc ["captured_contracts" "all_arity_unjustified"])) ["CLLowering.primitive_contracts.pc_cons"]
    "Captured |cons?| proved to be the Shen-test refinement of CONSP at the emitted arity."]]
  ["=" kl "rule_equal" [[inline "emit-equality-check, optimise-boolean-check" ["IF" "NULL" "EQ" "shen-cl.numeric-equal" "EQUAL" "shen-cl.absequal" "QUOTE"]]]
   [proved (append (buri.pt-cl-wrap ["absequal_data" "equal_data" "eq_rewrite_safe" "eq_rewrite_unsafe" "model_equality_ops" "cl_wrappers_admitted"])
                   (buri.pt-clc ["captured_contracts" "abs_symbolic_right" "abs_symbolic_left" "abs_string_right" "abs_string_left"
                                 "abs_numeric_right" "abs_numeric_left" "numeric_equal_value" "discharged_optimise_sound"]))
    ["CLWrappers.sbcl_equality_ops" "CLContracts.cl_host_ops" "CLContracts.cl_kernel_ops"]
    "Captured absequal proved on first-order data; the EQ rewrite of a quoted comparand is exact iff the comparand is a symbol or NIL (CLLowering.qsafe). Every specialization the optimizer emits (NULL, EQ, EQUAL with a string literal, numeric-equal with a numeric literal) is proved for every value against the captured bodies (CLContracts). Open: the vector branch (cf-vectors LOOP) between two vectors, floats inside =."]]
  ["eval-kl" kl "rule_eval_kl" [[def "eval-kl"]] (buri.pt-none)]
  ["absvector" kl "rule_absvector" [[def "absvector"]] (buri.pt-none)]
  ["address->" kl "rule_address_set" [[def "address->"]] (buri.pt-none)]
  ["<-address" kl "rule_address_get" [[def "<-address"]] (buri.pt-none)]
  ["absvector?" kl "rule_absvectorp" [[inline "compile-expression [absvector? X] -> emit-boolean" ["IF" "shen-cl.absvector-p" "QUOTE"]] [def "absvector?"]] (buri.pt-none)]
  ["write-byte" kl "rule_write_byte" [[def "write-byte"]] (buri.pt-none)]
  ["read-byte" kl "rule_read_byte" [[def "read-byte"]] (buri.pt-none)]
  ["open" kl "rule_open" [[def "open"]] (buri.pt-none)]
  ["close" kl "rule_close" [[def "close"]] (buri.pt-none)]
  ["get-time" kl "rule_get_time" [[def "get-time"]] (buri.pt-none)]
  ["+" kl "rule_arith PAdd" [[inline "binary-op-mapping + -> (kl add), optimise-static-application" ["shen-cl.add" "shen-cl.increment"]]]
   [proved (buri.pt-cl-wrap ["add_int" "arith_refines_rules" "model_arith_ops" "cl_wrappers_admitted"]) ["CLWrappers.sbcl_arith_ops"]
    "Captured shen-cl.add proved exact on all integers, and shen-cl.increment (CLContracts.CLContracts.increment_int). Open: floats."]]
  ["-" kl "rule_arith PSub" [[inline "binary-op-mapping - -> (kl subtract), optimise-static-application" ["shen-cl.subtract" "shen-cl.decrement"]]]
   [proved (buri.pt-cl-wrap ["subtract_int" "arith_refines_rules" "model_arith_ops"]) ["CLWrappers.sbcl_arith_ops"]
    "Captured shen-cl.subtract proved exact on all integers, and shen-cl.decrement (CLContracts.CLContracts.decrement_int). Open: floats."]]
  ["*" kl "rule_arith PMul" [[inline "binary-op-mapping * -> (kl multiply)" ["shen-cl.multiply"]]]
   [proved (buri.pt-cl-wrap ["multiply_int" "multiply_zero_absorbs_symbol" "arith_refines_rules" "model_arith_ops"]) ["CLWrappers.sbcl_arith_ops"]
    "Captured shen-cl.multiply proved exact on all integers; it answers 0 for (* 0 non-number) where KLambda raises (multiply_zero_absorbs_symbol)."]]
  ["/" kl "rule_div" [[inline "binary-op-mapping / -> (kl divide)" ["shen-cl.divide"]]]
   [proved (buri.pt-cl-wrap ["divide_int" "arith_refines_rules" "model_arith_ops"]) ["CLWrappers.sbcl_arith_ops"]
    "Captured shen-cl.divide proved: exact quotient, DIVISION-BY-ZERO, or the host double of x/y (never a ratio); int_div_inexact must be pinned to that conversion."]]
  [">" kl "rule_cmp PGt" [[inline "binary-op-mapping > -> (kl greater?)" ["shen-cl.greater?"]]]
   [proved (buri.pt-cl-wrap ["comparison_wrappers"]) ["CLLowering.primitive_contracts.pc_greater"] "Boolean wrapper of CL >; CL > itself is a host contract."]]
  ["<" kl "rule_cmp PLt" [[inline "binary-op-mapping < -> (kl less?)" ["shen-cl.less?"]]]
   [proved (buri.pt-cl-wrap ["comparison_wrappers"]) ["CLLowering.primitive_contracts.pc_less"] "Boolean wrapper of CL <."]]
  [">=" kl "rule_cmp PGe" [[inline "binary-op-mapping >= -> (kl greater-than-or-equal-to?)" ["shen-cl.greater-than-or-equal-to?"]]]
   [proved (buri.pt-cl-wrap ["comparison_wrappers"]) ["CLLowering.primitive_contracts.pc_greater_eq"] "Boolean wrapper of CL >=."]]
  ["<=" kl "rule_cmp PLe" [[inline "binary-op-mapping <= -> (kl less-than-or-equal-to?)" ["shen-cl.less-than-or-equal-to?"]]]
   [proved (buri.pt-cl-wrap ["comparison_wrappers"]) ["CLLowering.primitive_contracts.pc_less_eq"] "Boolean wrapper of CL <=."]]
  ["number?" kl "rule_numberp" [[inline "compile-expression [number? X] -> emit-boolean" ["IF" "NUMBERP" "QUOTE"]] [def "number?"]]
   [proved (append (buri.pt-cl-wrap ["number_wrapper" "cl_wrappers_admitted"]) (buri.pt-clc ["captured_contracts"])) ["CLLowering.primitive_contracts.pc_number"]
    "Captured |number?| proved to be the Shen-test refinement of NUMBERP at the emitted arity."]]
  ["shen-cl.true?" extra "if/cond Boolean guard (XNotBoolean)" [[def "shen-cl.true?"]]
   [proved ["CLPortGuard.CLPortGuard.actual_guard_refinement" "CLLowering.guard_rule_is_captured_guard"] []
    "Proved by E2E-16 (CLPortGuard); diagnostic text quotiented, FORMAT printer effects are a contract (OB-CL-FORMAT-PRINTER)."]]
  ["shen-cl.equal?" extra "rule_equal Boolean wrapper" [[def "shen-cl.equal?"]]
   [proved (append (buri.pt-cl-wrap ["equal_wrapper" "equal_data" "cl_wrappers_admitted"]) (buri.pt-clc ["captured_contracts"])) ["CLLowering.primitive_contracts.pc_absequal" "CLWrappers.sbcl_equality_ops"]
    "Boolean wrapper of absequal; reached only through lisp. escapes or direct calls; optimiser EQ rewrite exact iff the quoted comparand is symbolic."]]
  ["shen-cl.absequal" extra "rule_equal" [[def "shen-cl.absequal"]]
   [proved (append (buri.pt-cl-wrap ["absequal_data" "model_equality_ops"])
                   (buri.pt-clc ["abs_symbolic_right" "abs_symbolic_left" "abs_string_right" "abs_string_left" "abs_numeric_right" "abs_numeric_left"]))
    ["CLWrappers.sbcl_equality_ops" "CLContracts.cl_host_ops"]
    "Structural equality on first-order data; for every value against a symbol, NIL, string or numeric literal (CLContracts). cf-vectors (two vectors) open."]]
  ["shen-cl.numeric-equal" extra "rule_equal numeric literal" [[def "shen-cl.numeric-equal"]]
   [proved (append (buri.pt-clc ["numeric_equal_value" "abs_numeric_right" "abs_numeric_left" "captured_contracts"]) (buri.pt-cl-wrap ["cl_wrappers_admitted"]))
    ["CLContracts.cl_host_ops"]
    "For every value and every numeric literal the captured body gives the same result as the captured absequal (both reach the same host =), in either operand order (pc_numeric). The numeric meaning of = itself (floats, mixed exactness) is the host contract."]]
  ["shen-cl.add" extra "rule_arith PAdd" [[def "shen-cl.add"]] [proved (buri.pt-cl-wrap ["add_int"]) ["CLWrappers.sbcl_arith_ops"] "See +."]]
  ["shen-cl.subtract" extra "rule_arith PSub" [[def "shen-cl.subtract"]] [proved (buri.pt-cl-wrap ["subtract_int"]) ["CLWrappers.sbcl_arith_ops"] "See -."]]
  ["shen-cl.multiply" extra "rule_arith PMul" [[def "shen-cl.multiply"]] [proved (buri.pt-cl-wrap ["multiply_int" "multiply_zero_absorbs_symbol"]) ["CLWrappers.sbcl_arith_ops"] "See *."]]
  ["shen-cl.divide" extra "rule_div" [[def "shen-cl.divide"]] [proved (buri.pt-cl-wrap ["divide_int"]) ["CLWrappers.sbcl_arith_ops"] "See /."]]
  ["shen-cl.double-precision" extra "numeric coercion helper" [[def "shen-cl.double-precision"]] [proved (buri.pt-cl-wrap ["dp_int"]) ["CLWrappers.sbcl_arith_ops"] "Identity on integers; floats open."]]
  ["shen-cl.greater?" extra "rule_cmp PGt" [[def "shen-cl.greater?"]] [proved (buri.pt-cl-wrap ["comparison_wrappers"]) [] "See >."]]
  ["shen-cl.less?" extra "rule_cmp PLt" [[def "shen-cl.less?"]] [proved (buri.pt-cl-wrap ["comparison_wrappers"]) [] "See <."]]
  ["shen-cl.greater-than-or-equal-to?" extra "rule_cmp PGe" [[def "shen-cl.greater-than-or-equal-to?"]] [proved (buri.pt-cl-wrap ["comparison_wrappers"]) [] "See >=."]]
  ["shen-cl.less-than-or-equal-to?" extra "rule_cmp PLe" [[def "shen-cl.less-than-or-equal-to?"]] [proved (buri.pt-cl-wrap ["comparison_wrappers"]) [] "See <=."]]
  ["shen-cl.increment" extra "rule_arith PAdd (literal 1)" [[def "shen-cl.increment"]]
   [proved (append (buri.pt-clc ["increment_int" "step_refines_rules" "model_step_ops"]) (buri.pt-cl-wrap ["cl_wrappers_admitted"])) ["CLContracts.cl_step_ops"]
    "Captured body exact on every integer: (+ 1 X) and (+ X 1) rewritten to it give rule_arith's z+1. Floats open."]]
  ["shen-cl.decrement" extra "rule_arith PSub (literal 1)" [[def "shen-cl.decrement"]]
   [proved (append (buri.pt-clc ["decrement_int" "step_refines_rules" "model_step_ops"]) (buri.pt-cl-wrap ["cl_wrappers_admitted"])) ["CLContracts.cl_step_ops"]
    "Captured body exact on every integer: (- X 1) rewritten to it gives rule_arith's z-1. Floats open."]]
  ["shen-cl.absvector-p" extra "rule_absvectorp test" [[def "shen-cl.absvector-p"]] (buri.pt-none)]
  ["shen-cl.integral-p" extra "kernel integer? test" [[def "shen-cl.integral-p"]] (buri.pt-none)]
  ["shen-cl.boolean-p" extra "kernel boolean? test" [[def "shen-cl.boolean-p"]] (buri.pt-none)]
  ["shen-cl.pvar-p" extra "kernel shen.pvar? test" [[def "shen-cl.pvar-p"]] (buri.pt-none)]
  ["shen-cl.set-global" extra "rule_set (literal global)" [[def "shen-cl.set-global"]] (buri.pt-none)]
  ["shen-cl.value/or" extra "emit-trap-error-optimise" [[def "shen-cl.value/or"]] (buri.pt-none)]
  ["shen-cl.get/or" extra "emit-trap-error-optimise" [[def "shen-cl.get/or"]] (buri.pt-none)]
  ["shen-cl.<-address/or" extra "emit-trap-error-optimise" [[def "shen-cl.<-address/or"]] (buri.pt-none)]
  ["shen-cl.<-vector/or" extra "emit-trap-error-optimise" [[def "shen-cl.<-vector/or"]] (buri.pt-none)]
  ["if" extra "KLambda if (macro)" [[def "if"]] [sampled [] ["ports/shen-cl-contracts.lisp"] "Modelled by CLLowering's sand/sor rules; native SBCL samples only."]]
  ["and" extra "KLambda and (macro)" [[def "and"]] [sampled [] ["ports/shen-cl-contracts.lisp"] "Strict |and| macro; native SBCL samples only."]]
  ["or" extra "KLambda or (macro)" [[def "or"]] [sampled [] ["ports/shen-cl-contracts.lisp"] "Strict |or| macro; native SBCL samples only."]]
  ["trap-error" extra "KLambda trap-error (macro)" [[def "trap-error"]] (buri.pt-none)]
  ["lambda" extra "KLambda lambda (macro)" [[def "lambda"]] (buri.pt-none)]
  ["let" extra "KLambda let (macro)" [[def "let"]] (buri.pt-none)]
  ["freeze" extra "KLambda freeze (macro)" [[def "freeze"]] (buri.pt-none)]
  ["type" extra "KLambda type" [[def "type"]] (buri.pt-none)]])
(define buri.pt-entries "shen-scheme" -> (buri.pt-scheme-entries)  "shen-cl" -> (buri.pt-cl-entries))
