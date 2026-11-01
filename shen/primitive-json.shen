\\ E2E-17: named contracts and JSON rendering of the primitive matrix.
\\ Load after shen/primitive-inventory.shen and shen/primitive-table.shen.

\\ Every primitive contract assumed anywhere in the repository, by name:
\\ [Id HostOp Owner Status Note]. Status: host-contract (a premise of a proved
\\ wrapper theorem), discharged-at-use (a CLLowering field now a theorem at the
\\ arity the optimizer emits), assumed (still a premise elsewhere), bridged
\\ (proved on a stated domain), profile-slot (a KLambda profile parameter).
(define buri.pj-fields Prefix Owner Rows -> (map (/. R (buri.pj-field Prefix Owner R)) Rows))
(define buri.pj-field Prefix _ [F Op Owner] -> [(cn Prefix F) Op Owner "host-contract" ""])
(define buri.pj-contracts ->
 (append
  (buri.pj-fields "SchemeWrappers.chez_equality_ops." "" [["chez_eq" "chez:eq?" "E2E-21"] ["chez_number_p" "chez:number?" "E2E-21"]
    ["chez_num_eq" "chez:=" "E2E-24"] ["chez_pair_p" "chez:pair?" "E2E-21"] ["chez_car" "chez:car" "E2E-21"]
    ["chez_cdr" "chez:cdr" "E2E-21"] ["chez_string_p" "chez:string?" "E2E-21"] ["chez_string_eq" "chez:string=?" "E2E-24"]
    ["chez_vector_p" "chez:vector?" "E2E-21"]])
  (append
  (buri.pj-fields "SchemeWrappers.chez_assert_ops." "" [["chez_boolean_p" "chez:boolean?" "E2E-21"] ["chez_error_raises" "chez:error" "E2E-24"]])
  (append
  (buri.pj-fields "CLWrappers.sbcl_equality_ops." "" [["sbcl_eq" "sbcl:EQ" "E2E-21"] ["sbcl_typep_fixnum" "sbcl:TYPEP" "E2E-21"]
    ["sbcl_eql_int" "sbcl:EQL" "E2E-21"] ["sbcl_numberp" "sbcl:NUMBERP" "E2E-21"] ["sbcl_num_eq_int" "sbcl:=" "E2E-24"]
    ["sbcl_consp" "sbcl:CONSP" "E2E-21"] ["sbcl_car" "sbcl:CAR" "E2E-21"] ["sbcl_cdr" "sbcl:CDR" "E2E-21"]
    ["sbcl_stringp" "sbcl:STRINGP" "E2E-21"] ["sbcl_string_eq" "sbcl:STRING=" "E2E-24"] ["sbcl_arrayp" "sbcl:ARRAYP" "E2E-21"]
    ["sbcl_symbolp" "sbcl:SYMBOLP" "E2E-21"]])
  (append
  (buri.pj-fields "CLWrappers.sbcl_arith_ops." "" [["sbcl_fixnum_int" "sbcl:TYPEP" "E2E-21"] ["sbcl_double_int" "sbcl:TYPEP" "E2E-21"]
    ["sbcl_integer_or_double_int" "sbcl:TYPEP" "E2E-21"] ["sbcl_add" "sbcl:+" "E2E-24"] ["sbcl_sub" "sbcl:-" "E2E-24"]
    ["sbcl_mul" "sbcl:*" "E2E-24"] ["sbcl_zerop" "sbcl:ZEROP" "E2E-24"] ["sbcl_div" "sbcl:/" "E2E-24"]
    ["sbcl_integerp_int" "sbcl:INTEGERP" "E2E-21"] ["sbcl_integerp_ratio" "sbcl:INTEGERP" "E2E-21"]
    ["sbcl_coerce_one" "sbcl:COERCE" "E2E-24"] ["sbcl_float_ratio" "sbcl:* (ratio to double rounding)" "E2E-24"]
    ["sbcl_fixnum_sym" "sbcl:TYPEP" "E2E-21"]])
  (append
  [["CLLowering.primitive_contracts.pc_cons" "sbcl:CONSP" "E2E-21" "discharged-at-use" "CLWrappers.CLWrappers.cons_wrapper at arity 1; the all-arity field is stronger than the body (wrong-arity calls raise fresh program-errors)."]
   ["CLLowering.primitive_contracts.pc_string" "sbcl:STRINGP" "E2E-21" "discharged-at-use" "CLWrappers.CLWrappers.string_wrapper at arity 1."]
   ["CLLowering.primitive_contracts.pc_number" "sbcl:NUMBERP" "E2E-21" "discharged-at-use" "CLWrappers.CLWrappers.number_wrapper at arity 1."]
   ["CLLowering.primitive_contracts.pc_empty" "kernel empty? (compiled)" "E2E-16" "assumed" "empty? is kernel Shen code compiled by Shen-CL; no primitives.lsp body."]
   ["CLLowering.primitive_contracts.pc_greater" "sbcl:>" "E2E-24" "discharged-at-use" "CLWrappers.CLWrappers.comparison_wrappers at arity 2."]
   ["CLLowering.primitive_contracts.pc_greater_eq" "sbcl:>=" "E2E-24" "discharged-at-use" "CLWrappers.CLWrappers.comparison_wrappers at arity 2."]
   ["CLLowering.primitive_contracts.pc_less" "sbcl:<" "E2E-24" "discharged-at-use" "CLWrappers.CLWrappers.comparison_wrappers at arity 2."]
   ["CLLowering.primitive_contracts.pc_less_eq" "sbcl:<=" "E2E-24" "discharged-at-use" "CLWrappers.CLWrappers.comparison_wrappers at arity 2."]
   ["CLLowering.primitive_contracts.pc_absequal" "shen-cl.absequal" "E2E-17" "discharged-at-use" "CLWrappers.CLWrappers.equal_wrapper at arity 2; absequal itself: CLWrappers.CLWrappers.absequal_data on data."]
   ["CLLowering.primitive_contracts.pc_not" "kernel not (compiled)" "E2E-16" "assumed" "Kernel not compiled by Shen-CL."]
   ["CLLowering.primitive_contracts.pc_cl_not" "sbcl:NOT" "E2E-21" "assumed" "CL NOT on host truth."]
   ["CLLowering.primitive_contracts.pc_null_right" "sbcl:NULL" "E2E-17" "assumed" "Follows in the functional model from equal_data; the relational bridge is open."]
   ["CLLowering.primitive_contracts.pc_null_left" "sbcl:NULL" "E2E-17" "assumed" "As pc_null_right."]
   ["CLLowering.primitive_contracts.pc_fail" "kernel fail + sbcl:EQ" "E2E-16" "assumed" "(fail) is the symbol shen.fail!; EQ on a symbol is exact by eq_rewrite_safe in the functional model."]
   ["CLLowering.primitive_contracts.pc_string_equal" "sbcl:EQUAL" "E2E-17" "assumed" "EQUAL against a string literal; not yet proved."]
   ["CLLowering.primitive_contracts.pc_numeric" "shen-cl.numeric-equal" "E2E-17" "assumed" "Captured and admitted, not yet proved."]
   ["CLLowering.primitive_contracts.pc_symbol_eq" "sbcl:EQ" "E2E-21" "assumed" "Proved in the functional model (CLWrappers.CLWrappers.eq_rewrite_safe); relational bridge open."]
   ["StockDivisionGeneral.operation.divide" "chez:/" "E2E-24" "host-contract" "Premise of StockDivisionGeneral.all_value_wrapper_contract."]
   ["StockDivisionGeneral.operation.classify" "chez:integer?" "E2E-21" "host-contract" "As divide."]
   ["StockDivisionGeneral.operation.round" "chez:inexact" "E2E-24" "host-contract" "As divide; the int_div_inexact slot."]
   ["EqualityInductionSpecs.ask_eq" "kl:= (sealed replacement equal?)" "E2E-17" "bridged" "SchemeWrappers.SchemeWrappers.stock_matches_replacement: stock kl:= equals equal? on first-order data (EQ1-NUMERIC kl:= part); buri.nat? spelling remains."]
   ["IOReadCorrect.native_read_contract_suffices" "read-file-as-string, *home-directory*" "E2E-27" "assumed" "Chez file read and home-directory lookup."]
   ["EqualitySealCorrect.activation" "chez:eval, interaction-environment" "E2E-26" "assumed" "Chez eval/environment contract of the sealed activation."]
   ["CLPortGuard.format_printer" "sbcl:FORMAT ~A" "E2E-24" "assumed" "OB-CL-FORMAT-PRINTER: printer effects of the Boolean diagnostic."]]
  (append (buri.pj-native-rows)
   (map (/. F [(cn "KLValue.profile." F) "profile slot" "E2E-05" "profile-slot" "A per-port pin is required before any claim depends on it."])
        ["inexact_op" "inexact_cmp" "int_div_inexact" "float_text" "str_other" "sys_message" "absvector_fill" "time_value" "stack_limit" "heap_limit"]))))))))
\\ Native.primitive (OB-PRIM-CONTRACTS): the sealed lane's Chez library table.
(define buri.pj-native-ops -> ["cons" "list" "car" "cdr" "pair?" "null?" "eq?" "eqv?" "equal?" "number?" "integer?" "exact?"
  "boolean?" "string?" "symbol?" "symbol->string" "number->string" "/" "floor" "+" "-" "*" ">=" "<" "string-append"
  "string-length" "string-ref" "string" "char->integer" "substring"])
(define buri.pj-native-rows ->
  (append (map (/. Op [(cn "Native.primitive." Op) (cn "chez:" Op) (buri.pt-owner (cn "chez:" Op)) "assumed"
                       "Sealed-lane Native.v library contract (OB-PRIM-CONTRACTS)."]) (buri.pj-native-ops))
          [["Native.external.error" "chez:error" "E2E-24" "assumed" "Native.v error dispatch."]]))

\\ ---------- JSON ----------
(define buri.pj-esc S -> (buri.pj-esc-h (explode S)))
(define buri.pj-esc-h [] -> ""
  [C | R] -> (cn (n->string 92) (cn C (buri.pj-esc-h R))) where (or (= C (n->string 34)) (= C (n->string 92)))
  [C | R] -> (cn C (buri.pj-esc-h R)))
(define buri.pj-str S -> (cn (n->string 34) (cn (buri.pj-esc S) (n->string 34))))
(define buri.pj-join _ [] -> ""  _ [X] -> X  Sep [X | Xs] -> (cn X (cn Sep (buri.pj-join Sep Xs))))
(define buri.pj-arr Xs -> (cn "[" (cn (buri.pj-join ", " Xs) "]")))
(define buri.pj-strs Xs -> (buri.pj-arr (map (/. X (buri.pj-str X)) Xs)))
(define buri.pj-obj Pairs -> (cn "{" (cn (buri.pj-join ", " (map (/. P (cn (buri.pj-str (hd P)) (cn ": " (hd (tl P))))) Pairs)) "}")))
(define buri.pj-nl -> (n->string 10))

(define buri.pj-impl Port [def N] Db ->
  (let Found (buri.pt-resolve Port N Db)
    (if (= Found []) (simple-error (cn "primitive table: unknown definition " N))
        (buri.pj-arr (map (/. F (buri.pj-def-ref F)) Found))))
  Port [inline C Ops] Db ->
  (buri.pj-arr [(buri.pj-obj [["form" (buri.pj-str "inlined")] ["file" (buri.pj-str (hd (buri.pt-compiler Port)))]
                              ["blob" (buri.pj-str (hd (tl (buri.pt-compiler Port))))] ["clause" (buri.pj-str C)]
                              ["emits" (buri.pj-strs Ops)]])]))
(define buri.pj-def-ref [P B D Def] -> (buri.pj-obj [["form" (buri.pj-str "definition")] ["file" (buri.pj-str P)] ["blob" (buri.pj-str B)]
  ["name" (buri.pj-str (buri.pi-def-name Def))] ["bytes" (buri.pj-arr [(str (buri.pt-start Def)) (str (buri.pt-end Def))])]]))
(define buri.pj-impls Port Impls Db -> (buri.pj-flatten-arrs (map (/. I (buri.pj-impl Port I Db)) Impls)))
\\ Concatenate rendered arrays "[a, b]" "[c]" into "[a, b, c]".
(define buri.pj-flatten-arrs Arrs -> (buri.pj-arr (buri.pj-filter-empty (map (/. A (buri.pj-unbracket A)) Arrs))))
(define buri.pj-unbracket A -> (buri.pj-drop-last (tlstr A)))
(define buri.pj-drop-last S -> (buri.pt-implode (reverse (tl (reverse (explode S))))))
(define buri.pj-filter-empty [] -> []  ["" | R] -> (buri.pj-filter-empty R)  [X | R] -> [X | (buri.pj-filter-empty R)])
(define buri.pj-roots [] -> []
  [[def N] | R] -> [N | (buri.pj-roots R)]
  [[inline _ Ops] | R] -> (append Ops (buri.pj-roots R)))
(define buri.pj-closure Port Impls Db ->
  (let C (buri.pt-closure Port Db (buri.pj-roots Impls))
       Defs (hd C)
       Ext (hd (tl C))
    (buri.pj-obj [["definitions" (buri.pj-arr (map (/. D (buri.pj-closure-def D)) Defs))]
                  ["shen_functions" (buri.pj-strs (buri.pi-sort (buri.pj-of shen Ext)))]
                  ["host_ops" (buri.pj-arr (map (/. Op (buri.pj-obj [["op" (buri.pj-str Op)] ["owner" (buri.pj-str (buri.pt-owner Op))]]))
                                               (buri.pi-sort (buri.pj-of host Ext))))]])))
(define buri.pj-of _ [] -> []  Tag [[Tag X] | R] -> [X | (buri.pj-of Tag R)]  Tag [_ | R] -> (buri.pj-of Tag R))
(define buri.pj-closure-def [P B N S E] -> (buri.pj-obj [["file" (buri.pj-str P)] ["name" (buri.pj-str N)] ["bytes" (buri.pj-arr [(str S) (str E)])]]))
(define buri.pj-evidence [Kind Ths Cs Note] ->
  (buri.pj-obj [["kind" (buri.pj-str (str Kind))] ["theorems" (buri.pj-strs Ths)] ["contracts" (buri.pj-strs Cs)] ["note" (buri.pj-str Note)]]))
(define buri.pj-entry Port Db [Prim Kind Rule Impls Ev] ->
  (buri.pj-obj [["id" (buri.pj-str (cn Port (cn ":" Prim)))] ["port" (buri.pj-str Port)] ["primitive" (buri.pj-str Prim)]
                ["kind" (buri.pj-str (str Kind))] ["rule" (buri.pj-str Rule)]
                ["implementation" (buri.pj-impls Port Impls Db)] ["closure" (buri.pj-closure Port Impls Db)]
                ["evidence" (buri.pj-evidence Ev)]]))
(define buri.pj-port Port ->
  (let Db (buri.pt-db Port)
    (map (/. E (buri.pj-entry Port Db E)) (buri.pt-entries Port))))
(define buri.pj-source [P B D] -> (buri.pj-obj [["path" (buri.pj-str P)] ["blob" (buri.pj-str B)] ["dialect" (buri.pj-str (str D))]]))
(define buri.pj-port-header Port -> (buri.pj-obj [["id" (buri.pj-str Port)] ["revision" (buri.pj-str (buri.pt-revision Port))]
  ["sources" (buri.pj-arr (map (/. S (buri.pj-source S)) (buri.pt-sources Port)))]
  ["compiler" (buri.pj-obj [["path" (buri.pj-str (hd (buri.pt-compiler Port)))] ["blob" (buri.pj-str (hd (tl (buri.pt-compiler Port))))]])]]))
(define buri.pj-contract [Id Op Owner Status Note] ->
  (buri.pj-obj [["id" (buri.pj-str Id)] ["host_op" (buri.pj-str Op)] ["owner" (buri.pj-str Owner)] ["status" (buri.pj-str Status)] ["note" (buri.pj-str Note)]]))
(define buri.pj-cat [] -> ""  [S | Ss] -> (cn S (buri.pj-cat Ss)))
(define buri.pj-field-line K V -> (buri.pj-cat [" " (buri.pj-str K) ": " V]))
(define buri.pj-block Items -> (let Nl (buri.pj-nl) (buri.pj-cat ["[" Nl "  " (buri.pj-join (cn "," (cn Nl "  ")) Items) Nl " ]"])))
(define buri.pj-matrix ->
  (let Nl (buri.pj-nl)
       Entries (append (buri.pj-port "shen-scheme") (buri.pj-port "shen-cl"))
    (buri.pj-cat ["{" Nl
      (buri.pj-join (cn "," Nl)
        [(buri.pj-field-line "schema" (buri.pj-str "buri-primitive-matrix-1"))
         (buri.pj-field-line "package" (buri.pj-str "E2E-17"))
         (buri.pj-field-line "kl_primitives" (buri.pj-str "rocq/KLSyntax.v prim_name"))
         (buri.pj-field-line "generator" (buri.pj-str "shen/primitive-inventory.shen + shen/primitive-table.shen + shen/primitive-json.shen"))
         (buri.pj-field-line "ports" (buri.pj-arr (map (/. P (buri.pj-port-header P)) (buri.pt-ports))))
         (buri.pj-field-line "entries" (buri.pj-block Entries))
         (buri.pj-field-line "contracts" (buri.pj-block (map (/. C (buri.pj-contract C)) (buri.pj-contracts))))])
      Nl "}" Nl])))
(define buri.pj-write Path -> (let Out (open Path out)
                                   Text (buri.pj-matrix)
                                   W (pr Text Out)
                                (do (close Out) written)))
