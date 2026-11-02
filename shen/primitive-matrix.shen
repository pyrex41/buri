\\ E2E-17 primitive coverage matrix checker. It reads spec/primitives.json as
\\ inert data and rejects it unless: every KLambda primitive named in
\\ rocq/KLSyntax.v prim_name and every registered port primitive (recomputed
\\ from the pinned sources) has exactly one entry per port; every "proved"
\\ entry cites theorems, all present in rocq/Audit.v's assumption inventory;
\\ every remaining host operation is owned by one of E2E-21..27; and every
\\ field of the named contract records in the Rocq sources, every Native.v
\\ library operation and every profile slot is a named contract entry.
\\ Membership in the audit list shows only that `make prove` checks the name.
\\ Load after buri.shen, shen/ledger.shen and shen/primitive-inventory.shen.

(define buri.pm-host-owners -> ["E2E-21" "E2E-22" "E2E-23" "E2E-24" "E2E-25" "E2E-26" "E2E-27"])
(define buri.pm-contract-owners -> ["E2E-05" "E2E-16" "E2E-17" "E2E-21" "E2E-22" "E2E-23" "E2E-24" "E2E-25" "E2E-26" "E2E-27"])
(define buri.pm-kinds -> ["proved" "contract-assumed" "sampled" "none"])
(define buri.pm-statuses -> ["host-contract" "discharged" "reduced" "assumed" "bridged" "profile-slot"])

\\ String literals inside the prim_name definition of rocq/KLSyntax.v.
(define buri.pm-kl-names Bytes -> (buri.pm-quoted (buri.pm-between (buri.lj-bytes-of "Definition prim_name") (buri.lj-bytes-of " end.") Bytes)))
(define buri.lj-bytes-of S -> (map (/. C (string->n C)) (explode S)))
(define buri.pm-between Start Stop Bytes -> (buri.pm-upto Stop (buri.pm-after Start Bytes)))
(define buri.pm-after P Bs -> Bs where (buri.pm-starts? P Bs)
  P [] -> (simple-error "primitive matrix: marker not found")
  P [_ | Bs] -> (buri.pm-after P Bs))
(define buri.pm-upto P Bs -> [] where (buri.pm-starts? P Bs)
  _ [] -> []
  P [B | Bs] -> [B | (buri.pm-upto P Bs)])
(define buri.pm-starts? [] _ -> true  [B | P] [B | Bs] -> (buri.pm-starts? P Bs)  _ _ -> false)
(define buri.pm-quoted [] -> []
  [34 | R] -> (buri.pm-quoted-h R [])
  [_ | R] -> (buri.pm-quoted R))
(define buri.pm-quoted-h [] _ -> []
  [34 | R] Acc -> [(buri.lj-text (reverse Acc)) | (buri.pm-quoted R)]
  [B | R] Acc -> (buri.pm-quoted-h R [B | Acc]))

\\ Field names of "Record NAME ... {" up to "}." in Rocq source bytes.
(define buri.pm-record-fields Name Bytes ->
  (buri.pm-fields-lines (buri.llines (buri.pm-upto (buri.lj-bytes-of "}.") (buri.pm-after (buri.lj-bytes-of (cn "Record " (cn Name " "))) Bytes)))))
(define buri.pm-fields-lines Ls -> (buri.lfilter-empty (map (/. L (buri.pm-field-of (buri.pm-trim L))) Ls)))
(define buri.pm-trim [32 | R] -> (buri.pm-trim R)  [123 | R] -> (buri.pm-trim R)  R -> R)
(define buri.pm-field-of L -> (buri.pm-field-h L []))
(define buri.pm-field-h [32 58 | _] Acc -> (buri.lj-text (reverse Acc)) where (not (= Acc []))
  [B | R] Acc -> (buri.pm-field-h R [B | Acc]) where (or (= B 95) (and (>= B 97) (<= B 122)) (and (>= B 48) (<= B 57) (not (= Acc []))))
  _ _ -> [])
\\ Operation names of the Native.v primitive table (lines | "op",...).
(define buri.pm-native-ops Bytes ->
  (buri.pi-dedup (buri.lfilter-empty (map (/. L (buri.pm-native-line (buri.pm-trim L)))
    (buri.llines (buri.pm-between (buri.lj-bytes-of "Definition primitive op args") (buri.lj-bytes-of "| _,_ => None end.") Bytes))))))
(define buri.pm-native-line [124 32 34 | R] -> (buri.pm-native-name R [])  _ -> [])
(define buri.pm-native-name [34 | _] Acc -> (buri.lj-text (reverse Acc))  [B | R] Acc -> (buri.pm-native-name R [B | Acc])  _ _ -> [])

\\ Registered port primitives, recomputed from the pinned sources.
(define buri.pm-symbols Forms -> (buri.pi-dedup (buri.pm-syms-list Forms)))
(define buri.pm-syms-list Xs -> (buri.pi-concat (map (/. X (buri.pm-syms X)) Xs)))
(define buri.pm-syms [l Xs _ _] -> (buri.pm-syms-list Xs)  [y S] -> [S]  [Tag X] -> (buri.pm-syms X) where (element? Tag [quote qq uq fq])  _ -> [])
(define buri.pm-fn-names D Path -> (map (/. Def (buri.pi-def-name Def)) (buri.lfilter (/. Def (not (= (buri.pi-def-kind Def) var))) (buri.pi-defs D (buri.pi-read D Path)))))
(define buri.pm-registered "shen-scheme" KL ->
  (let Names (buri.pm-fn-names scheme "ports/upstream/primitives.scm")
       Syms (buri.pm-symbols (buri.pi-read shen "ports/upstream/compiler.shen"))
    (buri.pi-dedup (append (map (/. N (buri.pt0-drop 3 N)) (buri.lfilter (/. N (buri.pt0-prefix? "kl:" N)) Names))
                           (buri.lfilter (/. N (or (element? N Syms) (element? (cn "scm." N) Syms))) Names))))
  "shen-cl" KL ->
  (let Names (buri.pm-fn-names cl "ports/upstream/shen-cl/primitives.lsp")
       Syms (buri.pm-symbols (buri.pi-read shen "ports/upstream/shen-cl/compiler.shen"))
    (buri.pi-dedup (buri.lfilter (/. N (or (element? N KL) (element? N Syms)
                                       (and (buri.pt0-prefix? "shen-cl." N) (element? (buri.pt0-drop 8 N) Syms)))) Names))))
(define buri.pt0-drop 0 S -> S  N S -> (buri.pt0-drop (- N 1) (tlstr S)))

\\ ---------- The decision ----------
(define buri.pm-entries M -> (buri.la (buri.lf "entries" M)))
(define buri.pm-contract-ids M -> (map (/. C (buri.lfs "id" C)) (buri.la (buri.lf "contracts" M))))
(define buri.pm-port-prims Port M -> (map (/. E (buri.lfs "primitive" E)) (buri.lfilter (/. E (= (buri.lfs "port" E) Port)) (buri.pm-entries M))))
(define buri.pm-decide M KL Registered Audited Expected Files ->
  (let Ids (map (/. E (buri.lfs "id" E)) (buri.pm-entries M))
       Contracts (buri.pm-contract-ids M)
       V (buri.lconcat
          [(map (/. D [duplicate-entry D]) (buri.ldups Ids))
           (map (/. C [duplicate-contract C]) (buri.ldups Contracts))
           (buri.lconcat (map (/. Port (map (/. N [missing-kl-primitive (cn Port (cn ":" N))])
                                            (buri.pi-remove-all KL (buri.pm-port-prims Port M)))) (buri.pt-ports)))
           (buri.lconcat (map (/. P (map (/. N [missing-port-primitive (cn (hd P) (cn ":" N))])
                                         (buri.pi-remove-all (hd (tl P)) (buri.pm-port-prims (hd P) M)))) Registered))
           (buri.lconcat (map (/. E (buri.pm-check-entry E Audited Contracts Files)) (buri.pm-entries M)))
           (buri.lconcat (map (/. C (buri.pm-check-contract C)) (buri.la (buri.lf "contracts" M))))
           (map (/. C [missing-contract C]) (buri.pi-remove-all Expected Contracts))])
    (if (= V []) [primitive-matrix-consistent (length Ids) (length Contracts)] [rejected V])))
(define buri.pm-check-entry E Audited Contracts Files ->
  (let Id (buri.lfs "id" E)
       Ev (buri.lf "evidence" E)
       Kind (buri.lfs "kind" Ev)
       Ths (buri.lstrs (buri.lf "theorems" Ev))
       Cs (buri.lstrs (buri.lf "contracts" Ev))
       Ops (buri.la (buri.lf "host_ops" (buri.lf "closure" E)))
    (buri.lconcat
     [(buri.lwhen (not (buri.member? Kind (buri.pm-kinds))) [unknown-evidence-kind Id])
      (buri.lwhen (and (= Kind "proved") (= Ths [])) [proved-without-theorem Id])
      (map (/. T [unaudited-theorem (cn Id (cn " " T))]) (buri.lfilter (/. T (not (buri.member? T Audited))) Ths))
      (buri.lwhen (= (buri.la (buri.lf "implementation" E)) []) [missing-implementation Id])
      (map (/. O [unowned-host-op (cn Id (cn " " (buri.lfs "op" O)))])
           (buri.lfilter (/. O (not (buri.member? (buri.lfs "owner" O) (buri.pm-host-owners)))) Ops))
      (map (/. C [unknown-contract-reference (cn Id (cn " " C))])
           (buri.lfilter (/. C (not (buri.pm-known-ref? C Contracts Files))) Cs))])))
\\ A cited contract is a contract id, a record named by an id prefix, or a file.
(define buri.pm-known-ref? C Contracts Files -> (or (buri.member? C Contracts)
  (or (buri.lany? (/. K (buri.pt0-prefix? (cn C ".") K)) Contracts) (buri.member? C Files))))
(define buri.pm-check-contract C ->
  (let Id (buri.lfs "id" C)
    (buri.lconcat [(buri.lwhen (not (buri.member? (buri.lfs "owner" C) (buri.pm-contract-owners))) [unowned-contract Id])
                   (buri.lwhen (not (buri.member? (buri.lfs "status" C) (buri.pm-statuses))) [unknown-contract-status Id])])))

\\ Named contract records: [File Record IdPrefix].
(define buri.pm-records ->
  [["rocq/SchemeWrappers.v" "chez_equality_ops" "SchemeWrappers.chez_equality_ops."]
   ["rocq/SchemeWrappers.v" "chez_assert_ops" "SchemeWrappers.chez_assert_ops."]
   ["rocq/CLWrappers.v" "sbcl_equality_ops" "CLWrappers.sbcl_equality_ops."]
   ["rocq/CLWrappers.v" "sbcl_arith_ops" "CLWrappers.sbcl_arith_ops."]
   ["rocq/CLLowering.v" "primitive_contracts" "CLLowering.primitive_contracts."]
   ["rocq/CLContracts.v" "cl_host_ops" "CLContracts.cl_host_ops."]
   ["rocq/CLContracts.v" "cl_kernel_ops" "CLContracts.cl_kernel_ops."]
   ["rocq/CLContracts.v" "cl_step_ops" "CLContracts.cl_step_ops."]
   ["rocq/KLValue.v" "profile" "KLValue.profile."]])
(define buri.pm-expected-contracts ->
  (append (buri.pi-concat (map (/. R (map (/. F (cn (hd (tl (tl R))) F)) (buri.pm-record-fields (hd (tl R)) (read-file-as-bytelist (hd R)))))
                               (buri.pm-records)))
          (map (/. Op (cn "Native.primitive." Op)) (buri.pm-native-ops (read-file-as-bytelist "rocq/Native.v")))))
(define buri.pm-files -> ["ports/shen-cl-contracts.lisp" "ports/shen-cl-primitive-samples.lisp" "tests/primitives.shen"])
(define buri.pm-env ->
  (let KL (buri.pm-kl-names (read-file-as-bytelist "rocq/KLSyntax.v"))
    [KL [["shen-scheme" (buri.pm-registered "shen-scheme" KL)] ["shen-cl" (buri.pm-registered "shen-cl" KL)]]
     (buri.laudit-all "rocq/Audit.v") (buri.pm-expected-contracts)
     (buri.lfilter (/. F (buri.lexists? F)) (buri.pm-files))]))
(define buri.pm-decide-env M [KL Reg Aud Exp Files] -> (buri.pm-decide M KL Reg Aud Exp Files))
(define buri.pm-check Path -> (buri.pm-decide-env (buri.lread-json Path) (buri.pm-env)))
