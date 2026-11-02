\\ BURI/LEDGER-1: release-charter and obligation-graph coverage checker.
\\ Ledger files are read as byte lists and parsed by the inert JSON reader
\\ below. No ledger byte reaches load, eval, read-from-string or a macro.
\\ A [ledger-consistent ...] verdict is a coverage/closure-bookkeeping result.
\\ It is not proof acceptance: theorem validity is decided only by `make prove`.
(tc -)

\\ ---------------------------------------------------------------------------
\\ Inert JSON subset reader. Values: [obj [[Key V] ...]] [arr Vs] [str S]
\\ [int N] [bool B] null. Integers only; duplicate keys and trailing data are
\\ malformed. \uXXXX escapes are retained as their six literal characters.
(define buri.lj-fail M -> (simple-error (cn "ledger: json: " M)))
(define buri.lj-skip [B | Bs] -> (buri.lj-skip Bs) where (buri.member? B [32 9 10 13])
  Bs -> Bs)
(define buri.lj-digit? B -> (and (>= B 48) (<= B 57)))
(define buri.lj-hex? B -> (or (buri.lj-digit? B) (or (and (>= B 97) (<= B 102)) (and (>= B 65) (<= B 70)))))
(define buri.lj-parse Bytes ->
  (let R (buri.lj-value (buri.lj-skip Bytes))
    (if (= (buri.lj-skip (snd R)) []) (fst R) (buri.lj-fail "trailing data"))))
(define buri.lj-value
  [123 | Bs] -> (buri.lj-object (buri.lj-skip Bs))
  [91 | Bs] -> (buri.lj-array (buri.lj-skip Bs))
  [34 | Bs] -> (buri.lj-string Bs [])
  [116 114 117 101 | Bs] -> (@p [bool true] Bs)
  [102 97 108 115 101 | Bs] -> (@p [bool false] Bs)
  [110 117 108 108 | Bs] -> (@p null Bs)
  [45 B | Bs] -> (buri.lj-negate (buri.lj-number [B | Bs]))
  [B | Bs] -> (buri.lj-number [B | Bs]) where (buri.lj-digit? B)
  _ -> (buri.lj-fail "value expected"))
(define buri.lj-number [48 B | _] -> (buri.lj-fail "leading zero") where (buri.lj-digit? B)
  [B | Bs] -> (buri.lj-digits Bs (- B 48)) where (buri.lj-digit? B)
  _ -> (buri.lj-fail "digit expected"))
(define buri.lj-digits [B | Bs] N -> (buri.lj-digits Bs (+ (* N 10) (- B 48))) where (buri.lj-digit? B)
  [B | _] _ -> (buri.lj-fail "only integer numbers are admitted") where (buri.member? B [46 101 69])
  Bs N -> (@p [int N] Bs))
(define buri.lj-negate R -> (buri.lj-negate-h (fst R) (snd R)))
(define buri.lj-negate-h [int N] Bs -> (@p [int (- 0 N)] Bs))
(define buri.lj-string [34 | Bs] Acc -> (@p [str (buri.lj-text (buri.rev Acc))] Bs)
  [92 E | Bs] Acc -> (buri.lj-escape E Bs Acc)
  [B | Bs] Acc -> (if (< B 32) (buri.lj-fail "control byte in string") (buri.lj-string Bs [B | Acc]))
  _ _ -> (buri.lj-fail "unterminated string"))
(define buri.lj-escape 34 Bs Acc -> (buri.lj-string Bs [34 | Acc])
  92 Bs Acc -> (buri.lj-string Bs [92 | Acc])
  47 Bs Acc -> (buri.lj-string Bs [47 | Acc])
  110 Bs Acc -> (buri.lj-string Bs [10 | Acc])
  116 Bs Acc -> (buri.lj-string Bs [9 | Acc])
  114 Bs Acc -> (buri.lj-string Bs [13 | Acc])
  98 Bs Acc -> (buri.lj-string Bs [8 | Acc])
  102 Bs Acc -> (buri.lj-string Bs [12 | Acc])
  117 [A B C D | Bs] Acc -> (buri.lj-string Bs [D C B A 117 92 | Acc])
    where (and (buri.lj-hex? A) (and (buri.lj-hex? B) (and (buri.lj-hex? C) (buri.lj-hex? D))))
  _ _ _ -> (buri.lj-fail "bad string escape"))
(define buri.lj-text [] -> "" [B | Bs] -> (cn (n->string B) (buri.lj-text Bs)))
(define buri.lj-expect B [B | Bs] -> (buri.lj-skip Bs)
  _ _ -> (buri.lj-fail "punctuation expected"))
(define buri.lj-object [125 | Bs] -> (@p [obj []] Bs)
  Bs -> (buri.lj-member Bs []))
(define buri.lj-member [34 | Bs] Acc ->
  (let K (buri.lj-string Bs [])
       Key (buri.lj-key (fst K))
       V (buri.lj-value (buri.lj-expect 58 (buri.lj-skip (snd K))))
    (if (= (buri.get Key Acc) missing)
        (buri.lj-object-next (buri.lj-skip (snd V)) [[Key (fst V)] | Acc])
        (buri.lj-fail (cn "duplicate key " Key))))
  _ _ -> (buri.lj-fail "object key expected"))
(define buri.lj-key [str S] -> S)
(define buri.lj-object-next [44 | Bs] Acc -> (buri.lj-member (buri.lj-skip Bs) Acc)
  [125 | Bs] Acc -> (@p [obj (buri.rev Acc)] Bs)
  _ _ -> (buri.lj-fail "object separator expected"))
(define buri.lj-array [93 | Bs] -> (@p [arr []] Bs)
  Bs -> (buri.lj-elements Bs []))
(define buri.lj-elements Bs Acc ->
  (let V (buri.lj-value Bs) (buri.lj-array-next (buri.lj-skip (snd V)) [(fst V) | Acc])))
(define buri.lj-array-next [44 | Bs] Acc -> (buri.lj-elements (buri.lj-skip Bs) Acc)
  [93 | Bs] Acc -> (@p [arr (buri.rev Acc)] Bs)
  _ _ -> (buri.lj-fail "array separator expected"))

\\ ---------------------------------------------------------------------------
\\ Shape accessors. A shape failure is `malformed`, never a policy verdict.
(define buri.lfail M -> (simple-error (cn "ledger: shape: " M)))
(define buri.lf Key [obj Pairs] -> (buri.lf-h Key (buri.get Key Pairs))
  Key _ -> (buri.lfail (cn "object expected around field " Key)))
(define buri.lf-h _ [found V] -> V
  Key _ -> (buri.lfail (cn "missing field " Key)))
(define buri.lopt Key Default [obj Pairs] -> (buri.lopt-h Default (buri.get Key Pairs))
  Key _ _ -> (buri.lfail (cn "object expected around field " Key)))
(define buri.lopt-h _ [found V] -> V  Default _ -> Default)
(define buri.ls [str S] -> S  _ -> (buri.lfail "string expected"))
(define buri.la [arr Xs] -> Xs  _ -> (buri.lfail "array expected"))
(define buri.lint [int N] -> N  _ -> (buri.lfail "integer expected"))
(define buri.lbool [bool B] -> B  _ -> (buri.lfail "boolean expected"))
(define buri.lstrs V -> (map (/. X (buri.ls X)) (buri.la V)))
(define buri.lfs Key O -> (buri.ls (buri.lf Key O)))
\\ Optional string field: absent, null and "" are all reported as "".
(define buri.lfs-opt Key O -> (buri.lstr-or-empty (buri.lopt Key [str ""] O)))
(define buri.lstr-or-empty [str S] -> S  null -> ""  _ -> (buri.lfail "string or null expected"))
(define buri.lfa-opt Key O -> (buri.la (buri.lopt Key [arr []] O)))

\\ ---------------------------------------------------------------------------
\\ Small list helpers.
(define buri.lconcat [] -> [] [X | Xs] -> (buri.append X (buri.lconcat Xs)))
(define buri.lfilter _ [] -> [] F [X | Xs] -> (if (F X) [X | (buri.lfilter F Xs)] (buri.lfilter F Xs)))
(define buri.lall? _ [] -> true F [X | Xs] -> (and (F X) (buri.lall? F Xs)))
(define buri.lany? _ [] -> false F [X | Xs] -> (or (F X) (buri.lany? F Xs)))
(define buri.lsubset? Xs Ys -> (buri.lall? (/. X (buri.member? X Ys)) Xs))
(define buri.lset-equal? Xs Ys -> (and (buri.lsubset? Xs Ys) (buri.lsubset? Ys Xs)))
(define buri.ldups [] -> [] [X | Xs] -> (if (buri.member? X Xs) [X | (buri.ldups Xs)] (buri.ldups Xs)))
(define buri.lwhen Condition Violation -> (if Condition [Violation] []))
(define buri.lpath S -> (buri.lpath-h S ""))
(define buri.lpath-h "" Acc -> Acc
  S Acc -> Acc where (= (pos S 0) "#")
  S Acc -> (buri.lpath-h (tlstr S) (cn Acc (pos S 0))))

\\ ---------------------------------------------------------------------------
\\ Required-feature fingerprint: order-independent sum of polynomial string
\\ hashes modulo 2^61-1 over every required feature, property kind and pin id.
\\ It is a tamper-evidence aid, not a cryptographic commitment. Exact integer
\\ addition/multiplication/subtraction only: no division is used.
(define buri.lh-prime -> 2305843009213693951)
(define buri.lh-multiples M 0 Acc -> [M | Acc]
  M K Acc -> (buri.lh-multiples (+ M M) (- K 1) [M | Acc]))
(define buri.lh-reduce A [] -> A
  A [D | Ds] -> (buri.lh-reduce (if (>= A D) (- A D) A) Ds))
(define buri.lh-mod A -> (buri.lh-reduce A (buri.lh-multiples (buri.lh-prime) 9 [])))
(define buri.lh-string S -> (buri.lh-string-h S 7))
(define buri.lh-string-h "" H -> H
  S H -> (buri.lh-string-h (tlstr S) (buri.lh-mod (+ (* H 257) (+ 1 (string->n (pos S 0)))))))
(define buri.lh-sum [] Acc -> Acc
  [S | Ss] Acc -> (buri.lh-sum Ss (buri.lh-mod (+ Acc (buri.lh-string S)))))
(define buri.ledger-fingerprint Ids ->
  (cn "lh61:" (cn (str (length Ids)) (cn ":" (str (buri.lh-sum Ids 0))))))

\\ Frozen charter registry. Changing the required set needs a new version row
\\ here and in the charter history; editing data alone cannot keep a version.
(define buri.ledger-frozen-charters -> [[1 "lh61:95:414996911908889189"]])

\\ ---------------------------------------------------------------------------
\\ Fixed vocabularies.
(define buri.ledger-obligation-kinds ->
  ["model-proof" "implementation-correspondence" "artifact-correspondence" "deployment-identity"])
(define buri.ledger-statuses ->
  ["open" "partial" "assumed" "discharged" "refuted" "superseded" "foundation"])
(define buri.ledger-scopes -> ["universal" "instance"])
(define buri.ledger-evidence-kinds ->
  ["universal-theorem" "ground-derivation" "instance-validation" "sampled-agreement"
   "exhaustive-host-test" "identity-hash" "review" "counterexample"])
\\ Evidence kinds that are checked by the Rocq audit; refs must be audited names.
(define buri.ledger-audited-kinds -> ["universal-theorem" "ground-derivation" "instance-validation"])
(define buri.ledger-feature-categories ->
  ["language-construct" "primitive-family" "library-module" "effect" "numeric-policy"
   "encoding-policy" "concurrency-mode" "compiler-mode" "platform"])
(define buri.ledger-required-properties ->
  ["functional-correctness" "memory-safety" "confinement" "termination" "liveness"
   "confidentiality" "resource-adequacy"])
(define buri.ledger-required-pins ->
  ["shen-kernel" "pr117-overlay" "shen-scheme-release" "shen-scheme-source" "chez-scheme"
   "shen-cl-source" "sbcl" "rocq" "arm-architecture" "arm-abi" "arm-cpu-features"
   "os-profile" "linux-aarch64-host-archive" "compiler-modes"])
(define buri.ledger-package-statuses -> ["planned" "in-progress" "complete"])
(define buri.ledger-settled-statuses -> ["discharged" "superseded" "foundation"])

\\ Which evidence kinds may discharge an obligation of a given scope/kind.
(define buri.ledger-discharging-kinds "universal" _ -> ["universal-theorem"]
  "instance" "deployment-identity" -> ["universal-theorem" "ground-derivation" "instance-validation" "identity-hash"]
  "instance" _ -> ["universal-theorem" "ground-derivation" "instance-validation"]
  _ _ -> [])

\\ ---------------------------------------------------------------------------
\\ Graph reachability and cycles over [[Id Deps] ...].
(define buri.lg-deps Id G -> (buri.lg-deps-h (buri.get Id G)))
(define buri.lg-deps-h [found Ds] -> Ds  _ -> [])
(define buri.lg-reach G Todo Seen -> Seen where (= Todo [])
  G [X | Xs] Seen -> (buri.lg-reach G Xs Seen) where (buri.member? X Seen)
  G [X | Xs] Seen -> (buri.lg-reach G (buri.append (buri.lg-deps X G) Xs) [X | Seen]))
(define buri.lg-reach-table G -> (map (/. Node [(hd Node) (buri.lg-reach G (buri.lg-deps (hd Node) G) [])]) G))
(define buri.lg-reaches? From To Table -> (buri.member? To (buri.lg-deps From Table)))
(define buri.lg-cyclic? Id Table -> (buri.lg-reaches? Id Id Table))
(define buri.lg-scc Id Table ->
  (buri.lfilter (/. Other (and (buri.lg-reaches? Id Other Table) (buri.lg-reaches? Other Id Table)))
     (buri.keys Table)))

\\ ---------------------------------------------------------------------------
\\ Context. Env = [Audited TestIndex ExistingFiles]; computed by the IO wrapper.
(define buri.lenv-audited [A _ _] -> A)
(define buri.lenv-tests [_ T _] -> T)
(define buri.lenv-files [_ _ F] -> F)
(define buri.ltest-registered? File Name Env ->
  (buri.lreg-h Name (buri.get File (buri.lenv-tests Env))))
(define buri.lreg-h Name [found Names] -> (buri.member? Name Names)  _ _ -> false)
(define buri.lfile? Path Env -> (buri.member? (buri.lpath Path) (buri.lenv-files Env)))

\\ ---------------------------------------------------------------------------
\\ Package plan checks.
(define buri.lpkg-id P -> (buri.lfs "id" P))
(define buri.lpkg-deps P -> (buri.lstrs (buri.lf "depends_on" P)))
(define buri.lpkg-status P -> (buri.lfs "status" P))
\\ Package evidence items are either a path string or a typed object
\\ {kind, artifact, claim}; both resolve to the artifact path that must exist.
\\ The kind and claim are retained for reports but never grant completion.
(define buri.lpkg-evidence P -> (map (/. E (buri.lpkg-ev-artifact E)) (buri.la (buri.lopt "evidence" [arr []] P))))
(define buri.lpkg-ev-artifact [str S] -> S
  [obj Pairs] -> (let Kind (buri.lfs "kind" [obj Pairs])
                      Claim (buri.lfs "claim" [obj Pairs])
                   (if (or (= Kind "") (= Claim ""))
                       (buri.lfail "typed evidence needs nonempty kind and claim")
                       (buri.lfs "artifact" [obj Pairs])))
  _ -> (buri.lfail "evidence item must be a path or typed object"))
(define buri.lplan-packages Plan -> (buri.la (buri.lf "work_packages" Plan)))
(define buri.lplan-ids Plan -> (map (/. P (buri.lpkg-id P)) (buri.lplan-packages Plan)))

(define buri.lcheck-plan Plan Obligations Env ->
  (let Packages (buri.lplan-packages Plan)
       Ids (map (/. P (buri.lpkg-id P)) Packages)
       G (map (/. P [(buri.lpkg-id P) (buri.lpkg-deps P)]) Packages)
       Table (buri.lg-reach-table G)
       Complete (map (/. P (buri.lpkg-id P)) (buri.lfilter (/. P (= (buri.lpkg-status P) "complete")) Packages))
    (buri.lconcat
     [(map (/. D [duplicate-package D]) (buri.ldups Ids))
      (buri.lconcat (map (/. P (buri.lcheck-package P Ids Table Complete Obligations Env)) Packages))
      (buri.lwhen (and (buri.lbool (buri.lf "full_plan_complete" Plan))
                       (not (= (length Complete) (length Ids))))
                  [forged-plan-completion "full_plan_complete"])])))

(define buri.lcheck-package P Ids Table Complete Obligations Env ->
  (let Id (buri.lpkg-id P)
       Status (buri.lpkg-status P)
       Evidence (buri.lpkg-evidence P)
       Owned (buri.lfilter (/. O (= (buri.lob-owner O) Id)) Obligations)
    (buri.lconcat
     [(map (/. D [dangling-package-dependency (cn Id (cn " -> " D))])
           (buri.lfilter (/. D (not (buri.member? D Ids))) (buri.lpkg-deps P)))
      (buri.lwhen (buri.lg-cyclic? Id Table) [package-cycle Id])
      (buri.lwhen (not (buri.member? Status (buri.ledger-package-statuses))) [unknown-package-status Id])
      (buri.lwhen (and (= Status "in-progress") (= Evidence [])) [in-progress-without-evidence Id])
      (map (/. E [missing-package-evidence (cn Id (cn " " E))])
           (buri.lfilter (/. E (not (buri.lfile? E Env))) Evidence))
      (buri.lwhen (= Owned []) [package-owns-no-obligation Id])
      (buri.lwhen (and (= Status "complete")
                       (not (buri.lall? (/. O (buri.member? (buri.lob-status O) (buri.ledger-settled-statuses))) Owned)))
                  [complete-package-with-open-obligation Id])
      (buri.lwhen (and (= Status "complete") (not (buri.lsubset? (buri.lpkg-deps P) Complete)))
                  [complete-package-over-incomplete-dependency Id])
      (buri.lwhen (and (= Status "complete") (= Evidence [])) [complete-package-without-evidence Id])])))

\\ ---------------------------------------------------------------------------
\\ Obligation checks.
(define buri.lob-id O -> (buri.lfs "id" O))
(define buri.lob-owner O -> (buri.lfs-opt "owner" O))
(define buri.lob-status O -> (buri.lfs "status" O))
(define buri.lob-kind O -> (buri.lfs "kind" O))
(define buri.lob-scope O -> (buri.lfs "scope" O))
(define buri.lob-deps O -> (buri.lstrs (buri.lopt "depends_on" [arr []] O)))
(define buri.lob-joint O -> (buri.lfs-opt "joint_invariant" O))
(define buri.lob-evidence O -> (buri.lfa-opt "evidence" O))

(define buri.lev-kind E -> (buri.lfs "kind" E))
(define buri.lev-ref E -> (buri.lfs "ref" E))
(define buri.lev-establishes E -> (buri.lfs "establishes" E))

(define buri.lcheck-evidence Id E Env ->
  (let Kind (buri.lev-kind E)
       Ref (buri.lev-ref E)
       Establishes (buri.lev-establishes E)
    (buri.lconcat
     [(buri.lwhen (not (buri.member? Kind (buri.ledger-evidence-kinds))) [unknown-evidence-kind (cn Id (cn " " Kind))])
      (buri.lwhen (not (buri.member? Establishes (buri.ledger-obligation-kinds))) [unknown-evidence-target (cn Id (cn " " Establishes))])
      (buri.lwhen (and (buri.member? Kind (buri.ledger-audited-kinds))
                       (not (buri.member? Ref (buri.lenv-audited Env))))
                  [unaudited-theorem (cn Id (cn " " Ref))])
      (buri.lwhen (and (not (buri.member? Kind (buri.ledger-audited-kinds))) (not (buri.lfile? Ref Env)))
                  [missing-evidence-file (cn Id (cn " " Ref))])
      (buri.lcheck-evidence-test Id E Env)])))
(define buri.lcheck-evidence-test Id E Env ->
  (let Test (buri.lfs-opt "test" E)
    (buri.lwhen (and (not (= Test "")) (not (buri.ltest-registered? (buri.lpath (buri.lev-ref E)) Test Env)))
                [unregistered-test (cn Id (cn " " Test))])))

(define buri.ldischarge-ok? O ->
  (let Allowed (buri.ledger-discharging-kinds (buri.lob-scope O) (buri.lob-kind O))
       Kind (buri.lob-kind O)
    (buri.lany? (/. E (and (buri.member? (buri.lev-kind E) Allowed) (= (buri.lev-establishes E) Kind)))
                (buri.lob-evidence O))))

(define buri.lcheck-obligation O Ids Statuses Packages Table Joints Tags Foundations Env ->
  (let Id (buri.lob-id O)
       Owner (buri.lob-owner O)
       Status (buri.lob-status O)
       Joint (buri.lob-joint O)
       Evidence (buri.lob-evidence O)
       Cyclic (buri.lg-cyclic? Id Table)
       Deps (buri.lob-deps O)
    (buri.lconcat
     [(buri.lwhen (= Owner "") [missing-owner Id])
      (buri.lwhen (and (not (= Owner "")) (not (buri.member? Owner Packages))) [unknown-owner (cn Id (cn " " Owner))])
      (map (/. P [unknown-contributing-package (cn Id (cn " " P))])
           (buri.lfilter (/. P (not (buri.member? P Packages))) (buri.lstrs (buri.lopt "packages" [arr []] O))))
      (buri.lwhen (not (buri.member? (buri.lob-kind O) (buri.ledger-obligation-kinds))) [unknown-obligation-kind Id])
      (buri.lwhen (not (buri.member? (buri.lob-scope O) (buri.ledger-scopes))) [unknown-scope Id])
      (buri.lwhen (not (buri.member? Status (buri.ledger-statuses))) [unknown-status Id])
      (buri.lwhen (= (buri.lfs "statement" O) "") [missing-statement Id])
      (buri.lwhen (= (buri.lfs "boundary" O) "") [missing-boundary Id])
      (buri.lwhen (= (buri.lfs "completion_evidence" O) "") [missing-completion-evidence Id])
      (buri.lwhen (= (buri.lstrs (buri.lf "sources" O)) []) [unsourced-obligation Id])
      (map (/. S [missing-source-file (cn Id (cn " " S))])
           (buri.lfilter (/. S (not (buri.lfile? S Env))) (buri.lstrs (buri.lf "sources" O))))
      (map (/. D [dangling-dependency (cn Id (cn " -> " D))]) (buri.lfilter (/. D (not (buri.member? D Ids))) Deps))
      (buri.lconcat (map (/. E (buri.lcheck-evidence Id E Env)) Evidence))
      (buri.lwhen (and (= Status "discharged") (not (buri.ldischarge-ok? O))) [insufficient-discharge-evidence Id])
      (buri.lwhen (and (= Status "discharged")
                       (buri.lany? (/. D (not (buri.member? (buri.lstatus-of D Statuses) ["discharged" "foundation"]))) Deps))
                  [discharged-over-open-dependency Id])
      (buri.lwhen (and (= Status "partial") (= Evidence [])) [partial-without-evidence Id])
      (buri.lwhen (and (= Status "refuted")
                       (not (buri.lany? (/. E (= (buri.lev-kind E) "counterexample")) Evidence)))
                  [refuted-without-counterexample Id])
      (buri.lcheck-successor Id Status "refuted" "replaced_by" Ids O)
      (buri.lcheck-successor Id Status "superseded" "superseded_by" Ids O)
      (buri.lwhen (and (= Status "foundation") (not (buri.member? (buri.lfs-opt "foundation" O) Foundations)))
                  [unknown-foundation Id])
      (buri.lwhen (and (not (= Joint "")) (not (buri.member? Joint Joints))) [unknown-joint-invariant (cn Id (cn " " Joint))])
      (buri.lwhen (and Cyclic (= Joint "")) [unjustified-cycle Id])
      (buri.lwhen (and Cyclic (not (buri.lall? (/. U (= (buri.lstatus-of U Tags) Joint)) (buri.lg-scc Id Table))))
                  [mixed-joint-invariant-cycle Id])
      (buri.lwhen (and Cyclic (= Status "discharged")) [cycle-member-discharged Id])])))

(define buri.lcheck-successor Id Status Status Field Ids O ->
  (let Next (buri.lfs-opt Field O)
    (buri.lwhen (not (buri.member? Next Ids)) [missing-successor (cn Id (cn " " Field))]))
  _ _ _ _ _ _ -> [])
(define buri.lstatus-of D Statuses -> (buri.lstatus-h (buri.get D Statuses)))
(define buri.lstatus-h [found S] -> S  _ -> "missing")

(define buri.lcheck-graph Graph Charter Plan Env ->
  (let Obligations (buri.la (buri.lf "obligations" Graph))
       Ids (map (/. O (buri.lob-id O)) Obligations)
       Statuses (map (/. O [(buri.lob-id O) (buri.lob-status O)]) Obligations)
       Packages (buri.lplan-ids Plan)
       G (map (/. O [(buri.lob-id O) (buri.lob-deps O)]) Obligations)
       Table (buri.lg-reach-table G)
       JointRecords (buri.lfa-opt "joint_invariants" Graph)
       Joints (map (/. J (buri.lfs "id" J)) JointRecords)
       Tags (map (/. O [(buri.lob-id O) (buri.lob-joint O)]) Obligations)
       Foundations (buri.lstrs (buri.lf "ultimate_foundations" Plan))
    (buri.lconcat
     [(buri.lwhen (not (= (buri.lint (buri.lf "charter_version" Graph)) (buri.lint (buri.lf "charter_version" Charter))))
                  [stale-charter-reference "obligation graph"])
      (map (/. D [duplicate-obligation D]) (buri.ldups Ids))
      (buri.lconcat (map (/. O (buri.lcheck-obligation O Ids Statuses Packages Table Joints Tags Foundations Env)) Obligations))
      (buri.lconcat (map (/. J (buri.lcheck-joint J Packages Tags)) JointRecords))
      (buri.lcheck-legacy (buri.lfa-opt "legacy_inventory_map" Graph) Ids)
      (buri.lcheck-plan Plan Obligations Env)])))
(define buri.lcheck-joint J Packages Tags ->
  (let Id (buri.lfs "id" J)
       Members (buri.lstrs (buri.lf "members" J))
    (buri.lconcat
     [(buri.lwhen (not (buri.member? (buri.lfs-opt "owner" J) Packages)) [unknown-owner (cn Id " joint invariant")])
      (buri.lwhen (= (buri.lfs "status" J) "discharged") [joint-invariant-counted-discharged Id])
      (buri.lwhen (not (buri.lset-equal? Members (buri.keys (buri.lfilter (/. T (= (hd (tl T)) Id)) Tags))))
                  [joint-invariant-member-mismatch Id])])))
\\ Every entry of the older static inventory (shen/claims.shen) must map to a
\\ current obligation; that code is already loaded, it is not ledger input.
(define buri.lcheck-legacy Map Ids ->
  (let Pairs (map (/. E [(buri.lfs "legacy" E) (buri.lfs "obligation" E)]) Map)
    (buri.append
     (map (/. L [unmapped-legacy-obligation L])
          (buri.lfilter (/. L (= (buri.get L Pairs) missing))
                        (map (/. Entry (str (hd Entry))) (buri.obligations))))
     (map (/. P [legacy-maps-to-unknown-obligation (hd P)])
          (buri.lfilter (/. P (not (buri.member? (hd (tl P)) Ids))) Pairs)))))

\\ ---------------------------------------------------------------------------
\\ Charter checks.
(define buri.lcharter-required-ids Charter ->
  (buri.append (map (/. F (cn "feature:" (buri.lfs "id" F))) (buri.la (buri.lf "features" Charter)))
   (buri.append (map (/. P (cn "property:" (buri.lfs "id" P))) (buri.la (buri.lf "properties" Charter)))
                (map (/. P (cn "pin:" (buri.lfs "id" P))) (buri.la (buri.lf "pins" Charter))))))

(define buri.lcheck-charter Charter Plan Graph Env ->
  (let Packages (buri.lplan-ids Plan)
       Obligations (map (/. O (buri.lob-id O)) (buri.la (buri.lf "obligations" Graph)))
       Targets (map (/. T (buri.lfs "id" T)) (buri.la (buri.lf "semantics_targets" Charter)))
       Features (buri.la (buri.lf "features" Charter))
       Properties (buri.la (buri.lf "properties" Charter))
       Pins (buri.la (buri.lf "pins" Charter))
       Required (buri.lcharter-required-ids Charter)
       Fingerprint (buri.ledger-fingerprint Required)
       Version (buri.lint (buri.lf "charter_version" Charter))
       History (buri.la (buri.lf "history" Charter))
    (buri.lconcat
     [(map (/. D [duplicate-required-id D]) (buri.ldups Required))
      (map (/. T (buri.lcheck-target T Packages)) (buri.la (buri.lf "semantics_targets" Charter)))
      (buri.lconcat (map (/. F (buri.lcheck-feature F Packages Targets Obligations Env)) Features))
      (buri.lconcat (map (/. P (buri.lcheck-property P Packages Targets)) Properties))
      (map (/. P [missing-property-kind P])
           (buri.lfilter (/. P (not (buri.member? P (map (/. X (buri.lfs "id" X)) Properties))))
                         (buri.ledger-required-properties)))
      (buri.lconcat (map (/. P (buri.lcheck-pin P Packages Env)) Pins))
      (map (/. P [missing-pin-record P])
           (buri.lfilter (/. P (not (buri.member? P (map (/. X (buri.lfs "id" X)) Pins)))) (buri.ledger-required-pins)))
      (buri.lconcat (map (/. X (buri.lcheck-exclusion X Packages Obligations Env))
                         (buri.lfa-opt "excluded_extensions" Charter)))
      (buri.lwhen (not (= Fingerprint (buri.lfs "required_feature_fingerprint" Charter)))
                  [required-feature-fingerprint-mismatch Fingerprint])
      (buri.lwhen (not (= (buri.get Version (buri.ledger-frozen-charters)) [found Fingerprint]))
                  [required-feature-set-changed-without-version-change Fingerprint])
      (buri.lcheck-history History Version Required)])))

(define buri.lcheck-target T Packages ->
  (if (buri.member? (buri.lfs-opt "owner" T) Packages) [] [unknown-owner (cn (buri.lfs "id" T) " semantics target")]))
(define buri.lfilter-empty Vs -> (buri.lfilter (/. V (not (= V []))) Vs))

(define buri.lcheck-feature F Packages Targets Obligations Env ->
  (let Id (buri.lfs "id" F)
       Owner (buri.lfs-opt "owner" F)
       Status (buri.lfs "status" F)
       Target (buri.lfs-opt "semantics_target" F)
    (buri.lconcat
     [(buri.lwhen (= Owner "") [missing-owner (cn "feature " Id)])
      (buri.lwhen (and (not (= Owner "")) (not (buri.member? Owner Packages))) [unknown-owner (cn "feature " Id)])
      (buri.lwhen (not (buri.member? Target Targets)) [unknown-semantics-target (cn "feature " Id)])
      (buri.lwhen (not (buri.member? (buri.lfs "category" F) (buri.ledger-feature-categories))) [unknown-feature-category Id])
      (buri.lwhen (not (buri.lbool (buri.lf "required" F))) [unrequired-feature-in-required-set Id])
      (buri.lwhen (not (buri.member? Status ["in-scope" "provisional-exclusion"])) [unknown-feature-status Id])
      (map (/. O [dangling-feature-obligation (cn Id (cn " " O))])
           (buri.lfilter (/. O (not (buri.member? O Obligations))) (buri.lstrs (buri.lopt "obligations" [arr []] F))))
      (if (= Status "provisional-exclusion") (buri.lcheck-provisional Id (buri.lf "exclusion" F) Packages Env) [])
      (buri.lconcat (map (/. X (buri.lcheck-difference Id X Packages Env)) (buri.lfa-opt "profile_differences" F)))])))

\\ A deliberate reference-profile difference inside an in-scope feature: an
\\ owning package and at least one registered enforcement test.
(define buri.lcheck-difference Id X Packages Env ->
  (let Did (cn Id (cn " " (buri.lfs "id" X)))
       Tests (buri.lfa-opt "enforcement_tests" X)
    (buri.lconcat
     [(buri.lwhen (not (buri.member? (buri.lfs-opt "owner" X) Packages)) [difference-without-owner Did])
      (buri.lwhen (= Tests []) [difference-without-enforcement-test Did])
      (map (/. T [unregistered-enforcement-test (cn Did (cn " " (buri.lfs "test" T)))])
           (buri.lfilter (/. T (not (buri.ltest-registered? (buri.lfs "file" T) (buri.lfs "test" T) Env))) Tests))])))

(define buri.lcheck-provisional Id X Packages Env ->
  (let Closure (buri.lfs-opt "closure_package" X)
       Tests (buri.la (buri.lf "enforcement_tests" X))
    (buri.lconcat
     [(buri.lwhen (not (buri.member? Closure Packages)) [exclusion-without-closure-package Id])
      (buri.lwhen (= Tests []) [exclusion-without-enforcement-test Id])
      (map (/. T [unregistered-enforcement-test (cn Id (cn " " (buri.lfs "test" T)))])
           (buri.lfilter (/. T (not (buri.ltest-registered? (buri.lfs "file" T) (buri.lfs "test" T) Env))) Tests))])))

(define buri.lcheck-property P Packages Targets ->
  (let Id (buri.lfs "id" P)
    (buri.lconcat
     [(buri.lwhen (not (buri.member? (buri.lfs-opt "owner" P) Packages)) [unknown-owner (cn "property " Id)])
      (buri.lwhen (not (buri.member? (buri.lfs-opt "semantics_target" P) Targets)) [unknown-semantics-target (cn "property " Id)])
      (buri.lwhen (= (buri.lfs "definition" P) "") [undefined-property Id])
      (buri.lwhen (= (buri.lfs "not_implied_by" P) "") [property-separation-missing Id])])))

(define buri.lcheck-pin P Packages Env ->
  (let Id (buri.lfs "id" P)
       Status (buri.lfs "status" P)
       Value (buri.lfs-opt "value" P)
       Closure (buri.lfs-opt "closure_package" P)
       Source (buri.lfs-opt "source" P)
    (buri.lconcat
     [(buri.lwhen (not (buri.member? Status ["pinned" "identity-only" "unpinned"])) [unknown-pin-status Id])
      (buri.lwhen (and (= Status "pinned") (= Value "")) [pinned-without-value Id])
      (buri.lwhen (and (not (= Status "unpinned")) (not (buri.lfile? Source Env))) [pin-source-missing Id])
      (buri.lwhen (and (= Status "unpinned") (not (= Value ""))) [invented-pin-value Id])
      (buri.lwhen (and (not (= Status "pinned")) (not (buri.member? Closure Packages))) [unpinned-without-closure-package Id])])))

(define buri.lcheck-exclusion X Packages Obligations Env ->
  (let Id (buri.lfs "id" X)
       Tests (buri.lfa-opt "enforcement_tests" X)
       Gap (buri.lfs-opt "enforcement_gap" X)
    (buri.lconcat
     [(buri.lwhen (not (buri.member? (buri.lfs-opt "owner" X) Packages)) [unknown-owner (cn "extension " Id)])
      (buri.lwhen (and (= Tests []) (not (buri.member? Gap Obligations))) [exclusion-unenforced-and-untracked Id])
      (map (/. T [unregistered-enforcement-test (cn Id (cn " " (buri.lfs "test" T)))])
           (buri.lfilter (/. T (not (buri.ltest-registered? (buri.lfs "file" T) (buri.lfs "test" T) Env))) Tests))])))

(define buri.lcheck-history History Version Required ->
  (let Versions (map (/. H (buri.lint (buri.lf "version" H))) History)
    (buri.lconcat
     [(buri.lwhen (not (= Versions (buri.lcount-up 1 (length History)))) [nonconsecutive-charter-history "history"])
      (buri.lwhen (not (= Version (length History))) [charter-version-not-latest-history "history"])
      (if (and (not (= History []))
               (not (buri.lset-equal? Required (buri.lstrs (buri.lf "required" (buri.lindex-last History))))))
          [[required-set-differs-from-history "latest"]] [])
      (buri.lcheck-history-steps History)])))
(define buri.lindex-last [X] -> X  [_ | Xs] -> (buri.lindex-last Xs))
(define buri.lcount-up N Max -> [] where (> N Max)
  N Max -> [N | (buri.lcount-up (+ N 1) Max)])
(define buri.lcheck-history-steps [A B | Rest] ->
  (let Removed (map (/. R (buri.lfs "id" R)) (buri.la (buri.lf "removed" B)))
       Dropped (buri.lfilter (/. X (not (buri.member? X (buri.lstrs (buri.lf "required" B)))))
                            (buri.lstrs (buri.lf "required" A)))
    (buri.append (map (/. X [silent-feature-removal X]) (buri.lfilter (/. X (not (buri.member? X Removed))) Dropped))
                 (buri.lcheck-history-steps [B | Rest])))
  _ -> [])

\\ ---------------------------------------------------------------------------
\\ Pure decision. Removes the [] placeholders produced by lwhen-lists of lists.
(define buri.lclean [] -> []
  [[] | Vs] -> (buri.lclean Vs)
  [V | Vs] -> [V | (buri.lclean Vs)])
(define buri.ledger-decide Charter Plan Graph Env ->
  (trap-error (buri.ledger-decide-h Charter Plan Graph Env)
              (/. E (buri.ledger-error-verdict (error-to-string E)))))
(define buri.ledger-decide-h Charter Plan Graph Env ->
  (let S1 (buri.lfs "schema" Charter) S2 (buri.lfs "schema" Plan) S3 (buri.lfs "schema" Graph)
    (if (not (= [S1 S2 S3] ["buri-release-charter-1" "buri-end-to-end-plan-1" "buri-obligation-graph-1"]))
        [unsupported-schema [S1 S2 S3]]
        (let Violations (buri.lclean (buri.append (buri.lcheck-charter Charter Plan Graph Env)
                                                  (buri.lcheck-graph Graph Charter Plan Env)))
          (if (= Violations [])
              (buri.ledger-summary Charter Graph)
              [rejected Violations])))))
(define buri.ledger-summary Charter Graph ->
  (let Obligations (buri.la (buri.lf "obligations" Graph))
       Count (/. S (length (buri.lfilter (/. O (= (buri.lob-status O) S)) Obligations)))
    [ledger-consistent
     [charter-version (buri.lint (buri.lf "charter_version" Charter))]
     [fingerprint (buri.lfs "required_feature_fingerprint" Charter)]
     [features (length (buri.la (buri.lf "features" Charter)))]
     [obligations (length Obligations)]
     [discharged (Count "discharged")] [partial (Count "partial")] [open (Count "open")]
     [assumed (Count "assumed")] [refuted (Count "refuted")] [superseded (Count "superseded")]
     [foundation (Count "foundation")]]))
(define buri.ledger-error-verdict M ->
  (if (buri.lprefix? "ledger: " M) [malformed M] [unknown host-error M]))
(define buri.lprefix? "" _ -> true
  P S -> (and (not (= S "")) (and (= (pos P 0) (pos S 0)) (buri.lprefix? (tlstr P) (tlstr S)))))

\\ ---------------------------------------------------------------------------
\\ IO wrapper: reads exact bytes, builds Env, then calls the pure decision.
(define buri.lread-json Path -> (buri.lj-parse (read-file-as-bytelist Path)))
(define buri.llines Bytes -> (buri.llines-h Bytes [] []))
(define buri.llines-h [] [] Acc -> (buri.rev Acc)
  [] Line Acc -> (buri.rev [(buri.rev Line) | Acc])
  [10 | Bs] Line Acc -> (buri.llines-h Bs [] [(buri.rev Line) | Acc])
  [B | Bs] Line Acc -> (buri.llines-h Bs [B | Line] Acc))
\\ "Print Assumptions NAME." lines of rocq/Audit.v. Membership shows only that
\\ the name is in the audited inventory; `make prove` replays the proofs.
(define buri.laudit-names Bytes ->
  (buri.lfilter-empty (map (/. L (buri.laudit-line L)) (buri.llines Bytes))))
(define buri.laudit-line
  [80 114 105 110 116 32 65 115 115 117 109 112 116 105 111 110 115 32 | Rest] ->
    (buri.lj-text (buri.ldrop-dot Rest))
  _ -> [])
(define buri.ldrop-dot Bs -> (buri.rev (buri.ldrop-dot-h (buri.rev Bs))))
(define buri.ldrop-dot-h [13 | Bs] -> (buri.ldrop-dot-h Bs)  [46 | Bs] -> Bs  Bs -> Bs)
\\ "(buri.test NAME ..." registrations in a Shen test file.
(define buri.ltest-names Bytes -> (buri.lfilter-empty (map (/. L (buri.ltest-line L)) (buri.llines Bytes))))
(define buri.ltest-line [40 98 117 114 105 46 116 101 115 116 32 | Rest] -> (buri.lj-text (buri.ltoken Rest))
  _ -> [])
(define buri.ltoken [32 | _] -> []  [] -> []  [B | Bs] -> [B | (buri.ltoken Bs)])
(define buri.lexists? Path -> (trap-error (do (close (open Path in)) true) (/. E false)))

(define buri.lreferenced-tests Charter Graph ->
  (buri.append
   (map (/. T (buri.lfs "file" T))
        (buri.lconcat (map (/. F (buri.la (buri.lf "enforcement_tests" (buri.lf "exclusion" F))))
                           (buri.lfilter (/. F (= (buri.lfs "status" F) "provisional-exclusion"))
                                         (buri.la (buri.lf "features" Charter))))))
   (buri.append
    (map (/. T (buri.lfs "file" T))
         (buri.lconcat (map (/. F (buri.lconcat (map (/. X (buri.lfa-opt "enforcement_tests" X)) (buri.lfa-opt "profile_differences" F))))
                            (buri.la (buri.lf "features" Charter)))))
   (buri.append
    (map (/. T (buri.lfs "file" T)) (buri.lconcat (map (/. X (buri.lfa-opt "enforcement_tests" X)) (buri.lfa-opt "excluded_extensions" Charter))))
    (map (/. E (buri.lpath (buri.lev-ref E)))
         (buri.lfilter (/. E (not (= (buri.lfs-opt "test" E) "")))
                       (buri.lconcat (map (/. O (buri.lob-evidence O)) (buri.la (buri.lf "obligations" Graph))))))))))
(define buri.lreferenced-files Charter Plan Graph ->
  (map (/. P (buri.lpath P))
   (buri.lconcat
    [(map (/. P (buri.lfs-opt "source" P)) (buri.la (buri.lf "pins" Charter)))
     (buri.lconcat (map (/. P (buri.lpkg-evidence P)) (buri.lplan-packages Plan)))
     (buri.lconcat (map (/. O (buri.lstrs (buri.lf "sources" O))) (buri.la (buri.lf "obligations" Graph))))
     (map (/. E (buri.lev-ref E)) (buri.lconcat (map (/. O (buri.lob-evidence O)) (buri.la (buri.lf "obligations" Graph)))))])))
(define buri.lunique [] -> [] [X | Xs] -> (if (buri.member? X Xs) (buri.lunique Xs) [X | (buri.lunique Xs)]))

(define buri.ledger-env Charter Plan Graph AuditPath ->
  (let Tests (buri.lunique (buri.lreferenced-tests Charter Graph))
       Files (buri.lfilter (/. P (buri.lexists? P)) (buri.lunique (buri.lreferenced-files Charter Plan Graph)))
    [(buri.laudit-names (read-file-as-bytelist AuditPath))
     (map (/. T [T (if (buri.lexists? T) (buri.ltest-names (read-file-as-bytelist T)) [])]) Tests)
     Files]))

(define buri.ledger-check-files CharterPath PlanPath GraphPath AuditPath ->
  (trap-error
   (let Charter (buri.lread-json CharterPath)
        Plan (buri.lread-json PlanPath)
        Graph (buri.lread-json GraphPath)
     (buri.ledger-decide Charter Plan Graph (buri.ledger-env Charter Plan Graph AuditPath)))
   (/. E (buri.ledger-error-verdict (error-to-string E)))))
(define buri.ledger-check ->
  (buri.ledger-check-files "spec/release-charter.json" "spec/end-to-end-plan.json"
                           "spec/obligations.json" "rocq/Audit.v"))
