\\ BURI/EQ-1 acceptance kernel. Fixed definitions, equality replacement,
\\ universal instantiation, and structural induction over the free expr type.
\\ Search/normalization is NEVER called here. No artifact-supplied axioms.
(tc -)
(define buri.check-bundle
  Theory Bundle Budget ->
    (trap-error
      (if (= Theory (buri.theory))
          (if (buri.nat? Budget) (buri.bundle-h Bundle [] Budget)
              [rejected invalid-budget])
          [rejected theory-mismatch])
      (/. E [rejected malformed-evidence])))
(define buri.bundle-h [] Lemmas _ -> [accepted generic-equations (buri.rev Lemmas)]
  [[theorem Name C L R Proof] | Rest] Lemmas Budget ->
    (if (and (symbol? Name) (= (buri.rule Name Lemmas) missing))
        (if (buri.goal? C L R)
            (buri.bundle-next (buri.check-theorem C L R Proof Lemmas Budget)
              Name C L R Rest Lemmas Budget)
            [rejected ill-sorted-theorem])
        [rejected duplicate-or-invalid-name])
  _ _ _ -> [rejected malformed-bundle])
(define buri.bundle-next checked Name C L R Rest Lemmas N ->
    (buri.bundle-h Rest [[Name C L R] | Lemmas] N)
  Result _ _ _ _ _ _ _ -> Result)
(define buri.goal? C L R ->
  (and (buri.context? C)
    (and (not (= (buri.sort L C) missing)) (= (buri.sort L C) (buri.sort R C)))))
(define buri.check-theorem C L R [direct Steps] Lemmas N ->
    (buri.check-steps L R Steps C [] Lemmas N)
  C L R [induct X Cases] Lemmas N ->
    (if (= (buri.get X C) [found expr])
        (buri.check-cases [[lit [nat]] [add [expr expr]] [mul [expr expr]]]
                          Cases X C L R Lemmas N)
        [rejected unsupported-induction-sort])
  _ _ _ _ _ _ -> [rejected malformed-proof])
(define buri.check-cases [] [] _ _ _ _ _ _ -> checked
  [[Ctor Sorts] | Constructors] [[Ctor Names Steps] | Cases] X C L R Lemmas N ->
    (if (and (buri.all-symbols? Names)
             (and (buri.unique? Names) (buri.fresh? Names (buri.keys C))))
        (buri.check-case-bound (buri.zip Names Sorts) Ctor Constructors Cases
                               Names Steps X C L R Lemmas N)
        [rejected induction-variable-capture])
  _ _ _ _ _ _ _ _ -> [rejected missing-or-wrong-induction-case])
(define buri.fresh? [] _ -> true [X | Xs] Ys -> (and (not (buri.member? X Ys)) (buri.fresh? Xs Ys)))
(define buri.zip [] [] -> [zipped []]
  [X | Xs] [Y | Ys] -> (buri.zip-h X Y (buri.zip Xs Ys))
  _ _ -> mismatch)
(define buri.zip-h X Y [zipped Xs] -> [zipped [[X Y] | Xs]] _ _ _ -> mismatch)
(define buri.variables [] -> [] [X | Xs] -> [[v X] | (buri.variables Xs)])
(define buri.check-case-bound
  [zipped Bindings] Ctor Constructors Cases Names Steps X C L R Lemmas N ->
    (let General (buri.remove X C)
         Branch (buri.append Bindings General)
         Instance [[X [Ctor | (buri.variables Names)]]]
         Hypotheses (buri.induction-hyps Bindings X General L R)
         Result (buri.check-steps (buri.subst L Instance) (buri.subst R Instance)
                                 Steps Branch Hypotheses Lemmas N)
      (if (= Result checked)
          (buri.check-cases Constructors Cases X C L R Lemmas N)
          Result))
  _ _ _ _ _ _ _ _ _ _ _ _ -> [rejected constructor-arity])
(define buri.induction-hyps [] _ _ _ _ -> []
  [[A expr] | Bs] X General L R ->
    [[A General (buri.subst L [[X [v A]]]) (buri.subst R [[X [v A]]])] |
      (buri.induction-hyps Bs X General L R)]
  [_ | Bs] X General L R -> (buri.induction-hyps Bs X General L R))

(define buri.check-steps L R [] _ _ _ _ -> (if (= L R) checked [rejected conclusion-mismatch])
  _ _ [_ | _] _ _ _ 0 -> [unknown proof-budget]
  L R [[rewrite Path Direction Reference Sub] | Steps] C Hs Ls N ->
    (buri.check-step-result
      (buri.instantiate (buri.resolve Reference Hs Ls) Sub C)
      Path Direction L R Steps C Hs Ls N)
  _ _ _ _ _ _ _ -> [rejected malformed-rewrite])
(define buri.resolve [definition Name] _ _ -> (buri.rule Name (buri.rules))
  [hypothesis Name] Hs _ -> (buri.rule Name Hs)
  [lemma Name] _ Ls -> (buri.rule Name Ls)
  _ _ _ -> missing)
(define buri.instantiate [rule Vars L R] Sub C ->
    (if (buri.substitution? Vars Sub C)
        [equation (buri.subst L Sub) (buri.subst R Sub)]
        [rejected invalid-substitution])
  _ _ _ -> [rejected unknown-rule])
(define buri.check-step-result [equation A B] Path forward L R Steps C Hs Ls N ->
    (buri.after-rewrite (buri.replace L Path A B) R Steps C Hs Ls N)
  [equation A B] Path reverse L R Steps C Hs Ls N ->
    (buri.after-rewrite (buri.replace L Path B A) R Steps C Hs Ls N)
  _ _ _ _ _ _ _ _ _ _ -> [rejected invalid-rule-instance])
(define buri.after-rewrite [replaced L] R Steps C Hs Ls N ->
    (buri.check-steps L R Steps C Hs Ls (- N 1))
  _ _ _ _ _ _ _ -> [rejected rewrite-does-not-match])
(define buri.replace A [] A B -> [replaced B]
  [v _] [_ | _] _ _ -> mismatch
  [F | Args] [I | Is] A B ->
    (if (buri.nat? I) (buri.replace-app F (buri.replace-arg Args I Is A B)) mismatch)
  _ _ _ _ -> mismatch)
(define buri.replace-arg [T | Ts] 0 Path A B -> (buri.replace-head (buri.replace T Path A B) Ts)
  [T | Ts] I Path A B -> (buri.replace-tail T (buri.replace-arg Ts (- I 1) Path A B))
  _ _ _ _ _ -> mismatch)
(define buri.replace-head [replaced T] Ts -> [replaced-args [T | Ts]] _ _ -> mismatch)
(define buri.replace-tail T [replaced-args Ts] -> [replaced-args [T | Ts]] _ _ -> mismatch)
(define buri.replace-app F [replaced-args As] -> [replaced [F | As]] _ _ -> mismatch)
