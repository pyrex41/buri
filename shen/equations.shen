\\ Sorted first-order terms and an untrusted reference normalizer.
(tc -)
(define buri.sig F [] -> missing F [[G As R] | Ss] -> (if (= F G) [signature As R] (buri.sig F Ss)))
(define buri.sort
  [v X] C -> (buri.get X C)
  [F | Args] C -> (buri.sort-app (buri.sig F (buri.signature)) Args C)
  _ _ -> missing)
(define buri.sort-app
  [signature Sorts Result] Args C -> (if (buri.args? Args Sorts C) [found Result] missing)
  _ _ _ -> missing)
(define buri.args?
  [] [] _ -> true
  [A | As] [S | Ss] C -> (and (= (buri.sort A C) [found S]) (buri.args? As Ss C))
  _ _ _ -> false)
(define buri.context?
  C -> (and (buri.context-h? C) (buri.unique? (buri.keys C))))
(define buri.context-h?
  [] -> true
  [[X S] | C] -> (and (symbol? X) (and (buri.member? S [nat expr stack code outcome]) (buri.context-h? C)))
  _ -> false)
(define buri.subst [v X] Sub -> (buri.subst-var X (buri.get X Sub))
  [F | Args] Sub -> [F | (buri.substs Args Sub)])
(define buri.subst-var X missing -> [v X] _ [found T] -> T)
(define buri.substs [] _ -> [] [T | Ts] S -> [(buri.subst T S) | (buri.substs Ts S)])
(define buri.substitution?
  [] [] _ -> true
  [[X Sort] | Vars] [[X Term] | Sub] C ->
    (and (= (buri.sort Term C) [found Sort]) (buri.substitution? Vars Sub C))
  _ _ _ -> false)
(define buri.rule Name [] -> missing
  Name [[N Vs L R] | Rs] -> (if (= Name N) [rule Vs L R] (buri.rule Name Rs)))

\\ Matching is search only: the proof checker does not call this normalizer.
(define buri.match [v X] T S -> (buri.bind X T S)
  [F | Ps] [F | Ts] S -> (buri.matches Ps Ts S)
  _ _ _ -> fail)
(define buri.bind _ _ fail -> fail
  X T [match S] -> (buri.bind-h X T S (buri.get X S)))
(define buri.bind-h X T S missing -> [match [[X T] | S]]
  _ T S [found T] -> [match S]
  _ _ _ _ -> fail)
(define buri.matches [] [] S -> S
  [P | Ps] [T | Ts] S -> (buri.matches Ps Ts (buri.match P T S))
  _ _ _ -> fail)
(define buri.reduce T [] -> stable
  T [[_ _ L R] | Rs] -> (buri.reduce-match T R Rs (buri.match L T [match []])))
(define buri.reduce-match T R Rs fail -> (buri.reduce T Rs)
  _ R _ [match S] -> [reduced (buri.subst R S)])
(define buri.normalize
  Term Budget -> (if (and (buri.nat? Budget) (not (= (buri.sort Term []) missing)))
                    (buri.norm Term Budget) [rejected malformed-ground-term]))
(define buri.norm _ 0 -> [unknown normalization-budget]
  [F | Args] N -> (buri.norm-args-result F (buri.norm-list Args (- N 1)) (- N 1)))
(define buri.norm-list [] _ -> [normal-list []]
  [X | Xs] N -> (buri.norm-list-h (buri.norm X N) (buri.norm-list Xs N)))
(define buri.norm-list-h [normal X] [normal-list Xs] -> [normal-list [X | Xs]]
  _ _ -> [unknown normalization-budget])
(define buri.norm-args-result F [normal-list As] N -> (buri.norm-reduced [F | As] (buri.reduce [F | As] (buri.rules)) N)
  _ _ _ -> [unknown normalization-budget])
(define buri.norm-reduced T stable _ -> [normal T]
  _ [reduced T] N -> (buri.norm T N))
