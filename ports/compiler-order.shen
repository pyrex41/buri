(tc -)
(define _scm.merge-nested-lets
  [let [Binding] [let* Bindings Body]] -> [let* [Binding | Bindings] Body]
  [let [Binding1] [let [Binding2] Body]] -> [let* [Binding1 Binding2] Body]
  X -> X)

(define _scm.simple-scheme-expression?
  [quote _] -> true
  [lambda _ | _] -> true
  X -> (not (cons? X)))

(define _scm.has-computation?
  [] -> false
  [X | Xs] -> (or (not (_scm.simple-scheme-expression? X))
                  (_scm.has-computation? Xs)))

(define _scm.fresh-call-variable
  Used -> (let Name (gensym arg)
            (if (= 0 (occurrences Name Used))
                Name
                (_scm.fresh-call-variable Used))))

(define _scm.order-call-inputs
  [] Reversed _ -> (reverse Reversed)
  [X | Xs] Reversed Used
  -> (_scm.order-call-inputs Xs [X | Reversed] Used)
    where (or (_scm.simple-scheme-expression? X)
              (not (_scm.has-computation? Xs)))
  [X | Xs] Reversed Used
  -> (let Var (_scm.fresh-call-variable Used)
       (_scm.merge-nested-lets
        [let [[Var X]]
          (_scm.order-call-inputs Xs [Var | Reversed] [Var | Used])])))

(define _scm.order-call
  Call -> (_scm.order-call-inputs Call [] Call))
