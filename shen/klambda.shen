\\ BURI/KL-PURE-1. Inert, explicitly tagged syntax; not a general Shen loader.
\\ Fuel bounds evaluation-tree depth, not machine steps or runtime memory.
(tc -)
(define buri.literal?
  [int N] -> (and (number? N) (buri.exact-integer? N))
  [bool true] -> true [bool false] -> true
  [str S] -> (string? S) [sym S] -> (symbol? S)
  nil -> true
  [pair A B] -> (and (buri.literal? A) (buri.literal? B))
  _ -> false)
(define buri.expression?
  [literal V] -> (buri.literal? V)
  [var X] -> (symbol? X)
  [global X] -> (symbol? X)
  [lambda X E] -> (and (symbol? X) (buri.expression? E))
  [apply F A] -> (and (buri.expression? F) (buri.expression? A))
  [let X A B] -> (and (symbol? X) (and (buri.expression? A) (buri.expression? B)))
  [if C A B] -> (and (buri.expression? C) (and (buri.expression? A) (buri.expression? B)))
  [primitive Op Args] -> (and (buri.saturated? Op Args) (buri.expressions? Args))
  [raise E] -> (buri.expression? E)
  [trap E H] -> (and (buri.expression? E) (buri.expression? H))
  [freeze E] -> (buri.expression? E)
  [thaw E] -> (buri.expression? E)
  _ -> false)
\\ Primitive syntax is saturated only: [primitive Op Args] is a direct call of
\\ exactly (arity Op) arguments. KLambda curries and over-applies primitives;
\\ BURI/KL-PURE-1 rejects other arities at admission (release charter
\\ profile difference prim-partial-application on feature kl-currying).
(define buri.saturated?
  Op [_] -> (buri.member? Op [hd tl cons? number? string?])
  Op [_ _] -> (buri.member? Op [+ - * = < cons])
  _ _ -> false)
(define buri.expressions? [] -> true [E | Es] -> (and (buri.expression? E) (buri.expressions? Es)) _ -> false)
(define buri.definitions? D -> (and (buri.definitions-h? D) (buri.unique? (buri.definition-names D))))
(define buri.definitions-h?
  [] -> true
  [[Name Params Body] | Ds] ->
    (and (symbol? Name) (and (buri.all-symbols? Params)
      (and (not (= Params [])) (and (buri.unique? Params)
        (and (buri.expression? Body) (buri.definitions-h? Ds))))))
  _ -> false)
(define buri.definition-names [] -> [] [[N _ _] | Ds] -> [N | (buri.definition-names Ds)])
(define buri.definition N [] -> missing
  N [[M Ps B] | Ds] -> (if (= N M) [definition Ps B] (buri.definition N Ds)))
(define buri.evaluate D E Budget ->
  (trap-error
    (if (and (buri.definitions? D) (and (buri.expression? E) (buri.nat? Budget)))
        (buri.eval D E [] Budget)
        [rejected unsupported-or-malformed-program])
    (/. E [unknown host-error])))
(define buri.eval _ _ _ 0 -> [unknown evaluation-budget]
  _ [literal V] _ _ -> [returned V]
  _ [var X] Env _ -> (buri.lookup-value (buri.get X Env))
  D [global X] _ _ -> (if (= (buri.definition X D) missing) [raised "unbound-function"] [returned [function X []]])
  _ [lambda X E] Env _ -> [returned [closure X E Env]]
  D [let X A B] Env N -> (buri.eval-let (buri.eval D A Env (- N 1)) D X B Env (- N 1))
  D [if C A B] Env N -> (buri.eval-if (buri.eval D C Env (- N 1)) D A B Env (- N 1))
  D [apply F A] Env N -> (buri.eval-function (buri.eval D F Env (- N 1)) D A Env (- N 1))
  D [primitive Op Args] Env N -> (buri.eval-primitive (buri.eval-args D Args Env (- N 1)) Op)
  D [raise E] Env N -> (buri.eval-raise (buri.eval D E Env (- N 1)))
  D [trap E H] Env N -> (buri.eval-trap (buri.eval D E Env (- N 1)) D H Env (- N 1))
  _ [freeze E] Env _ -> [returned [thunk E Env]]
  D [thaw E] Env N -> (buri.eval-thaw (buri.eval D E Env (- N 1)) D (- N 1)))
(define buri.lookup-value [found V] -> [returned V] missing -> [raised "unbound-variable"])
(define buri.eval-let [returned V] D X B Env N -> (buri.eval D B [[X V] | Env] N) R _ _ _ _ _ -> R)
(define buri.eval-if [returned [bool true]] D A _ Env N -> (buri.eval D A Env N)
  [returned [bool false]] D _ B Env N -> (buri.eval D B Env N)
  [returned _] _ _ _ _ _ -> [raised "nonboolean-condition"]
  R _ _ _ _ _ -> R)
(define buri.eval-function [returned F] D A Env N -> (buri.eval-argument (buri.eval D A Env N) D F N)
  R _ _ _ _ -> R)
(define buri.eval-argument [returned A] D F N -> (buri.apply-value D F A N) R _ _ _ -> R)
(define buri.apply-value _ _ _ 0 -> [unknown evaluation-budget]
  D [closure X E Env] A N -> (buri.eval D E [[X A] | Env] (- N 1))
  D [function Name Previous] A N ->
    (buri.apply-global D (buri.definition Name D) Name (buri.append Previous [A]) N)
  _ [thunk _ _] _ _ -> [raised "arity"]
  _ _ _ _ -> [raised "not-callable"])
(define buri.apply-global D [definition Ps B] Name Args N ->
    (if (buri.fewer? Args Ps) [returned [function Name Args]]
        (buri.apply-bound D B (buri.zip Ps Args) N))
  _ _ _ _ _ -> [raised "unbound-function"])
(define buri.fewer? [] [_ | _] -> true [_ | Xs] [_ | Ys] -> (buri.fewer? Xs Ys) _ _ -> false)
(define buri.apply-bound D B [zipped Env] N -> (buri.eval D B Env (- N 1))
  _ _ _ _ -> [raised "arity"])
(define buri.eval-args _ [] _ _ -> [arguments []]
  D [E | Es] Env N -> (buri.eval-args-first (buri.eval D E Env N) D Es Env N))
(define buri.eval-args-first [returned V] D Es Env N -> (buri.eval-args-rest V (buri.eval-args D Es Env N))
  R _ _ _ _ -> R)
(define buri.eval-args-rest V [arguments Vs] -> [arguments [V | Vs]] _ R -> R)
(define buri.eval-primitive [arguments Vs] Op -> (buri.primitive Op Vs) R _ -> R)
(define buri.primitive + [[int A] [int B]] -> [returned [int (+ A B)]]
  - [[int A] [int B]] -> [returned [int (- A B)]]
  * [[int A] [int B]] -> [returned [int (* A B)]]
  < [[int A] [int B]] -> [returned [bool (< A B)]]
  = [A B] -> (buri.equality-verdict (buri.equal A B))
  cons [A B] -> [returned [pair A B]]
  hd [[pair A _]] -> [returned A]
  tl [[pair _ B]] -> [returned B]
  cons? [[pair _ _]] -> [returned [bool true]]
  cons? [_] -> [returned [bool false]]
  number? [[int _]] -> [returned [bool true]]
  number? [_] -> [returned [bool false]]
  string? [[str _]] -> [returned [bool true]]
  string? [_] -> [returned [bool false]]
  _ _ -> [raised "primitive-domain-or-arity"])
\\ KLambda structural equality: pairs left to right; a function value (closure,
\\ function, thunk) is unequal to every non-function value, and equality of two
\\ function values is undefined in the agreed profile (unsupported).
(define buri.function-value? [closure _ _ _] -> true [function _ _] -> true [thunk _ _] -> true _ -> false)
(define buri.equal
  [pair A1 A2] [pair B1 B2] -> (buri.equal-pair (buri.equal A1 B1) A2 B2)
  A B -> (buri.equal-leaf (buri.function-value? A) (buri.function-value? B) A B))
(define buri.equal-pair true A B -> (buri.equal A B) R _ _ -> R)
(define buri.equal-leaf true true _ _ -> unsupported
  false false A B -> (= A B)
  _ _ _ _ -> false)
(define buri.equality-verdict unsupported -> [unsupported closure-equality] B -> [returned [bool B]])
(define buri.eval-raise [returned [str S]] -> [raised S]
  [returned _] -> [raised "error-message-not-string"] R -> R)
(define buri.eval-trap [raised Message] D H Env N ->
    (buri.eval-handler (buri.eval D H Env N) D Message N)
  R _ _ _ _ -> R)
(define buri.eval-handler [returned H] D Message N -> (buri.apply-value D H [str Message] N)
  R _ _ _ -> R)
(define buri.eval-thaw [returned [thunk E Env]] D N -> (buri.eval D E Env N)
  [returned [closure _ _ _]] _ _ -> [raised "arity"]
  [returned [function Name Previous]] D N ->
    (buri.apply-global D (buri.definition Name D) Name Previous N)
  [returned _] _ _ -> [raised "not-callable"] R _ _ -> R)
