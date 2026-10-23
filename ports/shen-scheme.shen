\\ Trusted conformance harness. It intentionally executes generated code.
\\ NOT imported by buri.shen; never use it as an untrusted artifact reader.
(tc -)
(define buri.native-name X -> (intern (cn "buri.port." (str X))))
(define buri.native-variable N -> (intern (cn "BURI_VAR_" (str N))))
(define buri.native-literal [int N] -> N [bool B] -> B [str S] -> S
  [sym S] -> [intern (str S)] nil -> []
  [pair A B] -> [cons (buri.native-literal A) (buri.native-literal B)])
(define buri.native E -> (buri.native-h E [] 0))
(define buri.native-h
  [literal V] _ _ -> (buri.native-literal V)
  [var X] Env _ -> (buri.native-bound (buri.get X Env))
  [global Name] _ _ -> [function (buri.native-name Name)]
  [lambda X E] Env N ->
    [lambda (buri.native-variable N) (buri.native-h E [[X (buri.native-variable N)] | Env] (+ N 1))]
  [let X A B] Env N ->
    [let (buri.native-variable N) (buri.native-h A Env (+ N 1))
      (buri.native-h B [[X (buri.native-variable N)] | Env] (+ N 1))]
  [apply F A] Env N -> [(buri.native-h F Env N) (buri.native-h A Env N)]
  [if C A B] Env N -> [if (buri.native-h C Env N) (buri.native-h A Env N) (buri.native-h B Env N)]
  [primitive Op As] Env N -> [Op | (buri.native-args As Env N)]
  [raise E] Env N -> [simple-error (buri.native-h E Env N)]
  [trap E [lambda X H]] Env N ->
    [trap-error (buri.native-h E Env N)
      [lambda (buri.native-variable N)
        [let (buri.native-variable (+ N 1)) [error-to-string (buri.native-variable N)]
          (buri.native-h H [[X (buri.native-variable (+ N 1))] | Env] (+ N 2))]]]
  [freeze E] Env N -> [freeze (buri.native-h E Env N)]
  [thaw E] Env N -> [thaw (buri.native-h E Env N)]
  _ _ _ -> (simple-error "Unsupported native fixture"))
(define buri.native-bound [found X] -> X _ -> (simple-error "Unbound fixture variable"))
(define buri.native-args [] _ _ -> [] [A | As] Env N -> [(buri.native-h A Env N) | (buri.native-args As Env N)])
(define buri.native-reify [] -> nil true -> [bool true] false -> [bool false]
  [A | B] -> [pair (buri.native-reify A) (buri.native-reify B)]
  X -> [int X] where (and (number? X) (buri.exact-integer? X))
  X -> [str X] where (string? X)
  X -> [sym X] where (symbol? X)
  _ -> (simple-error "Unsupported native result"))
(define buri.native-result E ->
  (trap-error [returned (buri.native-reify (eval (buri.native E)))]
              (/. X [raised (error-to-string X)])))
(define buri.compare-native E N ->
  (let Reference (buri.evaluate [] E N)
       Native (buri.native-result E)
    (if (= Reference Native) [passed sampled-agreement E Reference]
      [counterexample native-conformance E Reference Native])))
