\\ Reify registered KLambda as inert, explicitly tagged syntax. No eval of
\\ captured syntax. Strings are byte-code lists, never interned as symbols.
(tc -)
(define buri.kl-bytes "" -> []
  S -> [(string->n (pos S 0)) | (buri.kl-bytes (tlstr S))])
(define buri.kl-node
  [] -> [nil]
  [H | T] -> [pair (buri.kl-node H) (buri.kl-node T)]
  X -> [text (buri.kl-bytes X)] where (string? X)
  X -> [num X] where (buri.exact-integer? X)
  X -> [sym X] where (symbol? X)
  _ -> (simple-error "Unsupported KLambda capture atom"))
(define buri.capture-encoder-kl Path Transcript ->
  (let Definitions [(ps buri.wire-byte) (ps buri.wire-string) (ps buri.wire)]
       Data [buri-encoder-kl-1 (buri.kl-node Definitions)]
    (do (write-to-file Path (buri.wire Data))
        (write-to-file Transcript (make-string "~S~%" Definitions)))))
