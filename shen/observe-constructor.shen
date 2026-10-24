\\ Typed native syntax capture. Booleans are distinct from quoted symbols.
(tc -)
(define buri.native-bytes "" -> []
 S -> [(string->n (pos S 0)) | (buri.native-bytes (tlstr S))])
(define buri.native-node true -> [bool 1]
 false -> [bool 0]
 [] -> [nil]
 [H | T] -> [pair (buri.native-node H) (buri.native-node T)]
 X -> [text (buri.native-bytes X)] where (string? X)
 X -> [num X] where (buri.exact-integer? X)
 X -> [sym X] where (symbol? X)
 _ -> (simple-error "Unsupported native syntax atom"))
(define buri.constructor-forms [] -> []
 [[tc -] | Forms] -> (buri.constructor-forms Forms)
 [Form | Forms] -> (do (buri.install-observed (shen.shen->kl-h Form))
                       (buri.constructor-forms Forms)))
(define buri.observe-constructor Path Bits ->
 (let Source (read-file-as-string Path)
      Mode (set _scm.*native-mode* compatible)
      Locals (set _scm.*native-local-map* [])
      Reset (set buri.observed [])
      Loaded (buri.constructor-forms (read-from-string Source))
      Targets (map (/. R (hd (tl R))) (reverse (value buri.observed)))
  (do (write-to-file (cn Bits ".source") Source)
      (write-to-file Bits (buri.wire [buri-constructor-native-1 (buri.native-node Targets)]))
      (write-to-file (cn Bits ".sexp") (make-string "~S~%" Targets)))))
