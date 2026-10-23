\\ Capture raw compiler data. No variable resolution or Coq AST generation.
(tc -)
(define buri.wire-byte N Count ->
  (if (= Count 0) ""
    (let Half (floor (/ N 2))
      (cn (if (= N (* Half 2)) "0" "1") (buri.wire-byte Half (- Count 1))))))
(define buri.wire-string "" -> "0"
  S -> (let N (string->n (pos S 0))
    (if (and (>= N 0) (< N 256))
      (cn "1" (cn (buri.wire-byte N 8) (buri.wire-string (tlstr S))))
      (simple-error "Wire atoms require byte strings"))))
(define buri.wire
  [] -> "00"
  [H | T] -> (cn "1" (cn (buri.wire H) (buri.wire T)))
  N -> (cn "011" (buri.wire-string (str N))) where (buri.exact-integer? N)
  X -> (cn "010" (buri.wire-string (str X))) where (symbol? X)
  _ -> (simple-error "Unsupported wire datum"))
(define buri.capture-records [] -> []
  [[Name Scope Source] | Schemas] ->
    [[Name Scope Source (_scm.compile-expression Source Scope)] | (buri.capture-records Schemas)])
(define buri.capture-wire Path Transcript ->
  (let Data [buri-native-1 (buri.capture-records (buri.compiler-schemas))]
       Bits (open Path out)
       Log (open Transcript out)
    (do (pr (buri.wire Data) Bits)
      (do (pr (make-string "~S~%" Data) Log)
        (do (close Bits) (close Log))))))
