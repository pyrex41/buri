\\ Capture raw compiler data. No variable resolution or Coq AST generation.
(tc -)
(load "shen/wire.shen")
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
