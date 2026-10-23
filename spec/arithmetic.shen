\\ BURI/ARITH-1: an intentionally small, closed compiler-proof theory.
\\ These equations are BOTH executable reference definitions and the kernel's
\\ definition rules. No separate handwritten evaluator/compiler is trusted.
(tc -)
(define buri.signature ->
 [[zero [] nat] [succ [nat] nat]
  [lit [nat] expr] [add [expr expr] expr] [mul [expr expr] expr]
  [nil [] stack] [cons [nat stack] stack]
  [halt [] code] [push [nat code] code] [plus [code] code] [times [code] code]
  [ok [stack] outcome] [fault [] outcome]
  [nadd [nat nat] nat] [nmul [nat nat] nat]
  [eval [expr] nat] [compile [expr code] code] [run [code stack] outcome]])
(define buri.constructors -> [zero succ lit add mul nil cons halt push plus times ok fault])
(define buri.rules ->
 [[nadd-zero [[y nat]] [nadd [zero] [v y]] [v y]]
  [nadd-succ [[x nat] [y nat]] [nadd [succ [v x]] [v y]] [succ [nadd [v x] [v y]]]]
  [nmul-zero [[y nat]] [nmul [zero] [v y]] [zero]]
  [nmul-succ [[x nat] [y nat]] [nmul [succ [v x]] [v y]] [nadd [v y] [nmul [v x] [v y]]]]
  [eval-lit [[n nat]] [eval [lit [v n]]] [v n]]
  [eval-add [[a expr] [b expr]] [eval [add [v a] [v b]]] [nadd [eval [v a]] [eval [v b]]]]
  [eval-mul [[a expr] [b expr]] [eval [mul [v a] [v b]]] [nmul [eval [v a]] [eval [v b]]]]
  [compile-lit [[n nat] [k code]] [compile [lit [v n]] [v k]] [push [v n] [v k]]]
  [compile-add [[a expr] [b expr] [k code]] [compile [add [v a] [v b]] [v k]] [compile [v a] [compile [v b] [plus [v k]]]]]
  [compile-mul [[a expr] [b expr] [k code]] [compile [mul [v a] [v b]] [v k]] [compile [v a] [compile [v b] [times [v k]]]]]
  [run-halt [[s stack]] [run [halt] [v s]] [ok [v s]]]
  [run-push [[n nat] [k code] [s stack]] [run [push [v n] [v k]] [v s]] [run [v k] [cons [v n] [v s]]]]
  [run-plus [[k code] [x nat] [y nat] [s stack]] [run [plus [v k]] [cons [v y] [cons [v x] [v s]]]] [run [v k] [cons [nadd [v x] [v y]] [v s]]]]
  [run-times [[k code] [x nat] [y nat] [s stack]] [run [times [v k]] [cons [v y] [cons [v x] [v s]]]] [run [v k] [cons [nmul [v x] [v y]] [v s]]]]
  [plus-empty [[k code]] [run [plus [v k]] [nil]] [fault]]
  [plus-short [[k code] [x nat]] [run [plus [v k]] [cons [v x] [nil]]] [fault]]
  [times-empty [[k code]] [run [times [v k]] [nil]] [fault]]
  [times-short [[k code] [x nat]] [run [times [v k]] [cons [v x] [nil]]] [fault]]])
(define buri.theory -> [buri-arith-1 (buri.signature) (buri.constructors) (buri.rules)])
