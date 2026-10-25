From Coq Require Import String.
Open Scope string_scope.
Definition stock_division_source : string := "(define (non-rational-/ x y)
  (let ((result (/ x y)))
    (if (integer? result)
        result
        (inexact result))))
".
