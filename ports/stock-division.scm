(define (non-rational-/ x y)
  (let ((result (/ x y)))
    (if (integer? result)
        result
        (inexact result))))
