(tc -)
(set buri.tests 0)
(define buri.test Name Actual Expected ->
  (if (= Actual Expected)
      (set buri.tests (+ 1 (value buri.tests)))
      (do (output "FAIL ~A~%actual: ~S~%expected: ~S~%" Name Actual Expected)
          (simple-error "Test failed"))))
(define buri.accepted? [accepted generic-equations _] -> true _ -> false)
(define buri.rejected? [rejected _] -> true _ -> false)
(define buri.swap Old New Old -> New
  Old New [H | T] -> [(buri.swap Old New H) | (buri.swap Old New T)]
  _ _ X -> X)
(define buri.done -> (output "BURI_TESTS_OK ~A~%" (value buri.tests)))
