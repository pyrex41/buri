(load "shen/cl-port-guard.shen")
(define buri.cl-test Expect Actual ->
 (if (= Expect Actual) passed (simple-error "CL guard regression")))
(buri.cl-test [accepted cl-strict-boolean-guard-1]
 (buri.cl-admit-capture (read-file-as-string "ports/shen-cl-guard.sexp")))
(buri.cl-test [rejected cl-guard-source-mismatch] (buri.cl-admit-guard []))
(buri.cl-test [returned host-true] (buri.cl-guard-model [bool true]))
(buri.cl-test [returned host-nil] (buri.cl-guard-model [bool false]))
(buri.cl-test [raised boolean-error] (buri.cl-guard-model nil))
(buri.cl-test [raised boolean-error] (buri.cl-guard-model [int 0]))
(buri.cl-test [rejected cl-guard-source-mismatch]
 (buri.cl-admit-capture (cn " " (read-file-as-string "ports/shen-cl-guard.sexp"))))
(output "BURI_TESTS_OK 7~%")
