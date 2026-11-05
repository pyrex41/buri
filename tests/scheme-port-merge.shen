\\ Finite regressions for the actual source-linked compiler pass.
\\ Universal preservation is checked separately in SchemePortMerge.v.
(tc -)
(load "ports/compiler-merge.shen")

(define buri.scheme-port-assert
  Expected Actual -> true where (= Expected Actual)
  Expected Actual -> (error "Scheme merge regression: expected ~A, got ~A" Expected Actual))

(buri.scheme-port-assert
  [let* [[x 1]] x]
  (_scm.merge-nested-lets [let [[x 1]] [let* [] x]]))

(buri.scheme-port-assert
  [let* [[x 1] [a x] [b a] [c b] [d c]] d]
  (_scm.merge-nested-lets
    [let [[x 1]] [let* [[a x] [b a] [c b] [d c]] d]]))

(buri.scheme-port-assert
  [let* [[x 1] [x [+ x 1]] [x [+ x 1]]] x]
  (_scm.merge-nested-lets
    [let [[x 1]] [let* [[x [+ x 1]] [x [+ x 1]]] x]]))

(buri.scheme-port-assert
  [let* [[x [raise first]] [y [raise second]]] [raise body]]
  (_scm.merge-nested-lets
    [let [[x [raise first]]] [let* [[y [raise second]]] [raise body]]]))

(buri.scheme-port-assert
  [let [[x 1] [y 2]] [let* [[z 3]] z]]
  (_scm.merge-nested-lets [let [[x 1] [y 2]] [let* [[z 3]] z]]))

(output "BURI_TESTS_OK 5~%")
