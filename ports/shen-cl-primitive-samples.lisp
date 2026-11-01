;;; SAMPLED native evidence for the E2E-17 Shen-CL wrapper lane (docs/PRIMITIVES.md).
;;; It reads the pinned src/primitives.lsp (blob f9b11c8a0b57c8492e66094d5e236a8711983e7a)
;;; with read-time evaluation disabled and evaluates only the selected
;;; definitions. It is a ground observation of SBCL, never a proof and never an
;;; artifact checker; the universal statements are rocq/CLWrappers.v.
(defpackage :shen (:use :cl))
(in-package :cl-user)
(defvar *wanted* '("simple-error" "cons?" "string?" "number?" "shen-cl.equal?" "shen-cl.absequal"
                   "shen-cl.numeric-equal" "CF-VECTORS" "shen-cl.double-precision" "shen-cl.add"
                   "shen-cl.subtract" "shen-cl.multiply" "shen-cl.divide" "shen-cl.greater?"
                   "shen-cl.less?" "shen-cl.greater-than-or-equal-to?" "shen-cl.less-than-or-equal-to?"))
(defun sym (name) (intern name :shen))
(let ((source (second sb-ext:*posix-argv*)) (forms nil) (wanted (mapcar #'sym *wanted*)))
  (let ((*package* (find-package :shen)) (*read-eval* nil) (*readtable* (copy-readtable nil)))
    (set-dispatch-macro-character #\# #\.
      (lambda (stream subchar arg) (declare (ignore subchar arg))
        ;; The only #. in the selected forms is the array-total-size-limit bound.
        (let ((x (read stream t nil t)))
          (assert (eq x 'array-total-size-limit))
          array-total-size-limit)))
    (with-open-file (in source)
      (loop for form = (read in nil :eof) until (eq form :eof) do
        (when (and (consp form) (member (car form) '(defun defmacro))
                   (member (second form) wanted))
          (push form forms)))))
  (assert (= (length forms) (length wanted)))
  (dolist (form (reverse forms)) (eval form)))
(defun f (name &rest args) (apply (symbol-function (sym name)) args))
(defun outcome (thunk)
  (handler-case (list :value (funcall thunk))
    (division-by-zero () (list :raise 'division-by-zero))
    (type-error () (list :raise 'type-error))
    (error (c) (list :raise (type-of c)))))
(defun expect (what thunk expected)
  (let ((got (outcome thunk)))
    (unless (equalp got expected)
      (error "primitive sample failed: ~A got ~S expected ~S" what got expected))
    (format t "SAMPLE ~A ~S~%" what got)))
(defvar *true* (sym "true"))
(defvar *false* (sym "false"))
;; Exact integer arithmetic, including bignums (KL rule_arith on NInt).
(expect "add-bignum" (lambda () (f "shen-cl.add" (expt 2 70) 1)) (list :value (1+ (expt 2 70))))
(expect "subtract-negative" (lambda () (f "shen-cl.subtract" -3 (expt 2 64))) (list :value (- -3 (expt 2 64))))
(expect "multiply-bignum" (lambda () (f "shen-cl.multiply" (expt 2 40) (expt 2 40))) (list :value (expt 2 80)))
(expect "divide-exact" (lambda () (f "shen-cl.divide" 4 2)) (list :value 2))
(expect "divide-inexact" (lambda () (f "shen-cl.divide" 7 2)) (list :value 3.5d0))
(expect "divide-zero" (lambda () (f "shen-cl.divide" 1 0)) (list :raise 'division-by-zero))
(expect "divide-no-ratio" (lambda () (typep (second (outcome (lambda () (f "shen-cl.divide" 1 3)))) 'double-float))
        (list :value t))
;; Discovered wrapper divergence: an exact zero absorbs a non-number.
(expect "multiply-zero-symbol" (lambda () (f "shen-cl.multiply" 0 *true*)) (list :value 0))
(expect "multiply-zero-string" (lambda () (f "shen-cl.multiply" 0 "s")) (list :value 0))
(expect "multiply-symbol-zero" (lambda () (f "shen-cl.multiply" *true* 0)) (list :raise 'type-error))
(expect "add-symbol" (lambda () (f "shen-cl.add" 0 *true*)) (list :raise 'type-error))
;; Equality: shen-cl.equal? is the Boolean wrapper of absequal; EQ is not.
(expect "equal-list" (lambda () (f "shen-cl.equal?" (list 1 (list 2 "x")) (list 1 (list 2 "x")))) (list :value *true*))
(expect "equal-mixed-number" (lambda () (f "shen-cl.equal?" 1 1.0d0)) (list :value *true*))
(expect "eq-list" (lambda () (eq (list 1 2) (copy-list '(1 2)))) (list :value nil))
(expect "eq-mixed-number" (lambda () (eq 1 1.0d0)) (list :value nil))
(expect "eq-string" (lambda () (eq "ab" (copy-seq "ab"))) (list :value nil))
(expect "eq-symbol" (lambda () (eq *true* (sym "true"))) (list :value t))
(expect "greater-int" (lambda () (f "shen-cl.greater?" (expt 2 70) 3)) (list :value *true*))
(format t "BURI_CL_PRIMITIVE_SAMPLES_OK~%")
