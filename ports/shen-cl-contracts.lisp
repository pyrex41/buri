;;; Trusted native conformance harness for the Shen-CL lowering lane. It is
;;; SAMPLED evidence for the named primitive contracts of rocq/CLLowering.v
;;; (primitive_contracts, owned by E2E-17), never a proof and never an
;;; artifact checker. It reads the pinned src/primitives.lsp with read-time
;;; evaluation disabled and evaluates only the selected definitions below.
(defpackage :shen (:use :cl))
(in-package :cl-user)
(defvar *wanted* '("if" "and" "or" "simple-error" "cons?" "string?" "number?"
                   "shen-cl.equal?" "shen-cl.absequal" "shen-cl.numeric-equal" "shen-cl.true?"
                   "shen-cl.greater?" "shen-cl.less?" "shen-cl.greater-than-or-equal-to?"
                   "shen-cl.less-than-or-equal-to?"))
(defun sym (name) (intern name :shen))
(let ((source (second sb-ext:*posix-argv*)) (forms nil) (wanted (mapcar #'sym *wanted*)))
  (let ((*package* (find-package :shen)) (*read-eval* nil) (*readtable* (copy-readtable nil)))
    (set-dispatch-macro-character #\# #\.
      (lambda (stream subchar arg) (declare (ignore subchar arg))
        (list :disabled-reader-eval (read stream t nil t))))
    (with-open-file (in source)
      (loop for form = (read in nil :eof) until (eq form :eof) do
        (when (and (consp form) (member (car form) '(defun defmacro))
                   (member (second form) wanted))
          (push form forms)))))
  (assert (= (length forms) (length wanted)))
  (dolist (form (reverse forms)) (eval form)))

(defun f (name &rest args) (apply (symbol-function (sym name)) args))
(defvar *true* (sym "true"))
(defvar *false* (sym "false"))
(defun shen-test (thunk)
  "Observation of (shen-cl.true? (thunk)): :tt, :tf, :tb (Boolean error), :tr (other error)."
  (handler-case (let ((v (funcall thunk)))
                  (cond ((eq v *true*) :tt) ((eq v *false*) :tf) (t :tb)))
    (error () :tr)))
(defun cl-test (thunk)
  (handler-case (if (funcall thunk) :tt :tf) (error () :tr)))
(defun agree (shen cl what)
  (let ((a (shen-test shen)) (b (cl-test cl)))
    (unless (eq a b) (error "contract sample failed: ~A (~S vs ~S)" what a b))))

(defvar *values*
  (list nil t 0 1 -1 1.0 1/2 (expt 2 70) "s" "t" "" #\a *true* *false* (sym "sym")
        (intern "sym" :cl-user) (list 1 2) (list *true*) (vector 1 2) #'identity))
(defvar *numbers* (list 0 1 -1 1.0 1/2 (expt 2 70)))
(defvar *strings* (list "s" "t" ""))
(defvar *symbols* (list nil *true* *false* (sym "sym") (sym "shen.fail!")))

;; pc_cons, pc_string, pc_number: Shen predicate under true? = CL predicate.
(dolist (v *values*)
  (agree (lambda () (f "cons?" v)) (lambda () (consp v)) "cons?/CONSP")
  (agree (lambda () (f "string?" v)) (lambda () (stringp v)) "string?/STRINGP")
  (agree (lambda () (f "number?" v)) (lambda () (numberp v)) "number?/NUMBERP"))
;; pc_absequal, pc_null_*, pc_string_equal, pc_numeric, pc_symbol_eq, pc_fail.
(dolist (a *values*)
  (dolist (b *values*)
    (agree (lambda () (f "shen-cl.equal?" a b)) (lambda () (f "shen-cl.absequal" a b)) "equal?/absequal")))
(dolist (v *values*)
  (agree (lambda () (f "shen-cl.equal?" v nil)) (lambda () (null v)) "equal? NIL/NULL")
  (agree (lambda () (f "shen-cl.equal?" nil v)) (lambda () (null v)) "NIL equal?/NULL")
  (dolist (s *strings*)
    (agree (lambda () (f "shen-cl.equal?" s v)) (lambda () (equal s v)) "string equal?/EQUAL")
    (agree (lambda () (f "shen-cl.equal?" v s)) (lambda () (equal v s)) "equal? string/EQUAL"))
  (dolist (n *numbers*)
    (agree (lambda () (f "shen-cl.equal?" v n)) (lambda () (f "shen-cl.numeric-equal" v n)) "equal? number")
    (agree (lambda () (f "shen-cl.equal?" n v)) (lambda () (f "shen-cl.numeric-equal" v n)) "number equal? swapped"))
  (dolist (d *symbols*)
    (agree (lambda () (f "shen-cl.equal?" v d)) (lambda () (eq v d)) "equal? symbol/EQ")
    (agree (lambda () (f "shen-cl.equal?" d v)) (lambda () (eq v d)) "symbol equal?/EQ swapped")))
;; pc_greater ... pc_less_eq, including errors on non-numbers.
(dolist (a *values*)
  (dolist (b *values*)
    (agree (lambda () (f "shen-cl.greater?" a b)) (lambda () (> a b)) ">")
    (agree (lambda () (f "shen-cl.less?" a b)) (lambda () (< a b)) "<")
    (agree (lambda () (f "shen-cl.greater-than-or-equal-to?" a b)) (lambda () (>= a b)) ">=")
    (agree (lambda () (f "shen-cl.less-than-or-equal-to?" a b)) (lambda () (<= a b)) "<=")))
;; The qsafe premise is necessary: for a quoted cons, Shen equality and EQ differ.
(let ((quoted '(1 2)))
  (assert (eq (f "shen-cl.equal?" (list 1 2) quoted) *true*))
  (assert (null (eq (list 1 2) quoted))))
;; Shen |and| / |or| macros: strict, short-circuit, left to right.
(defmacro events-of (form)
  `(let ((events nil))
     (flet ((ev (tag v) (push tag events) v))
       (declare (ignorable #'ev))
       (let ((r (handler-case ,form (error () :error)))) (list r (reverse events))))))
(flet ((both (x y) (eval `(events-of (,(sym "and") (ev :x ',x) (ev :y ',y)))))
       (either (x y) (eval `(events-of (,(sym "or") (ev :x ',x) (ev :y ',y))))))
  (assert (equal (both *true* *true*) (list *true* '(:x :y))))
  (assert (equal (both *false* 0) (list *false* '(:x))))
  (assert (equal (both 0 *true*) (list :error '(:x))))
  (assert (equal (both *true* 0) (list :error '(:x :y))))
  (assert (equal (either *true* 0) (list *true* '(:x))))
  (assert (equal (either *false* *false*) (list *false* '(:x :y))))
  (assert (equal (either 0 *true*) (list :error '(:x)))))
(format t "CL lowering contracts: native samples passed.~%")
