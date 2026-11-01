;;; Conservative static reachability over SBCL code-component boxed constants
;;; (fdefns, functions, code) from SHEN::|buri-arm-add|, plus the static
;;; function and assembly routine the disassembly names (TWO-ARG-+ via the
;;; static-fdefn table, ALLOC-TRAMP).  Data for E2E-24/25; it does not follow
;;; data-held closures, CLOS dispatch, or C runtime callees, and is not a proof
;;; of closure.
(in-package :cl-user)
(defun buri-code-of (x)
  (typecase x
    (sb-kernel:code-component x)
    (sb-kernel:fdefn (let ((f (sb-kernel:fdefn-fun x))) (and f (buri-code-of f))))
    (sb-kernel:closure (buri-code-of (sb-kernel:%closure-fun x)))
    (sb-kernel:simple-fun (sb-kernel:fun-code-header x))
    (function (ignore-errors (sb-kernel:fun-code-header (sb-kernel:%fun-fun x))))
    (t nil)))
(defun buri-code-name (c)
  (if (plusp (sb-kernel:code-n-entries c))
      (sb-kernel:%simple-fun-name (sb-kernel:%code-entry-point c 0))
      (sb-kernel:%code-debug-info c)))
(defun buri-closure (root-name extra-names out &key (max-depth 64))
  (let ((seen (make-hash-table :test 'eq)) (queue nil) (rows nil))
    (flet ((push-code (c d) (when (and c (not (gethash c seen)) (<= d max-depth))
                              (setf (gethash c seen) d)
                              (setf queue (append queue (list (cons c d)))))))
      (push-code (buri-code-of (fdefinition root-name)) 0)
      (dolist (n extra-names) (push-code (buri-code-of (fdefinition n)) 1))
      (loop while queue do
        (destructuring-bind (c . d) (pop queue)
          (push (list d (buri-code-name c) (sb-kernel:%code-text-size c)) rows)
          (loop for i from sb-vm:code-constants-offset below (sb-kernel:code-header-words c)
                do (push-code (buri-code-of (sb-kernel:code-header-ref c i)) (1+ d))))))
    (setf rows (nreverse rows))
    (with-open-file (o out :direction :output :if-exists :supersede)
      (format o "# sbcl ~a ~a: code components reachable from ~s via boxed constants~%"
              (lisp-implementation-version) (machine-type) root-name)
      (format o "# extra seeds (from disassembly notes): ~s~%" extra-names)
      (format o "# count ~d total-text-bytes ~d~%" (length rows) (reduce #'+ rows :key #'third))
      (loop for d from 0 to max-depth
            for at = (remove d rows :key #'first :test-not #'=)
            while at
            do (format o "# depth ~d: ~d components, ~d bytes~%" d (length at) (reduce #'+ at :key #'third)))
      (dolist (r rows) (when (<= (first r) 2) (format o "~d ~s ~d~%" (first r) (second r) (third r)))))
    (length rows)))
