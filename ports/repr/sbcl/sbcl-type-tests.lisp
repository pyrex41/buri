;; E2E-21 capture: the arm64 code the pinned SBCL 2.6.8 image emits for the
;; host operations named in CLContracts.cl_host_ops, each compiled as a
;; one-operation function of untyped arguments under the default policy.
;; Inert: compiles only the literal forms below and prints, per case, the
;; disassembly (comments for humans) and the raw 32-bit instruction words
;; read from the code object, from the simple-fun entry to the end of text.
;; Output lines:
;;   case NAME
;;   form TEXT
;;   entry-offset N      (byte offset of the entry instruction in the text)
;;   words W0 W1 ...     (little-endian 32-bit instruction words, decimal)
;;   end
(defun dump-case (name form)
  (let* ((f (let ((*load-truename* nil) (*load-pathname* nil)) (compile nil form)))
         (code (sb-kernel:fun-code-header f))
         (base (sb-sys:sap-int (sb-kernel:code-instructions code)))
         (entry (+ (- (sb-kernel:get-lisp-obj-address f) sb-vm:fun-pointer-lowtag)
                   (* sb-vm:n-word-bytes sb-vm:simple-fun-insts-offset)))
         (size (sb-kernel:%code-text-size code))
         (sap (sb-kernel:code-instructions code)))
    (format t "case ~a~%" name)
    (format t "form ~s~%" form)
    (format t "entry-offset ~d~%" (- entry base))
    (format t "words")
    (loop for off from (- entry base) below size by 4
          do (format t " ~d" (sb-sys:sap-ref-32 sap off)))
    (format t "~%")
    (let ((text (with-output-to-string (s)
                  (sb-disassem:disassemble-code-component f :stream s))))
      (with-input-from-string (in text)
        (loop for line = (read-line in nil) while line
              do (format t "; ~a~%" line))))
    (format t "end~%")))
(format t "lisp-implementation-version ~a~%" (lisp-implementation-version))
(format t "machine-type ~a~%" (machine-type))
(format t "nil-value ~d~%" sb-vm:nil-value)
(format t "t-address ~d~%" (sb-kernel:get-lisp-obj-address t))
(dump-case "eq" '(lambda (x y) (eq x y)))
(dump-case "typep-fixnum" '(lambda (x) (typep x 'fixnum)))
(dump-case "integerp" '(lambda (x) (integerp x)))
(dump-case "numberp" '(lambda (x) (numberp x)))
(dump-case "consp" '(lambda (x) (consp x)))
(dump-case "stringp" '(lambda (x) (stringp x)))
(dump-case "arrayp" '(lambda (x) (arrayp x)))
(dump-case "symbolp" '(lambda (x) (symbolp x)))
(dump-case "not" '(lambda (x) (not x)))
(dump-case "null" '(lambda (x) (null x)))
(dump-case "string=" '(lambda (x y) (string= x y)))
(dump-case "equal" '(lambda (x y) (equal x y)))
(dump-case "eql" '(lambda (x y) (eql x y)))
(dump-case "num-eq" '(lambda (x y) (= x y)))
