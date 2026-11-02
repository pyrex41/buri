;; Prints named sb-vm constants of the running SBCL image, one per line:
;;   NAME VALUE
;; Inert: reads constants, evaluates nothing from input.
(defun show (sym)
  (let ((s (find-symbol (string sym) "SB-VM")))
    (if (and s (boundp s))
        (format t "~a ~d~%" (string-downcase (symbol-name s)) (symbol-value s))
        (format t "~a MISSING~%" (string-downcase (string sym))))))
(format t "lisp-implementation-version ~a~%" (lisp-implementation-version))
(format t "machine-type ~a~%" (machine-type))
(format t "feature-sb-unicode ~a~%" (if (member :sb-unicode *features*) 1 0))
(format t "feature-sb-thread ~a~%" (if (member :sb-thread *features*) 1 0))
(format t "feature-64-bit ~a~%" (if (member :64-bit *features*) 1 0))
(format t "feature-compact-instance-header ~a~%" (if (member :compact-instance-header *features*) 1 0))
(format t "features~{ ~(~a~)~}~%" (sort (mapcar (function symbol-name) *features*) (function string<)))
(let ((s (find-symbol "+INTERNAL-FEATURES+" "SB-IMPL")))
  (format t "internal-features~{ ~(~a~)~}~%" (if (and s (boundp s)) (sort (mapcar (function symbol-name) (copy-list (symbol-value s))) (function string<)) (list "MISSING"))))
(format t "char-code-limit ~d~%" char-code-limit)
(format t "most-positive-fixnum ~d~%" most-positive-fixnum)
(format t "most-negative-fixnum ~d~%" most-negative-fixnum)
(dolist (c '(n-word-bits n-word-bytes word-shift n-lowtag-bits lowtag-mask n-fixnum-tag-bits
             fixnum-tag-mask n-fixnum-bits n-widetag-bits widetag-mask n-byte-bits
             even-fixnum-lowtag odd-fixnum-lowtag instance-pointer-lowtag list-pointer-lowtag
             fun-pointer-lowtag other-pointer-lowtag other-immediate-0-lowtag
             other-immediate-1-lowtag other-immediate-2-lowtag other-immediate-3-lowtag
             bignum-widetag ratio-widetag single-float-widetag double-float-widetag
             complex-widetag character-widetag symbol-widetag instance-widetag
             funcallable-instance-widetag simple-fun-widetag closure-widetag
             code-header-widetag unbound-marker-widetag no-tls-value-marker
             simple-vector-widetag simple-base-string-widetag simple-character-string-widetag
             simple-array-widetag complex-character-string-widetag
             nil-value t-value
             cons-car-slot cons-cdr-slot cons-size
             symbol-value-slot symbol-hash-slot symbol-info-slot symbol-name-slot
             symbol-fdefn-slot symbol-size
             vector-length-slot vector-data-offset
             bignum-digits-offset n-bignum-bits
             double-float-value-slot double-float-size
             closure-fun-slot closure-info-offset
             simple-fun-insts-offset
             null-offset cfp-offset csp-offset nsp-offset thread-offset lexenv-offset
             nargs-offset nfp-offset ocfp-offset lr-offset code-offset cardtable-offset
             tmp-offset r0-offset r1-offset r2-offset r3-offset))
  (show c))
