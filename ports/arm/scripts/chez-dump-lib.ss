;;; Raw code-object dumper for Chez Scheme 10.3.0 (64-bit).
;;; Layout from the build's own boot/<m>/equates.h (tarm64le and ta6le agree):
;;; code_length_disp 0x9, code_data_disp 0x41, type_typed_object 0x7.
;;; foreign-callable-entry-point returns ($object-address co code-data-disp).
;;; The bytes are the artifact; the compiler's assembly listing is a reading aid.
(define (hex n w)
  (let ([s (number->string n 16)])
    (string-append (make-string (max 0 (- w (string-length s))) #\0) s)))

(define (buri-dump-proc proc form out-prefix)
  (let* ([co (#%$closure-code proc)]
         [_ (lock-object co)]
         [obj-addr (#%$object-address co 0)]
         [data-addr (foreign-callable-entry-point co)]
         [code-len (#%$object-ref 'iptr co 9)])
    (call-with-output-file (string-append out-prefix ".hex")
      (lambda (o)
        (fprintf o "# ~a ~a ~a~%" (scheme-version) (machine-type) (if (threaded?) "threaded" "nonthreaded"))
        (fprintf o "# form ~s~%" form)
        (fprintf o "# code object #x~x data #x~x (disp ~d) length ~d name ~s arity-mask ~s~%"
                 obj-addr data-addr (- data-addr obj-addr) code-len
                 (#%$code-name co) (#%$code-arity-mask co))
        (fprintf o "# dump-time params optimize-level ~s debug-level ~s generate-interrupt-trap ~s~%"
                 (optimize-level) (debug-level) (generate-interrupt-trap))
        (do ([i 0 (+ i 4)]) ((>= i code-len))
          (fprintf o "~a ~a~%" (hex i 4) (hex (foreign-ref 'unsigned-32 data-addr i) 8))))
      'replace)
    (call-with-port (open-file-output-port (string-append out-prefix ".bin")
                                            (file-options no-fail))
      (lambda (o)
        (do ([i 0 (+ i 1)]) ((>= i code-len))
          (put-u8 o (foreign-ref 'unsigned-8 data-addr i)))))
    (call-with-output-file (string-append out-prefix ".relocs")
      (lambda (o)
        (let ([r (((inspect/object co) 'reloc+offset) 'value)])
          (for-each (lambda (x) (fprintf o "~s~%" x))
                    (if (vector? r) (vector->list r) r))))
      'replace)
    code-len))
