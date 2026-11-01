;;; Conservative static code-object reachability from kl:buri-arm-add through
;;; relocation tables (Chez 10.3.0).  Data for E2E-24/25 dependency closure; it
;;; is an over-approximation of code reachable by direct relocation only.  It
;;; does not follow closures stored in data, top-level-value lookups, or C
;;; entry points called through foreign-procedure stubs, and is NOT a proof
;;; that nothing else is reachable.
;;; usage: scheme -q --script chez-closure.ss OUT
(define out (cadr (command-line)))
(define form '(define (kl:buri-arm-add V3015 V3016) (+ V3015 V3016)))
(eval form (interaction-environment))
(define root (#%$closure-code (eval 'kl:buri-arm-add (interaction-environment))))

(define seen (make-eq-hashtable))
(define order '())
(define (code-bytes co) (#%$object-ref 'iptr co 9))
(define (relocs co)
  (let ([r (((inspect/object co) 'reloc) 'value)])
    (if (vector? r) (vector->list r) r)))
(define (visit! co depth)
  (unless (hashtable-contains? seen co)
    (hashtable-set! seen co depth)
    (set! order (cons (cons co depth) order))
    (for-each (lambda (x)
                (cond [(#%$code? x) (visit! x (+ depth 1))]
                      [(and (procedure? x) (#%$code? (#%$closure-code x)))
                       (visit! (#%$closure-code x) (+ depth 1))]
                      ;; symbol referenced by the code: follow its global
                      ;; procedure value (call through the symbol's value slot)
                      [(and (symbol? x) (top-level-bound? x)
                            (procedure? (top-level-value x)))
                       (visit! (#%$closure-code (top-level-value x)) (+ depth 1))]))
              (relocs co))))
(visit! root 0)
(define nodes (reverse order))
(call-with-output-file out
  (lambda (o)
    (fprintf o "# ~a ~a: code objects reachable from kl:buri-arm-add via relocations~%"
             (scheme-version) (machine-type))
    (fprintf o "# count ~d total-instruction-bytes ~d~%" (length nodes)
             (apply + (map (lambda (p) (code-bytes (car p))) nodes)))
    (let loop ([d 0])
      (let ([at (filter (lambda (p) (= (cdr p) d)) nodes)])
        (unless (null? at)
          (fprintf o "# depth ~d: ~d objects, ~d bytes~%" d (length at)
                   (apply + (map (lambda (p) (code-bytes (car p))) at)))
          (loop (+ d 1)))))
    (for-each (lambda (p)
                (when (<= (cdr p) 1)
                  (fprintf o "#   relocs of ~s: ~s~%" (#%$code-name (car p))
                           (map (lambda (x) (cond [(#%$code? x) (list 'code (#%$code-name x))]
                                                  [(symbol? x) (list 'symbol x)]
                                                  [else (list 'other (if (procedure? x) 'procedure x))]))
                                (relocs (car p))))))
              nodes)
    (for-each (lambda (p)
                (when (<= (cdr p) 2)
                  (fprintf o "~d ~s ~d~%" (cdr p) (#%$code-name (car p)) (code-bytes (car p)))))
              nodes))
  'replace)
