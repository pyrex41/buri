;;; E2E-22 intermediate-representation capture (orchestration only).
;;;
;;; Compile the exact Scheme form Shen-Scheme v0.52 emits for
;;;   (define buri-arm-add X Y -> (+ X Y))
;;; with the parameters a running Shen-Scheme v0.52 reports (all Chez
;;; defaults), through the real Chez 10.3.0 `eval` (current-eval = compile),
;;; and write Chez's own unparsed output of every traced nanopass pass.
;;;
;;; The front end (expand, cpvalid, cp0, cptypes, cpletrec, cpcheck,
;;; cpcommonize) has no tracer; it is replayed with the same internal entry
;;; points and the same composition as compile.ss `compile` (default run-cp0
;;; runs the cp0/cptypes/cpletrec triple twice), each output printed with
;;; Chez's own $uncprep.  The replay's final output is printed next to the
;;; real pipeline's expand/optimize-output so the two can be compared.
;;;
;;; Nothing here decides validity: it only records what the compiler printed.
;;; usage: scheme -q --script np-dump.ss OUT-FILE
(define out-file (cadr (command-line)))
(define form '(define (kl:buri-arm-add V3015 V3016) (+ V3015 V3016)))
(define env (interaction-environment))
(print-gensym 'pretty/suffix)
(print-graph #t)
;; Chez prints every np-languages `info` record (and its subtypes) as the
;; opaque "#<info>".  Replace only that writer by one that prints the record
;; type name and every field, so the dumps keep the information the unparsers
;; would otherwise hide.  This changes printing only, never compilation.
(define info-rtd (#%$sgetprop '#{info n93q6qho9id46fha8itaytldd-5} '*rtd* #f))
(unless (record-type-descriptor? info-rtd) (errorf 'np-dump "info rtd not found"))
(define (all-fields rtd)
  (if rtd
      (append (all-fields (record-type-parent rtd))
              (let ([names (vector->list (record-type-field-names rtd))])
                (let loop ([i 0] [names names])
                  (if (null? names)
                      '()
                      (cons (cons (car names) (record-accessor rtd i))
                            (loop (+ i 1) (cdr names)))))))
      '()))
(record-writer info-rtd
  (lambda (x p wr)
    (display "#[info:" p)
    (display (record-type-name (record-rtd x)) p)
    (for-each
      (lambda (f)
        (display " " p)
        (display (car f) p)
        (display "=" p)
        (wr ((cdr f) x) p))
      (all-fields (record-rtd x)))
    (display "]" p)))
(define op (open-output-file out-file 'replace))
(define (section name thunk)
  (fprintf op "@@@ ~a~%" name)
  (thunk)
  (fprintf op "@@@ end~%"))
(define (show x) (parameterize ([print-graph #t]) (pretty-print x op)))
(section "parameters"
  (lambda ()
    (show `((scheme-version ,(scheme-version))
            (machine-type ,(machine-type))
            (threaded ,(threaded?))
            (optimize-level ,(optimize-level))
            (debug-level ,(debug-level))
            (generate-inspector-information ,(generate-inspector-information))
            (generate-procedure-source-information ,(generate-procedure-source-information))
            (enable-type-recovery ,(enable-type-recovery))
            (generate-interrupt-trap ,(generate-interrupt-trap))
            (compile-interpret-simple ,(compile-interpret-simple))
            (enable-unsafe-application ,(enable-unsafe-application))
            (enable-unsafe-variable-reference ,(enable-unsafe-variable-reference))
            (enable-arithmetic-left-associative ,(enable-arithmetic-left-associative))
            (commonization-level ,(commonization-level))
            (compile-profile ,(compile-profile))
            (generate-profile-forms ,(generate-profile-forms))
            (lift-closures ,(#%$lift-closures))
            (optimize-closures ,(#%$optimize-closures))
            (loop-unroll-limit ,(#%$loop-unroll-limit))
            (enable-check-prelex-flags ,(#%$enable-check-prelex-flags))
            (current-eval-is-compile ,(eq? (current-eval) compile))))))
(section "source" (lambda () (show form)))
;; Front-end replay (compile.ss `compile`, lines 1797-1817).
(define (front)
  (let* ([x1 (sc-expand form env #t)]
         [_ (section "expand" (lambda () (show (#%$uncprep x1))))]
         [x2 (#%$cpvalid x1)]
         [_ (section "cpvalid" (lambda () (show (#%$uncprep x2))))]
         [round 0]
         [x2a ((run-cp0)
               (lambda (x)
                 (set! round (+ round 1))
                 (let* ([x (#%$cp0 x)]
                        [_ (section (format "cp0#~a" round) (lambda () (show (#%$uncprep x))))]
                        [x (if (enable-type-recovery) (#%$cptypes x) x)]
                        [_ (section (format "cptypes#~a" round) (lambda () (show (#%$uncprep x))))]
                        [x (#%$cpletrec x)]
                        [_ (section (format "cpletrec#~a" round) (lambda () (show (#%$uncprep x))))])
                   x))
               x2)]
         [x2b (#%$cpcheck x2a)]
         [_ (section "cpcheck" (lambda () (show (#%$uncprep x2b))))]
         [x2b (#%$cpcommonize x2b)])
    (section "cpcommonize" (lambda () (show (#%$uncprep x2b))))))
(front)
;; The real pipeline, with every nanopass pass traced.
(define (backend)
  (let ([trace (open-output-string)] [eo (open-output-string)])
    (#%$np-tracer #t)
    (parameterize ([current-error-port trace] [expand/optimize-output eo])
      (eval form env))
    (#%$np-tracer #f)
    (section "expand/optimize-output" (lambda () (display (get-output-string eo) op)))
    (section "np-trace" (lambda () (display (get-output-string trace) op)))))
(backend)
(close-port op)
(printf "BURI_NP_DUMP_OK ~a~%" (machine-type))
