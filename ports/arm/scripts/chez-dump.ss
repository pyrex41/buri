;;; Compile the exact Scheme form Shen-Scheme v0.52 emits for
;;;   (define buri-arm-add X Y -> (+ X Y))
;;; i.e. (define (kl:buri-arm-add V3015 V3016) (+ V3015 V3016)), with
;;; Shen-Scheme's observed eval-time parameters (all Chez defaults:
;;; optimize-level 0, debug-level 1, inspector info on, interrupt trap on),
;;; then dump the code object's exact machine-code bytes and relocations.
;;; usage: scheme -q --script chez-dump.ss LIBDIR OUT-PREFIX
(define libdir (cadr (command-line)))
(define out-prefix (caddr (command-line)))
(load (string-append libdir "/chez-dump-lib.ss"))
(define form '(define (kl:buri-arm-add V3015 V3016) (+ V3015 V3016)))
(collect-request-handler void)          ; no GC while we hold raw addresses
(call-with-output-file (string-append out-prefix ".chez-asm")
  (lambda (asm)
    (parameterize ([#%$assembly-output asm])
      (eval form (interaction-environment))))
  'replace)
(define proc (eval 'kl:buri-arm-add (interaction-environment)))
(buri-dump-proc proc form out-prefix)
(printf "~s~%" (list 'add-1-2 (proc 1 2)))
(printf "~s~%" (list 'add-fixnum-overflow (proc (most-positive-fixnum) 1)))
(printf "~s~%" (list 'add-flonum (proc 1.5 2)))
(printf "~s~%" (list 'add-bad (guard (e [#t (condition-message e)]) (proc 'a 1))))
(printf "~s~%" (list 'most-positive-fixnum (most-positive-fixnum)))
