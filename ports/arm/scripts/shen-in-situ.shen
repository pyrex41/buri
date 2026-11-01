\\ Define the function inside a real Shen-Scheme v0.52 process and dump the
\\ code object that process produced.  Host-only (ta6le): no aarch64
\\ Shen-Scheme process exists in this experiment.
(define buri-arm-add X Y -> (+ X Y))
(define buri-scm Code -> ((foreign scm.eval) ((foreign scm.read) ((foreign scm.open-input-string) Code))))
(buri-scm "(load c#34;chez-dump-lib.ssc#34;)")
(buri-scm "(collect-request-handler void)")
(print (buri-scm "(buri-dump-proc kl:buri-arm-add '(define (kl:buri-arm-add V3015 V3016) (+ V3015 V3016)) c#34;shen-scheme-ta6le-buri-arm-addc#34;)"))
