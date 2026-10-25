\\ Controlled load path. Compile once, evaluate that exact target value,
\\ record only completed installations. No ps or metadata reads.
(tc -)
(define buri.install-observed
 [defun Name Args Body] ->
 (let Arity (shen.store-arity Name (length Args))
      Form [defun Name Args Body]
      Target (_scm.kl->scheme Form)
      Result ((foreign scm.eval) Target)
      Record (set buri.observed [[Form Target] | (value buri.observed)])
   Name)
 _ -> (simple-error "Observed loader requires a defun"))
(define buri.observe-forms
 [[tc -] A B C] -> (do (buri.install-observed (shen.shen->kl-h A))
                     (buri.install-observed (shen.shen->kl-h B))
                     (buri.install-observed (shen.shen->kl-h C)))
 _ -> (simple-error "Observed loader requires tc- and three definitions"))
(define buri.observe-encoder Path Bits Transcript ->
 (let Mode (set _scm.*native-mode* compatible)
      Locals (set _scm.*native-local-map* [])
      Reset (set buri.observed [])
      Source (read-file-as-string Path)
      Input (set buri.observed-source Source)
      Loaded (buri.observe-forms (read-from-string Source))
      Records (reverse (value buri.observed))
      Data [buri-observed-encoder-1 (buri.kl-node Records)]
   (do (buri.checked-write (cn Bits ".source") Source)
       (buri.checked-write Bits (buri.wire Data))
       (buri.checked-write Transcript (make-string "~S~%" Records)))))

\\ Verify actual persisted text; write-to-file alone may be suppressed by *hush*.
(define buri.checked-write Path Text ->
 (let Written (write-to-file Path Text)
      Actual (read-file-as-string Path)
   (if (= Actual Text) Text
       (simple-error "Snapshot write verification failed"))))
