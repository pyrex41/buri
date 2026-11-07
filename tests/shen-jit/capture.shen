\\ Differential capture for the Shen/JIT bytecode semantics (rocq/JitBytecode.v).
\\ Run by the pinned binary: `shen-jit script tests/shen-jit/capture.shen FILE KIND`.
\\ For each case it prints the code the real lowerer produced and what the real
\\ runtime did with that code. Lowering happens in guest code, as eval-kl does it,
\\ so each case sees the sealing and inlining state left by the earlier ones.
\\ These are samples: agreement on them is test evidence, not proof.
(tc -)
(put shen-jit.bit-or arity 2)
(put shen-jit.bit-and arity 2)
(put shen-jit.shift-right arity 2)
(put shen-jit.pvar? arity 1)
(put shen-jit.pvar-offset arity 1)
(put shen-jit.bytes? arity 1)
(put shen-jit.symbol? arity 1)
(set sj.cap.depth 64)

(define sj.cap.hex-digit N -> (pos "0123456789abcdef" N))
(define sj.cap.hex-from "" -> "" S -> (let B (string->n S)
   (cn (sj.cap.hex-digit (shen-jit.shift-right B 4))
       (cn (sj.cap.hex-digit (shen-jit.bit-and B 15)) (sj.cap.hex-from (tlstr S))))))
(define sj.cap.hex S -> (sj.cap.hex-from S))

(define sj.cap.items V I N D -> "" where (>= I N)
  V I N D -> (cn (sj.cap.ser (<-address V I) D) (cn " " (sj.cap.items V (+ I 1) N D))))
(define sj.cap.vlen V N -> (trap-error (do (<-address V N) (sj.cap.vlen V (+ N 1))) (/. E N)))

\\ The canonical text of a value. JitDiffLib.v computes the same text in Rocq.
\\ D bounds nesting through heads and vector cells, not along a list's tail.
(define sj.cap.fix? X -> (trap-error (do (shen-jit.bit-or X 0) true) (/. E false)))
(define sj.cap.ser
  _ 0 -> "#"
  X D -> (let D1 (- D 1)
    (cond ((number? X) (cn "n" (str X)))
          ((shen-jit.pvar? X) (cn "V" (str (shen-jit.pvar-offset X))))
          ((string? X) (cn "c#34;" (cn (sj.cap.hex X) "c#34;")))
          ((= X true) "T")
          ((= X false) "F")
          ((= X []) "N")
          ((shen-jit.symbol? X) (cn "s" (sj.cap.hex (str X))))
          ((cons? X) (cn "(" (cn (sj.cap.ser (hd X) D1) (cn " " (cn (sj.cap.ser (tl X) D) ")")))))
          ((absvector? X) (cn "[" (cn (sj.cap.items X 0 (sj.cap.vlen X 0) D1) "]")))
          ((shen-jit.bytes? X) "B")
          (true (str X)))))

(define sj.cap.say Tag Text -> (do (pr Tag (stoutput)) (do (pr " " (stoutput)) (do (pr Text (stoutput)) (pr "c#10;" (stoutput))))))
\\ Sealed port functions are named through eval-kl: Shen's compiler would apply
\\ (fn F), and kernel lambda forms do not exist for them. Globals carry the data.
(define sj.cap.lower F -> (do (set sj.cap.f F)
   (trap-error [ok (eval-kl [shen-jit.lower.toplevel [value sj.cap.f] []])] (/. E [bad (error-to-string E)]))))
(define sj.cap.install L -> (do (set sj.cap.l L) (eval-kl [shen-jit.install [value sj.cap.l]])))
(define sj.cap.exec L -> (trap-error
   [ok (if (= (hd L) defun) (sj.cap.install L) (thaw (sj.cap.install L)))]
   (/. E [err (error-to-string E)])))
(define sj.cap.report
  [ok V] -> (sj.cap.say "@ok" (sj.cap.ser V (value sj.cap.depth)))
  [err M] -> (sj.cap.say "@err" (sj.cap.hex M)))
(define sj.cap.case F ->
  (if (not (cons? F)) (sj.cap.say "@atom" (sj.cap.ser F (value sj.cap.depth)))
    (let L (sj.cap.lower F)
      (if (= (hd L) bad) (sj.cap.say "@lowerr" (sj.cap.hex (hd (tl L))))
        (let Code (hd (tl L))
          (do (sj.cap.say "@code" (sj.cap.ser Code 1000000))
              (sj.cap.report (sj.cap.exec Code))))))))
\\ (value E F), (error F), (error Prefix F), a string to skip, or a bare form.
\\ (error _ (shen-jit.save-executable S ())) is skipped too: the named build runs from an executable, so it
\\ saves one and ends the process, and no case after it would run. save-executable is excluded from the claim.
(define sj.cap.kl-form
  [error _ [shen-jit.save-executable S []]] -> [] where (string? S)
  [value _ F] -> [F]
  [error F] -> [F]
  [error _ F] -> [F]
  S -> [] where (string? S)
  F -> [F])
(define sj.cap.run [] -> done
  [[F] | R] -> (do (sj.cap.case F) (sj.cap.run R))
  [[] | R] -> (sj.cap.run R))
\\ Raw s-expressions: the kernel's read-file also rewrites applications, which is
\\ not what eval-kl is given by a KLambda file.
(define sj.cap.kl-file Path -> (sj.cap.run (map (/. X (sj.cap.kl-form X))
   (compile (/. X (shen.<s-exprs> X)) (read-file-as-bytelist Path)))))
\\ The contract file's last form is (Runner Cases 0 0); Cases is a list expression.
(define sj.cap.last [X] -> X [_ | R] -> (sj.cap.last R))
(define sj.cap.contract-file Path ->
  (let Call (sj.cap.last (read-file Path))
       Cases (eval-kl (hd (tl Call)))
    (sj.cap.run (map (/. C [(hd (tl C))]) Cases))))
\\ Globals, for the model's starting store: symbols that are bound to data.
(define sj.cap.global S -> (trap-error (sj.cap.say "@global" (cn (sj.cap.hex (str S)) (cn " " (sj.cap.ser (value S) 12)))) (/. E skip)))
