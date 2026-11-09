\\ For tests/shen-jit/capture_passes.shen in place of build/tools/lower.shen: the
\\ entry points it calls, mapped to the lowerer sealed in the running Shen/JIT image
\\ (shen-jit.lower.*), to measure how far that lowerer reproduces stage 0. Not
\\ used for witnesses: in the image, shen-jit.sealed? and shen-jit.inline-body
\\ are primitives over the image's own sealing, which leaves the six extension
\\ files open, where stage 0 sealed every input (src/runtime/main.c,
\\ src/lowerer/host.shen).
\\ Sealed port functions are named through eval-kl, as tests/shen-jit/capture.shen
\\ does: Shen's compiler would apply (fn F), and no lambda form exists for them.
\\ The arguments go through globals.
(define pc.image-call
  F Args -> (do (set pc.image-args Args)
                (eval-kl [F | (pc.image-refs Args 0)])))
(define pc.image-refs
  [] _ -> []
  [_ | As] N -> [[pc.image-nth N [value pc.image-args]] | (pc.image-refs As (+ N 1))])
(define pc.image-nth
  0 L -> (hd L)
  N L -> (pc.image-nth (- N 1) (tl L)))
\\ check-defun is called first, so the image's own globals are reset here, as
\\ shen-jit.lower.defun does.
(define stage0.lower.check-defun
  F Params Sealed -> (do (pc.image-call shen-jit.lower.check-defun [F Params Sealed])
                         (set shen-jit.lower.*inline-depth* 0)
                         (set shen-jit.lower.*fresh* 0)))
(define stage0.lower.share X -> (pc.image-call shen-jit.lower.share [X]))
(define stage0.lower.norm Params X -> (pc.image-call shen-jit.lower.norm [Params X]))
(define stage0.lower.code F Params N Sealed -> (pc.image-call shen-jit.lower.code [F Params N Sealed]))
(define stage0.lower.inline-form F Params Body -> (pc.image-call shen-jit.lower.inline-form [F Params Body]))
