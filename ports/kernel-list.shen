\\ Exact list helpers from Shen kernel 43.1 sources/sys.shen
\\ (ShenOSKernel-43.1.tar.gz, sha256 900eedef44f440af78f9395ed06e689ce1604546fc309f5bc7c8bc84cc651920,
\\ pinned by the tizoc/shen-scheme Makefile; sys.shen blob 92aab80f04afe0b91a8f37eb835c245441b7ef09).
\\ Copyright (c) 2010-2022 Mark Tarver. BSD-3-Clause; see LICENSES/Shen-Kernel.txt.
\\ Only defined names and their self-references are prefixed with buri.kernel.
\\ so that capture does not redefine the running kernel; bodies are unchanged.
(tc -)
(define buri.kernel.occurrences
  X X -> 1
  X [Y | Z] -> (+ (buri.kernel.occurrences X Y) (buri.kernel.occurrences X Z))
  _ _ -> 0)

(define buri.kernel.reverse
  X -> (buri.kernel.reverse-help X []))

(define buri.kernel.reverse-help
  [] R -> R
  [X | Y] R -> (buri.kernel.reverse-help Y [X | R])
  _ _ -> (error "attempt to reverse a non-list~%"))

(define buri.kernel.not
  X -> (if X false true))
