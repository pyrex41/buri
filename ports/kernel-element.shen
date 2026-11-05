\\ Exact element? from Shen kernel 43.1 sources/sys.shen
\\ (ShenOSKernel-43.1.tar.gz, sha256 900eedef44f440af78f9395ed06e689ce1604546fc309f5bc7c8bc84cc651920,
\\ pinned by the tizoc/shen-scheme Makefile; sys.shen blob 92aab80f04afe0b91a8f37eb835c245441b7ef09).
\\ Copyright (c) 2010-2022 Mark Tarver. BSD-3-Clause; see LICENSES/Shen-Kernel.txt.
\\ Only the defined name and its self-reference are prefixed with buri.kernel.
\\ so that capture does not redefine the running kernel; the body is unchanged.
(tc -)
(define buri.kernel.element?
  _ [] -> false
  X [X | _] -> true
  X [_ | Z] -> (buri.kernel.element? X Z)
  _ _ -> (error "attempt to find an element in a non-list~%"))
