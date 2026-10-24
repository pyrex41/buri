(load "buri.shen")
(load "shen/wire.shen")
(load "shen/export-encoder-kl.shen")
(load "tests/support.shen")
\\ Independent bounded oracle: no division or floor in expected bits.
(define buri.test-half N -> (if (< N 2) 0 (+ 1 (buri.test-half (- N 2)))))
(define buri.test-bits N 0 -> ""
  N Count -> (let H (buri.test-half N)
    (cn (if (= N (* H 2)) "0" "1") (buri.test-bits H (- Count 1)))))
(define buri.test-counts N Count ->
  (and (= (buri.wire-byte N Count) (buri.test-bits N Count))
       (if (= Count 0) true (buri.test-counts N (- Count 1)))))
(define buri.test-bytes 256 -> true
  N -> (do
    (buri.test [byte-contract N]
      [(floor (/ N 2)) (string->n (pos (n->string N) 0))
       (tlstr (n->string N)) (buri.kl-node (n->string N))
       (buri.test-counts N 8)]
      [(buri.test-half N) N "" [text [N]] true])
    (buri.test-bytes (+ N 1))))
(buri.test-bytes 0)
\\ Characterize a known out-of-profile counterexample; do not promote it to
\\ an allowed primitive contract. This pinned host rounds odd large ratios.
(buri.test known-large-half-counterexample
  (= (floor (/ 9007199254740995 2)) 4503599627370497) false)
(buri.test known-large-byte-counterexample
  (= (buri.wire-byte 9007199254740995 8) "11000000") false)
\\ Metadata and executable bindings are separable. Confine this deliberate
\\ metadata substitution to this fresh test image and restore it afterward.
(set buri.saved-wire-source (ps buri.wire))
(put buri.wire shen.source [defun buri.wire [X] "forged"])
(buri.test ps-is-mutable-metadata (ps buri.wire) [defun buri.wire [X] "forged"])
(buri.test ps-does-not-identify-executable (buri.wire []) "00")
(put buri.wire shen.source (value buri.saved-wire-source))
(buri.done)
