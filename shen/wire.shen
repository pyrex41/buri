(tc -)
(define buri.wire-byte N Count -> (if (= Count 0) "" (let Local (floor (/ N 2)) (cn (if (= N (* Local 2)) "0" "1") (buri.wire-byte Local (- Count 1))))))
(define buri.wire-string S -> (if (= S "") "0" (let Local (string->n (pos S 0)) (if (and (>= Local 0) (< Local 256)) (cn "1" (cn (buri.wire-byte Local 8) (buri.wire-string (tlstr S)))) (simple-error "Wire atoms require byte strings")))))
(define buri.wire X -> (if (= X []) "00" (if (cons? X) (cn "1" (cn (buri.wire (hd X)) (buri.wire (tl X)))) (if (buri.exact-integer? X) (cn "011" (buri.wire-string (str X))) (if (symbol? X) (cn "010" (buri.wire-string (str X))) (simple-error "Unsupported wire datum"))))))
