\\ Small total helpers on validated finite data. No eval or host callbacks.
(tc -)
(define buri.member? X [] -> false X [Y | Ys] -> (or (= X Y) (buri.member? X Ys)))
(define buri.unique? [] -> true [X | Xs] -> (and (not (buri.member? X Xs)) (buri.unique? Xs)))
(define buri.append [] Ys -> Ys [X | Xs] Ys -> [X | (buri.append Xs Ys)])
(define buri.rev Xs -> (buri.rev-h Xs []))
(define buri.rev-h [] A -> A [X | Xs] A -> (buri.rev-h Xs [X | A]))
(define buri.get K [] -> missing K [[J V] | Xs] -> (if (= K J) [found V] (buri.get K Xs)))
(define buri.keys [] -> [] [[K _] | Xs] -> [K | (buri.keys Xs)])
(define buri.remove K [] -> [] K [[J V] | Xs] -> (if (= K J) Xs [[J V] | (buri.remove K Xs)]))
(define buri.nat? N -> (and (>= N 0) (buri.exact-integer? N)) where (number? N) _ -> false)
(define buri.index N [] -> missing 0 [X | _] -> [found X] N [_ | Xs] -> (buri.index (- N 1) Xs))
(define buri.every-list? [] -> true [_ | T] -> (buri.every-list? T) _ -> false)
(define buri.all-symbols? [] -> true [X | Xs] -> (and (symbol? X) (buri.all-symbols? Xs)) _ -> false)
(define buri.check Condition Message -> (if Condition true (simple-error Message)))

\\ The supported host profile requires decimal integer printing. Inexact
\\ integral floats (1.0) are deliberately excluded, not promoted to exact ints.
(define buri.exact-integer? X -> (buri.integer-spelling? (str X)) where (number? X) _ -> false)
(define buri.integer-spelling? "" -> false
  S -> (buri.unsigned-spelling? (tlstr S)) where (= (pos S 0) "-")
  S -> (buri.unsigned-spelling? S))
(define buri.unsigned-spelling? "" -> false S -> (buri.digits? S))
(define buri.digits? "" -> true
  S -> (and (buri.member? (pos S 0) ["0" "1" "2" "3" "4" "5" "6" "7" "8" "9"])
            (buri.digits? (tlstr S))))
