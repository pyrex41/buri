\\ E2E-04 observation vocabulary: the executable Shen counterpart of
\\ rocq/Observation.v. Behaviors, outcomes, events and verdicts are inert data.
\\ The refinement checks below decide ground (finite, concrete) instances only;
\\ the universal refinement lemmas are in Rocq. No correspondence proof between
\\ this file and Observation.v exists yet (E2E-07 obligation).
(tc -)
(define buri.obs-handle? H -> (buri.nat? H))
(define buri.obs-byte? B -> (and (buri.nat? B) (< B 256)))
(define buri.obs-bytes? [] -> true [B | Bs] -> (and (buri.obs-byte? B) (buri.obs-bytes? Bs)) _ -> false)
(define buri.obs-io-error? [other C] -> (buri.nat? C)
  E -> (buri.member? E [no-entity permission bad-handle no-space closed short-write protocol]))
(define buri.obs-request?
  [open Path Dir] -> (and (string? Path) (buri.member? Dir [in out]))
  [close H] -> (buri.obs-handle? H)
  [read H Max] -> (and (buri.obs-handle? H) (buri.nat? Max))
  [write H Bytes] -> (and (buri.obs-handle? H) (buri.obs-bytes? Bytes))
  [time Clock] -> (symbol? Clock)
  [random Bound] -> (buri.nat? Bound)
  _ -> false)
(define buri.obs-response?
  [opened H] -> (buri.obs-handle? H)
  closed -> true
  [read Bytes] -> (buri.obs-bytes? Bytes)
  eof -> true
  [wrote N] -> (buri.nat? N)
  [failed E] -> (buri.obs-io-error? E)
  [time T] -> (buri.exact-integer? T)
  [random N] -> (buri.nat? N)
  _ -> false)
(define buri.obs-signal? [other N] -> (buri.nat? N) S -> (buri.member? S [int term kill hup]))
(define buri.obs-event?
  [io Q R] -> (and (buri.obs-request? Q) (buri.obs-response? R))
  [signal S] -> (buri.obs-signal? S)
  cancel -> true
  _ -> false)
(define buri.obs-trace? [] -> true [E | Es] -> (and (buri.obs-event? E) (buri.obs-trace? Es)) _ -> false)
(define buri.obs-outcome?
  [normal _] -> true
  [error _] -> true
  [resource R] -> (buri.member? R [heap stack])
  [exit C] -> (buri.exact-integer? C)
  [killed S] -> (buri.obs-signal? S)
  cancelled -> true
  _ -> false)
\\ Finite behaviors. Reactive (infinitely observable) behaviors have no finite
\\ representation here; they exist only in the Rocq vocabulary.
(define buri.obs-behavior?
  [terminates T O] -> (and (buri.obs-trace? T) (buri.obs-outcome? O))
  [diverges T] -> (buri.obs-trace? T)
  [goes-wrong T] -> (buri.obs-trace? T)
  _ -> false)
\\ Evaluator verdicts are not program behaviors. Exhaustion is distinct from
\\ unknown, unsupported and rejected, and it never denotes divergence.
(define buri.obs-verdict?
  [done T O] -> (and (buri.obs-trace? T) (buri.obs-outcome? O))
  [wrong T] -> (buri.obs-trace? T)
  [exhausted T] -> (buri.obs-trace? T)
  unknown -> true unsupported -> true rejected -> true
  _ -> false)
(define buri.obs-write-failed?
  [io [write _ _] [failed _]] -> true
  [io [write _ Bytes] [wrote N]] -> (< N (length Bytes))
  _ -> false)
(define buri.obs-prefix? [] _ -> true [E | Es] [E | Fs] -> (buri.obs-prefix? Es Fs) _ _ -> false)
(define buri.obs-trace-of
  [terminates T _] -> T [diverges T] -> T [goes-wrong T] -> T)
\\ Strict refinement of ground behaviors, with equality as the value and error
\\ payload relation: identical traces and the same outcome constructor.
(define buri.obs-refines? Target Source ->
  (and (buri.obs-behavior? Target) (and (buri.obs-behavior? Source) (buri.obs-refines-h? Target Source))))
(define buri.obs-refines-h?
  [terminates T O] [terminates T O] -> true
  [diverges T] [diverges T] -> true
  [goes-wrong T] [goes-wrong T] -> true
  _ _ -> false)
\\ Resource-relaxed refinement: additionally, a target may stop with a named
\\ resource failure after a prefix of the source trace.
(define buri.obs-refines-res? Target Source ->
  (and (buri.obs-behavior? Target) (and (buri.obs-behavior? Source)
    (or (buri.obs-refines-h? Target Source) (buri.obs-resource-stop? Target Source)))))
(define buri.obs-resource-stop?
  [terminates T [resource _]] Source -> (buri.obs-prefix? T (buri.obs-trace-of Source))
  _ _ -> false)
