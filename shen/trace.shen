\\ Ground replay evidence is NOT a universal theorem or port refinement.
(tc -)
(define buri.replay D E Claimed Budget ->
  (buri.replay-result D E Claimed (buri.evaluate D E Budget)))
(define buri.replay-result D E R [unknown Why] -> [unknown Why]
  _ _ _ [unsupported Why] -> [unsupported Why]
  _ _ _ [rejected Why] -> [rejected Why]
  D E R Actual -> (if (= R Actual)
    [accepted ground-replay [buri-kl-pure-1 D E R]]
    [counterexample claimed R actual Actual]))
