(load "buri.shen")
(load "shen/observation.shen")
(load "tests/support.shen")
\\ Ground checks of the Shen observation vocabulary (E2E-04). Sampled data only.
(set buri.obs-fail [io [write 1 [65 66]] [failed no-space]])
(set buri.obs-short [io [write 1 [65 66]] [wrote 1]])
(set buri.obs-ok [io [write 1 [65]] [wrote 1]])
(buri.test failed-write-is-observable (buri.obs-write-failed? (value buri.obs-fail)) true)
(buri.test partial-write-is-observable (buri.obs-write-failed? (value buri.obs-short)) true)
(buri.test full-write-not-failed (buri.obs-write-failed? (value buri.obs-ok)) false)
(buri.test partial-read-event (buri.obs-event? [io [read 0 8] [read [1 2 3]]]) true)
(buri.test signal-event (buri.obs-event? [signal int]) true)
(buri.test bad-byte-rejected (buri.obs-event? [io [write 1 [256]] [wrote 1]]) false)
(buri.test exhausted-not-behavior (buri.obs-behavior? [exhausted []]) false)
(buri.test exhausted-is-verdict (buri.obs-verdict? [exhausted []]) true)
(buri.test unknown-distinct (buri.obs-behavior? unknown) false)
(buri.test refl (buri.obs-refines? [terminates [(value buri.obs-ok)] [normal 3]]
                                   [terminates [(value buri.obs-ok)] [normal 3]]) true)
(buri.test cannot-hide-error (buri.obs-refines? [terminates [] [normal 3]] [terminates [] [error boom]]) false)
(buri.test cannot-invent-error (buri.obs-refines? [terminates [] [error boom]] [terminates [] [normal 3]]) false)
(buri.test cannot-drop-failed-write
 (buri.obs-refines-res? [terminates [] [normal 0]] [terminates [(value buri.obs-fail)] [normal 0]]) false)
(buri.test cannot-hide-loop (buri.obs-refines-res? [diverges []] [terminates [] [normal 0]]) false)
(buri.test loop-not-termination (buri.obs-refines-res? [terminates [] [normal 0]] [diverges []]) false)
(buri.test resource-stop-at-prefix
 (buri.obs-refines-res? [terminates [(value buri.obs-ok)] [resource heap]]
                        [terminates [(value buri.obs-ok) (value buri.obs-fail)] [normal 0]]) true)
(buri.test resource-stop-not-prefix
 (buri.obs-refines-res? [terminates [(value buri.obs-fail)] [resource stack]]
                        [terminates [(value buri.obs-ok)] [normal 0]]) false)
(buri.test strict-has-no-resource-stop
 (buri.obs-refines? [terminates [] [resource heap]] [terminates [] [normal 0]]) false)
(buri.test wrong-only-wrong (buri.obs-refines-res? [goes-wrong []] [terminates [] [normal 0]]) false)
(buri.done)
