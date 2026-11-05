# Spike 3: Búri's KLambda semantics under Rocq 9

Result: **passed.** Búri's KLambda semantics compiles under the Rocq that Theorem's model
needs, with no change other than one import line per file. Both can be used in one Rocq
session. This keeps a single copy of the spec, so the planned `rocq-jit/` fork isn't needed
for these files. It proves nothing new about Shen/JIT.

Evidence kind: Rocq compilation and `rocqchk` replay under Rocq 9.3.0.

| Check | Result |
|---|---|
| Files compiled | 10 of 10: `Lambda`, `Observation`, `KLSyntax`, `KLValue`, `KLSemantics`, `KLMetatheory`, `KLWellFormed`, `KLTail`, `KLBridge`, `KLExamples` |
| Difference from `rocq/` | 1 line per file: `From Coq Require` becomes `From Stdlib Require` |
| Drift gate | `port.sh` exits 2 on any other difference; tested by adding a rewrite to `rewrites.sed` |
| `rocqchk` on all 10 | exit 0 |
| `Print Assumptions` on `refinement_preserves_errors_res`, `terminates_unique`, `progress`, `step_deterministic` | Closed under the global context |
| Linked with Theorem's model and the spike 1 proof | exit 0, using `Observation.refines_res`, `KLSemantics.step`, `source_wexit`, `omni_strong_universal` |
| Deprecation warnings | 26, including 13 for `app_length`, so a later Rocq could remove these |

## Limits

- Only these 10 files were ported, not the rest of Búri's 179 Rocq files. Búri's main gates
  stay on Coq 8.18, so the two copies are compiled by different provers.
- Linking means the definitions can be stated together. No theorem connects KLambda
  behavior to process behavior yet.
- `port.sh` compares text, not the compiled statements. The compared difference is an import
  line, but the same source could still mean something different if the new standard library's
  definitions changed. I didn't check that beyond `KLExamples` and the proofs compiling.

## Pins

Rocq 9.3.0, OCaml 5.2.1, Theorem's model at `5e13f6b0f82936aa5d006438e07e265c5d9fcfc4`.

## Reproduce

In the container from `spikes/jit-in-model/setup.sh`, after building spike 1's example:
`bash spikes/rocq9-port/port.sh`.
