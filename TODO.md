# TODO: the next workflow (Shen/JIT Phase 2, round 3)

Phase 2 is done when the pipeline judge reports "N of 955 kernel definitions validated", every rewrite family has a
checker with closed soundness, and no more than 20 residuals remain outside Reuben's decisions. Rough remaining
effort: 2 to 4 weeks. Round 3 is the first step; the eval-kl and Prolog-cluster models are the main schedule risk.

Starting point: `p2/int` at the merge of `p2/r21-sms-fresh-fix` (Fresh m). Decisions in force are quoted in
[docs/decisions/p2-answers-verbatim.md](docs/decisions/p2-answers-verbatim.md).

## How the workflow runs

- **One critic round.** Follow-up work goes into the next round's plan, shown to Reuben before it runs.
- **Each task cleans up.** A task deletes its own `/tmp/p2-<task>*` build directories in `buri-lps` when it ends,
  pass or fail. Host free space under 8 GiB pauses new builds.
- **More parallel slots.** Raise `/lps/bin/rocq-slot` from 4 to 6 once Coq 8.18 is gone.
- **No replies to workflow agents.** A decision that comes up mid-run is recorded by the main session in
  `docs/decisions/` and picked up by the next task or merge.
- **Evidence rules stay.** No new axioms, no weakened theorems, counted and measured numbers kept apart, UNKNOWN when
  not run.

## Round 3a: foundations (do first, in order)

1. **Retire Coq 8.18.** Move `toolchain.lock.json`, the Makefile (`make prove`, `make report`), CI and the older Búri
   proofs to Rocq 9.3. Re-run the full gate and `rocqchk` with an unchanged assumption audit. Delete the 8.18
   workarounds and the amd64 gate container. Accept: `make report` passes in `buri-lps`, totals measured.
2. **Re-pin Shen/JIT.** Check upstream first. Take v0.8 if it is out, otherwise v0.7 (`2f4b48b`). Kernel 43.4 to
   43.6, `lower.shen` +179 lines, one new Prolog primitive. Re-capture witnesses, re-run the census and the source
   judge. Accept: hashes reproduced, the new "N of 955" measured.
3. **Lane on the merged tree.** Re-run the Shen/JIT lane and the mutation suite on round 2's final `p2/int`, and
   measure the audit count (915) and pin (306).

## Round 3b: proofs (parallel after 3a)

| Task | What | Decision behind it |
|---|---|---|
| Port primitives | Wire `jit_port_prims_proposed` into `jit_rules`; `hash` as a KL transcription of `hash_go` | Item 1 |
| Locality lemma | FunRel locality, so a definition validates when its own callees do | 10 Nov |
| inline-int-arg checker | Proved checker for `lower.subst` of integer arguments (447 dependents forecast) | Unowned, SME review's first experiment |
| Guarded inline/bind | State `inline_site_sound_g` and `bind_site_sound_g`, then prove them | Item 8 |
| Fixed-name primitives | D_wf admits `+`, `-` as `FPrim`; re-prove KRef's D_wf uses | Item 9 |
| Source profile | absvector bound, real `error-to-string` text, IO home prefix and stream state | Item 7 |
| Emit families and assembly | The per-family emit rules and their composition, on the Fresh-repaired SMs | Item 10 |
| Pipeline judge | Wire every proved checker into the stage 0 pipeline and report validated definitions | Definition of done |

## Round 4: the cliff (after round 3)

- Allocation identity in the source model, then NaN `=` modelled exactly (items 3 and 4).
- The 181-definition Prolog-heavy cluster: Prolog variables, `deref=`, binding-vector reuse at v0.7.
- Byte buffers, `quiet?`, `exit`, `read-file`, sealing.
- eval-kl stays a gated residual in Phase 2 (item 2).

## Housekeeping

- Delete merged `buri-p2-*` worktrees and their branches once `p2/int` is pushed.
- Record the full-gate recipe in the repo, not in a scratch directory.
