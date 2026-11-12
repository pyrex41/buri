# Phase 2 decision packet: gated residuals and scoped premises

Task `r21-decisions`, branch `p2/r21-decisions` off `p2/int` `f42d6c4`. **For Reuben.** Nothing in this
packet is approved. Each item is **awaiting decision**, its ledger entry stays `open`, and nothing is
marked discharged. No agent can approve these items. No Rocq file was changed.

Where things stand on `p2/int` `f42d6c4`:

- Source judge: 148 of 955 stage 0 definitions accepted. This is a Rocq verdict, pinned in
  `tests/shen-jit/stage0-accepted.txt`.
- Residual: 807.
- Full-pipeline validated: UNKNOWN, because there is no full-pipeline judge yet.

The denominator is 955, the v0.6 stage 0 set. "lower.shen proved" is not claimed anywhere.

## Decision record

Recorded by task `r21-decision-intake` on 2026-11-11, on branch `p2/r21-decision-intake` off `p2/int`
`91718d4`. An answer below counts only if it is quoted verbatim from Reuben's own message, with that
message's date. No agent, script or computed task text can supply one.

**Messages from Reuben received for this intake.** As of 2026-11-11 there is one: the workflow resume
request, relayed by the harness, which reads in full "we are back early -- resume the workflow". It
answers none of the items below. **No item has an answer, so Q0 and items 1 to 10 are all OPEN.**

**Intake of 2026-11-12 (task `r22-decide`, branch `p2/r22-decide` off `p2/int` `5f7fc96`).**

- On 2026-11-12, Q0 and then items 1 to 10, each with its default, were sent to the orchestrator (main)
  to present to Reuben. The request asked main to relay his exact words for each item, with the time he
  sent them.
- The ground rules sent with the request:
  - An item is recorded as ANSWERED only if main returns text it identifies as Reuben's own verbatim
    words.
  - A paraphrase, a blanket "approve", "go with the recommendation", or an answer written by an agent
    leaves the item OPEN.
  - No answer is inferred from another. For example, an answer to Q0 does not answer items 1 to 4.
- No reply from main had arrived when this record was committed.
- The only message from Reuben that reached this intake is again the harness-relayed workflow request,
  which reads in full "we are back early -- resume the workflow". It answers no item.
- **So on 2026-11-12, Q0 and items 1 to 10 all stay OPEN, and each default in the table below stands.**
- **Q0 is OPEN, so the literal reading stands.** Every callee-link failure is a non-gated residual and
  counts against the cap of 20. **Under this status quo, Phase 2 cannot reach the cap of 20.** By the
  forecast, any of items 1, 3 or 4 left as a residual puts hundreds of definitions against the cap.
- If Reuben answers later, a later intake adds his words to this record, with the date and the scope.
  This entry is not edited to carry them.

While an item is OPEN its default stands. That default is the status quo, or a named residual. It is
**not** the packet's recommendation. Where the packet recommends approving or amending something, that
recommendation is not adopted.

| # | item | answer | what stands while OPEN |
|---|---|---|---|
| Q0 | do callee-link failures inherit a decision gate? | OPEN (no answer received) | The literal reading of the definition of done holds: a callee-link failure is a non-gated residual and counts against the cap of 20. The packet's forecast says this puts hundreds of definitions against the cap if any of items 1, 3 or 4 stays a residual. **Under this status quo, Phase 2 cannot be done.** |
| 1 | port primitives with no approved source meaning | OPEN (no answer received) | Named residual. No port primitive is wired into `jit_rules`. |
| 2 | eval-kl | OPEN (no answer received) | Named residual. Runtime lowering stays outside the claim. |
| 3 | identity primitives | OPEN (no answer received) | Named residual. No model change. |
| 4 | `=` on two possibly-NaN computed operands | OPEN (no answer received) | Named residual. `pguard` stays as it is, and the cycle half has no case in `Out'`. |
| 5 | share premises HT and HP | OPEN (no answer received) | HT and HP stay Section hypotheses of `check_share_sound`, as on p2/r1-share-ht. Neither is replaced by a D check or recorded as met. |
| 6 | uncurrying DoD amendment | OPEN (no answer received) | DoD (2) is **not** amended. Its uncurrying line stays unmet, and `uncurry_not_kref` shows that no KRef-sound rule exists for it. |
| 7 | emit-spec premises and design choices | OPEN (no answer received) | None of the five shape and scope rows is approved. The five `frame_prim` exclusions stand, and their 35 definitions (census at `f42d6c4`) are non-gated residuals. |
| 8 | guarded inline and bind statements | OPEN (no answer received) | The refuted statements `inline_site_sound_statement` and `bind_site_sound_statement` stand, refuted. No guarded replacement is approved. |
| 9 | fixed-name `FPrim` entries in D_wf | OPEN (no answer received) | D_wf is unchanged. `fold_arith_needs_store` stands, and the 6 definitions (census) are non-gated residuals. |
| 10 | corrected SMs / `m_next` statements (r21-sms-fresh-fix) | OPEN (no answer received, 2026-11-11 and 2026-11-12). The corrected statements now exist on p2/r21-sms-fresh-fix `4ff09d1`, unmerged into p2/int. The refutations of the old text, first on p2/r22-emit-sim `82679ef`, are on `p2/int` since r22-sim-land merged `45dc6dc` (`rocq/JitEmitSim.v`) (see item 10, update of 2026-11-12) | No corrected statement is approved. On p2/int the statements stay as written in `rocq/JitEmitInv.v`, refuted (`rocq/JitEmitSim.v`); on p2/r21-sms-fresh-fix the refuted text is kept as `*_v1`. See item 10. |

The counts in this packet were computed at `f42d6c4`. They were **not re-run** on `91718d4`. The
full-pipeline validated count stays UNKNOWN.

## How to read the counts

| label | what it is |
|---|---|
| **Rocq** | a theorem or `vm_compute` verdict, cited by name. Theorems on `p2/int` were seen in `rocq/Audit_Jit.v` at `f42d6c4`. Theorems on unmerged branches were seen in that branch's `rocq/Audit_Jit.v` (a `git grep` of its `Print Assumptions` lines). Their "Closed under the global context" status is as that branch reported it; it was **not re-run on this tree (UNKNOWN)**. |
| **census** | a syntactic count over the pinned norm witness by the existing census tools. It decides nothing. |
| **test** | a Rocq `vm_compute` run over real data that its author recorded as a test, not a theorem. |
| **forecast** | `feature_census.py`'s prediction of what future checkers would admit. It is not a count of anything validated. |

Unless a count says otherwise, it is the number of the 955 stage 0 definitions affected.

Census inputs, all re-hashed in buri-lps for this packet:

- stage 0 `*.forms *.sbc`: `ec9b3872...`;
- norm witness: `e45add98...b69dd1`;
- Rocq judge verdicts src/nf/tf from the `f42d6c4` merge's `judge_split.sh` run: `7ec2a9bb...`,
  `61aff6c8...` and `45ebad60...`, the listings recorded in `stage0-residuals.txt`.

Both committed census outputs were regenerated from these inputs, and both are byte-identical to the
committed files:

- `tests/shen-jit/stage0_residuals.py` gives `tests/shen-jit/stage0-residuals.txt` (sha256 `9044ef21...`);
- `tests/shen-jit/feature_census.py` gives `spikes/pass-split/features.tsv` (sha256 `6eeef697...`).

Its src/tf/nf consistency check reports 0 mismatches against the Rocq verdicts.

Since `fc966bc`, no input of the census tools has changed: not the inputs (`JitLowerRel.pmap`,
`KLSyntax.prim_name`, `JitProfile.v`), not the walker, and not the witness. Only append-only modes were
added to `stage0_to_rocq.py`.

The per-primitive and union counts below come from a helper. It wraps `stage0_residuals.labels` and
adds no classification of its own:

- helper: `/tmp/p2-r21-decisions-census.py` in buri-lps, sha256 `fde9da69...`;
- output: `/tmp/p2-r21-decisions-census.out`, sha256 `b47a7b3d...`;
- command: `python3 -I /tmp/p2-r21-decisions-census.py /work/p2-r21-decisions /tmp/p2-r21-decisions-in/wit /tmp/p2-r21-decisions-in/judge`.

## Q0 (cross-cutting, decide first): do callee-link failures inherit a decision gate?

The definition of done counts against the cap of 20 every residual outside the four gated classes,
"including callee-link failures under the D design". Read literally, a definition whose own body
validates, but which calls a definition that is a gated residual, is a non-gated residual.

The forecast says what that costs. `spikes/pass-split/FEATURES.md`, "Decisions for Reuben", gives the
cost of leaving each item out with everything else admitted. That is a forecast (census), measured
directly, under D-src and under D-low:

| item | cost (direct / D-src / D-low) |
|---|---|
| eval-kl | -16 / -450 / -16 |
| identity primitives | -48 / -480 / -480 |
| other port primitives | -178 / -581 / -581 |
| NaN `=` | -206 / -648 / -648 |

The amplification comes from one strongly connected component. It holds 181 definitions, and 450
definitions reach it. Every one of items 1 to 4 has users inside it.

**Under the literal reading, a default of "named residual" on any of items 1, 3 or 4 puts hundreds of
callee-link residuals against the cap of 20, and Phase 2 cannot be done.** eval-kl alone survives under
D-low, at 16.

**Recommended:** rule that a callee-link failure inherits the gate when every failing member of its
callee closure is a gated residual. It is then recorded with the gated callee named. With that rule,
items 1 to 4 cost 0 against the cap whatever is decided on each. The alternative is to admit all four,
which the forecast puts at 955 of 955, and which needs model changes on every one.

## Summary

The "affected" column is in definitions of 955, with its kind. "Cap impact" is the change to the
count of 20 non-gated residuals.

| # | item | Rocq evidence | affected | recommended default | cap impact |
|---|---|---|---|---|---|
| 1 | port primitives with no approved source meaning (OB-JIT-PORT-PRIMS) | `JitProfile.jit_port_prims_off`, `jit_port_prims_partition`, `jit_port_prims_arity`, `pp_*_ok`; source judge rejects | 178 touching (census), 140 with this as their only gated item; 63 use a no-carrier operator, 158 a proposed one (census) | gated residual (status quo), plus the Q0 rule. The wiring of the 15 non-identity candidates is offered as a separate approval | 0 with the Q0 rule. Without it, up to -581 under closure (forecast): not done |
| 2 | eval-kl (OB-JIT-LOWER-GENERAL) | `JitKRefPrim.prim_param_eval_kl` (the primitive step only); source judge rejects all 16 | 16 calling `shen-jit.eval-kl` (census), 9 with only this item | gated residual. Runtime lowering stays out of Phase 2 | 0 with the Q0 rule. Without it: 16 under D-low, 450 under D-src (forecast) |
| 3 | identity primitives (OB-JIT-IDENTITY-MODEL) | `JitBytecode` `RIdentity` (`PSamep`, `same`); `JitProfile.pp_samep_ok`, `pp_taggedp_ok`; source judge rejects | 48 touching (census), 22 with only this item | gated residual, plus the Q0 rule | 0 with the Q0 rule. Without it, -480 (forecast) |
| 4 | `=` on possibly-NaN operands (OB-JIT-NAN-IDENTITY / OB-JIT-EQ-CYCLE) | `JitLowerRel.pguard`; `JitEqBudget.nan_not_reflexive`, `eq_budget_refuted`; `JitEmitInv.dv_eq_nan`, `dv_eq_cycle`, `dv_eq_cycle_rel` (r1-emit-spec-merge) | 206 touching (census), 171 with only this item, 59 with it as first blocker; cycles cannot be counted statically | gated residual now; option (a), NaN identity in the profile, is the only one that reaches all 206 | 0 with the Q0 rule. Without it, -648 (forecast) |
| 5 | share premises HT and HP (p2/r1-share-ht) | `share_needs_thaw_outright`, `share_needs_hd_tl`, `share_premises_sat`, `ht_not_com`, `hp_of_com`, `thaw_stable`, `hd_tl_stable`, `share_rewrites_validated` | 4 share rewrites (census; the Rocq verdict accepts 4 of 4 under HT/HP). 37 need thaw in D: share, thaw-sugar or copy (census) | HP: treat as met by every Com store (`hp_of_com`). HT: replace the Section hypothesis with a decidable D check, met once the emit App family admits thaw's 0-ary dynamic apply | 0 if the App family lands. Otherwise up to 37 (census): over the cap |
| 6 | uncurrying (outside KRef) | `JitFrontCopyFold.uncurry_not_kref` (no premise); `uncurry_scan` (test) | 0 multi-argument dynamic applications in the source (test). In the witness, 33 dynamic calls, all 1-argument, 0 with 2 or more (census) | amend DoD (2): no uncurrying rule. Keep `uncurry_not_kref`; any future site gets a rejection trace | 0 at v0.6 |
| 7 | emit-spec premises and design choices (p2/r1-emit-spec-merge) | `env_ok_needed`, `resp_ok_bound_needed`, `env_ok_inhabited`, `dv_*`, `gvals_needed`, `old_reflect_false`, `old_reflect'_iff_core`, `cx_catch_up`, `JitEmitNestTest` | `frame_prim` exclusions: 35 (census). `=` with `pguard`: 206 (item 4). One-argument window: 0 (census). `env_ok`: on every run statement; 18 use KL IO (census). Shapes: 0 | approve `env_ok`, the window, `GvalsRel`, catch-up and the index shape. For the `frame_prim` exclusions, decide the five source-model questions so that the families can admit them | 0 if the model questions are decided and the families land. Otherwise 35 (census): over the cap |
| 8 | guarded inline and bind statements | `JitFrontInline.inline_site_unsound`, `bind_site_unsound` (r1-f-inline); `JitFrontProlog.bind_site_unsound` (p2/int) | 528 with an inline marker, 7 with bound-now (37 sites) (census). The guard changes 0 verdicts (`site_report`, test) | approve: guarded statements, refutations kept | 0 once guarded soundness is proved. Until then the 528 cannot pass: over the cap |
| 9 | fixed-name primitive entries (`+`, `-`) in D_wf | `JitFrontCopyFold.fold_arith_needs_store` (no premise); `JitProfile.jit_defun_fixed_refused`; the `hd_tl_stable` pattern | 6 (census; the same 6 by `d00_inline_census.py` MODE=5 and by Rocq's inline-site test, 522 of 528 without fold) | approve: D_wf admits fixed-name `FPrim` entries, with a `fixed_stable` lemma. This also settles HP on the real D (item 5) | 0 if approved. Otherwise 6 of the 20 |
| 10 | corrected SMs / `m_next` statements (added by r21-decision-intake) | `JitEmitSim.preservation'_false`, `call_preservation'_false`, `call_preservation_src'_false`, `raise_resolve_false`, `fx_next`, `fx_no_funrel` (p2/r22-emit-sim `82679ef`; on `p2/int` since r22-sim-land merged `45dc6dc`) | every run statement (statement shape) | none. The corrected statements (`Fresh m`, `sm_fresh`) are on p2/r21-sms-fresh-fix `4ff09d1`, unmerged, and are not approved. Options (a), (b) and (c) are in item 10, unranked | DoD (1)'s `call_preservation_src'` cannot be proved as stated on p2/int. Over the corrected SMs its truth is UNKNOWN |

Across items 1 to 4, 391 of the 807 residual definitions touch at least one gated item (census, from
the `decisions` column of `stage0-residuals.txt`). The other 416 touch none. They wait on emit and
front families, not on these decisions.

## The items

### 1. Port primitives with no approved source meaning (OB-JIT-PORT-PRIMS)

**Evidence (Rocq, p2/int):**

- `JitProfile.jit_port_prims_off`: `jit_rules` has no port primitive, so each one raises
  `XUndefinedFun`, and the source judge rejects every definition that calls one.
- `jit_port_prims_partition`: every census operator has exactly one of a candidate meaning or a named
  reason (`jit_port_prims_residual`).
- `jit_port_prims_arity`: each candidate is in the bytecode's table at its arity.
- `pp_*_ok`: sanity lemmas on the 18 candidates.

All are in `Audit_Jit`.

**Affected (census):**

- 178 residual definitions touch a non-identity port primitive, and 140 have it as their only gated
  item.
- By operator set, over all 955:
  - 63 use one of the 19 operators with no carrier (`jit_port_prims_residual`, led by
    `shen-jit.pvar-offset` 13 and `shen-jit.pvar?` 12);
  - 158 use one of the 18 proposed candidates (led by `shen-jit.symbol-kind` 50 and
    `shen-jit.append` 41).
- The partition with item 3: `shen-jit.same?` and `shen-jit.tagged?` are proposed candidates and
  `shen-jit.deref` has no carrier. `stage0_residuals.py` files all three under identity (item 3), not
  here.

**Options:**

- (a) Wire the 15 non-identity candidates into `jit_rules`. That is one line plus a `hash` parameter,
  and each needs a JitLowerPrim-style refinement lemma. JitProfile's header lists the choices to
  accept: XUser messages, `hash` as a parameter, dictionary key comparison and the heap limit.
- (b) Keep everything a gated residual.

**Recommended default:** (b) for the 19 no-carrier operators, which are decision-gated by definition,
together with the Q0 rule. (a) for the 15 candidates is a separate approval: it is model work for the
emit Prim family, not for this packet.

**Cap:** 0 with the Q0 rule. Without it, leaving the non-identity port primitives out costs -178
direct and -581 under D-src/D-low (forecast). The phase is then not done.

### 2. eval-kl (OB-JIT-LOWER-GENERAL)

**Evidence (Rocq, p2/int):**

- `JitKRefPrim.prim_param_eval_kl` proves eval-kl's *primitive step*: `parse` of related data gives
  related expressions.
- Nothing relates the code that shen-jit lowers at runtime to its input. That is OB-JIT-LOWER-GENERAL,
  and it needs a source-linked model of lower.shen.
- The source judge rejects all 16 callers (Rocq verdict).

**Affected (census):** 16 definitions call `shen-jit.eval-kl`, 6 with it as their first blocker, and
9 have no other gated item. Four of them sit in the 181-definition component. `shen-jit.eval-kl` itself
needs `shen-jit.install`, which is item 1.

**Recommended default:** a gated residual. Runtime lowering correctness stays out of Phase 2 scope, and
the claim is stated as "for definitions lowered at stage 0".

**Cap:** 0 with the Q0 rule. Without it: 16 under D-low, or 450 under D-src (forecast).

### 3. Identity primitives (OB-JIT-IDENTITY-MODEL)

**Evidence (Rocq, p2/int):**

- `JitBytecode`: `same` returns `None` on pairs, strings and reals, and the machine stops with
  `MStuck RIdentity` (the `PSamep` case and `eq_val`'s `EqIdentity`).
- `JitProfile.pp_samep_ok` and `pp_taggedp_ok` model `same?` and `tagged?` as `OWrong` there.
- The source judge rejects these definitions (Rocq verdict).

**Affected (census):** 48 residual definitions use `shen-jit.same?`, `shen-jit.tagged?` or
`shen-jit.deref` (feature column `identity = yes`: also 48). 22 have no other gated item. By operator:
`deref` 37, `tagged?` 12, `same?` 4.

**Options:** give pairs, strings and reals identity in both models, which is a model change through
KLValue, KLPort and the bytecode; or prove that admitted programs never reach the stuck case; or keep
a residual.

**Recommended default:** a gated residual, with the Q0 rule.

**Cap:** 0 with the Q0 rule. Otherwise -48 direct and -480 under closure (forecast).

### 4. `=` on possibly-NaN operands (OB-JIT-NAN-IDENTITY, OB-JIT-EQ-CYCLE)

**Evidence:**

- Rocq, p2/int:
  - `JitLowerRel.pguard` admits `=` only when an operand is a safe constant, never a NaN;
  - `JitEqBudget.nan_not_reflexive` (an Example): two NaNs compare false;
  - `eq_budget_refuted`: the budget statement is false without its hypotheses;
  - `JitProfile`'s `Dev "nan-identity"` row.
- Rocq, p2/r1-emit-spec-merge `7bb9bb7`, in its Audit_Jit:
  - `dv_eq_nan`: on two NaNs the bytecode is stuck;
  - `dv_eq_cycle` and `dv_eq_cycle_rel`: on two related cyclic vectors the source goes wrong and the
    bytecode is stuck in `RCyclic`;
  - `dv_eq_cycle_same`.

**Affected (census):** 206 definitions have `=` on two computed operands, and 59 have it as their first
blocker. 171 have no other gated item. 98 of them are "guardable", meaning one operand is never a real
by the Python `NONREAL` heuristic. That is a census, not a Rocq judgment. Cycles are a run-time
property, and no static census exists (UNKNOWN).

**Options (forecast, direct / D-src / D-low):**

- (a) a NaN identity rule in the profile or the semantics: +171 / +129 / +129;
- (b) a Rocq static non-real judgment extending `pguard`: +98 / +18 / +18;
- (c) a gated residual: +0.

For the cycle half: a named limit of the claim. `Out'` has no case for it, and neither side answers.

**Recommended default:** (c), with the Q0 rule, and the cycle half as a named limit. If Reuben wants
these definitions inside the claim, (a) is the only option that covers all 206.

**Cap:** 0 with the Q0 rule. Without it, -648 under closure (forecast).

### 5. Share premises HT and HP (p2/r1-share-ht `0695f04`, unmerged)

**The premises.** They are the Section hypotheses of `JitFrontShare.check_share_sound`:

- HT: D defines `thaw` as the kernel does, `(defun thaw (V) (V))`.
- HP: D holds `hd` and `tl` as the primitives.

**Evidence (Rocq, in that branch's Audit_Jit):**

- `share_needs_thaw_outright`: D_wf, FrontHyps and HP hold, and `share_rule` is not `rule_sound`, so HT
  cannot be dropped.
- `share_needs_hd_tl`: each half of HP is necessary.
- `share_premises_sat`: the premises can hold together.
- `ht_not_com`: with HT, no store meeting D has `Com`, because Comp has no dynamic apply. So HT and
  call_preservation_src's premises cannot hold together on today's back end.
- `thaw_stable` and `hd_tl_stable`: these entries can come only from the initial store.
- `hp_of_com`: every Com store meets HP's store side.
- `share_rewrites_validated`: a `vm_compute` verdict accepting the 4 v0.6 share rewrites under HT, HP
  and D_wf.

**Affected (census, features.tsv):** share fires in 4 definitions (`shen.macros`, `shen.process-let`,
`shen.lambda-of-defun`, `shen.process-assoc`).

The same blocker (`ht_not_com`) stands behind every front rule that needs the kernel's `thaw` in D:

- `JitFrontSugar.chk_thaw` checks `has_thaw` on D;
- `JitFrontCopyFold.KRefF_thaw` on r1-f-copy-fold-apply.

Share, thaw-sugar or copy fires in 37 definitions (census).

HP on the real D has a second dependency. D_wf asks that every D entry be sealed. JitFrontD notes that
a primitive entry such as `(cons, FPrim PCons)` would break D_wf, because cons is not sealed. Whether
the pinned sealed list holds `hd` and `tl` was not checked (UNKNOWN). If it does not, HP waits on item 9.

**Recommended default:**

- HP: record it as met by every store of call_preservation_src (`hp_of_com`). Its D-side half is
  settled together with item 9.
- HT: do not keep it as a Section hypothesis of the pipeline. Make it a decidable check on D, as
  `has_thaw` already is. Its satisfiability then follows from DoD (2)'s emit App family: once Comp
  admits thaw's 0-ary dynamic apply, `ht_not_com` no longer holds. OB-JIT-IMAGE shows that the image's
  initial table binds `thaw`.

The ledger entry is OB-JIT-SHARE-THAW on the branch. Until merge, it is recorded here under
OB-JIT-LOWER-FRONT.

**Cap:** 0 if the App family lands. If it does not, up to 37 definitions (census) carry a premise
outside call_preservation_src's. Those are over the cap. Of the residual witness, the counterexample
half exists (`share_needs_thaw_outright`). The `vm_compute` rejection traces do not yet exist.

### 6. Uncurrying (p2/r1-f-copy-fold-apply `6278940`, unmerged)

**Evidence:**

- Rocq: `JitFrontCopyFold.uncurry_not_kref`, with no premise, in that branch's Audit_Jit. It binds F
  to a partial application of a 2-ary g. Then `(F 1 2)` returns in the source, while `((F 1) 2)`
  raises `XArity` under jit_rules' arity errors.
- Under jit_rules no `VPartial` is ever made. The counterexample is reached only through KRef's
  quantification over related environments.
- `uncurry_scan` (test: a Rocq `vm_compute` over the 955 parsed sources, not in Audit_Jit) finds 0
  dynamic applications of two or more arguments.

**Affected:** 0 multi-argument dynamic applications in the stage 0 sources (test). The census on the
norm witness agrees: 33 definitions make a dynamic call, all with 1 argument, and 0 with 2 or more.

**Conflict with the definition of done.** DoD (2) lists "dynamic-application uncurrying" among the norm
families that get a checker with closed soundness. `uncurry_not_kref` shows no KRef-sound rule exists
for it. That DoD line cannot be met as written.

**Recommended default:** amend DoD (2) to "uncurrying: no rule". `uncurry_not_kref` is kept as the
counterexample and `uncurry_scan` as the scope fact. Any site that appears in a later build gets a
pipeline-judge rejection trace naming it. The ledger entry is OB-JIT-FRONT-UNCURRY on the branch,
recorded here under OB-JIT-LOWER-FRONT.

**Cap:** 0 at v0.6.

### 7. Emit-spec scoped premises and design choices (p2/r1-emit-spec-merge `7bb9bb7`, unmerged)

None of these is approved. Every `dv_*` below is a closed Example at the primitive or call level, not
a refutation of `sim'_statement`. Only `env_ok` has a statement-level necessity proof.

| premise or choice | Rocq evidence | affected | recommended | cap |
|---|---|---|---|---|
| `env_ok` on the run statements | `env_ok_needed`, `resp_ok_bound_needed` (`preservation'_statement` without it is false), `env_ok_inhabited`, `dv_io_fail` | every run statement (all 955). 18 use a KL IO primitive (census) | approve, as a named assumption about the environment, not derivable from the pin. Necessity is proved for `preservation'` only | 0 |
| `frame_prim` excludes absvector | `dv_absvector_src`, `dv_absvector_byt` (at 2^48 the source allocates and the bytecode raises) | 17 (census) | decide the bound: put the bytecode's limit in the source profile | in the 35 |
| `frame_prim` excludes error-to-string | `dv_ets_src`, `dv_ets_byt`, `dv_ets_rel` ("error" against the exception's text) | 3 (census) | decide under OB-JIT-ERROR-TEXT (messages not compared) | in the 35 |
| `frame_prim` excludes open, close, read-byte, write-byte | `dv_open` (home-directory prefix), `dv_close`, `dv_read_closed`, `dv_write_closed` (closed-stream state) | open 3, close 4, read-byte 13, write-byte 2 (census) | model the prefix and the stream state in the source port | in the 35 |
| `=` only with `pguard` | `dv_eq_nan`, `dv_eq_cycle`, `dv_eq_cycle_rel` | 206 (item 4) | as item 4 | as item 4 |
| dynamic-call window of at most one argument | `dv_window`, `dv_window_rel` | 0 with 2 or more arguments; 33 with 1 (census) | approve | 0 |
| `GvalsRel [] s m` on the `*_old` statements | `gvals_needed` | 0 (statement shape) | approve | 0 |
| catch-up form of the reflection | `old_reflect_false`, `cx_catch_up`, `old_reflect'_iff_core` | 0 (statement shape). `old_reflect_core_statement` stays UNKNOWN | approve the form | 0 |
| six-parameter `Rule_X` hooks with `c`/`cv` indices | `JitEmitNestTest` (nested `Comp_ind'` works); uniform-index strict-positivity failure (scratchpad only) | 0 (proof structure) | approve | 0 |

**Affected by the five `frame_prim` exclusions together:** 35 definitions (census, union). The union
with the `pguard`-only `=` is 237.

**Recommended default:** approve the five shape and scope rows (`env_ok`, the window, `GvalsRel`,
catch-up, the index shape). For the `frame_prim` exclusions, do **not** default to residuals. Each one
is a disagreement between the source model and the bytecode on a question with no recorded answer:

- the absvector bound;
- the error-to-string text;
- the home-directory prefix on open;
- closed or wrong-direction stream state;
- the raise continuation of an IO failure with no handler.

Reuben deciding those questions is what lets the Store, Prim and IO families admit the frames.

**Cap:** 0 for the approved rows. The exclusions are not gated classes. If they stand, the 35
definitions (census) are non-gated residuals, over the cap on their own, and the phase is not done.

### 8. Guarded replacements for the refuted inline and bind statements

**Evidence (Rocq):**

- `JitFrontInline.inline_site_unsound`: `~ JitFrontD.inline_site_sound_statement`.
- `JitFrontInline.bind_site_unsound`: `~ JitFrontD.bind_site_sound_statement`. Both are on
  p2/r1-f-inline `be367ab`, unmerged.
- `JitFrontProlog.bind_site_unsound`: the second refutation of `bind_site_sound_statement`. It is on
  p2/int `f42d6c4`, in Audit_Jit.
- The hole: a thawed frozen argument that reads KLPort's closure-identity key `id_key`.
- The proposed guard: add `negb (bound (K.fv x) KLPort.id_key)` to `inl_eq`'s SFrozen case and to
  `bind_site`.
- r1-f-inline has the guarded checkers `inl_site_g` and `bind_site_g`. Their soundness is **not
  proved** (open under OB-JIT-LOWER-FRONT).
- `JitFrontInline.aeq_sound` is proved.

**Affected:** 528 definitions carry an inline marker, and 7 have bound-now rewrites (37 sites)
(census). The guard changes no verdict: `site_report` gives 5430 inline sites, 0 frozen arguments
reading `id_key`, and 37 of 37 bound-now sites accepted with and without the guard. That is a test,
r1-f-inline's run on stage 0 `ec9b3872` and norm `e45add98`. `id_key` is `"\0id"`, which no stage 0
name contains.

**Recommended default:** approve.

- State `inline_site_sound_g_statement` and `bind_site_sound_g_statement` over the guarded checkers in
  `JitFrontD.v`. That file is D00's, so its owner makes the edit.
- Keep the two old statements as `Definition`s. Keep all three refutations in Audit_Jit.

This is replacing a false statement with a guarded one. It is not weakening a statement to make a
proof go through: the refutations stay as the record, and the guard rejects nothing in stage 0.

**Cap:** 0 once the guarded soundness is proved. Until then, no definition with an inline marker
passes the pipeline judge: 528 (census), far over the cap.

### 9. Fixed-name primitive entries (`+`, `-`) in D_wf

**Evidence:**

- Rocq, p2/r1-f-copy-fold-apply `6278940`: `JitFrontCopyFold.fold_arith_needs_store`, with no premise,
  refutes `KRef sealed [] [] (+ 1 2) 3` with a store, allowed by SRel, whose `+` is a user function.
  So fold-arith needs a D fact about `+` and `-`.
- `JitKRef.D_wf` asks that every D entry be sealed and that the names be distinct. A D built by
  `JitFrontD.D_of` therefore never holds `+` or `-` (JitFrontD interface item 2).
- Rocq, p2/int: `JitProfile.jit_defun_fixed_refused` (defun of a fixed name raises).
- Rocq, r1-share-ht: the `hd_tl_fixed`, `hd_tl_defun_refused` and `hd_tl_stable` pattern. A fixed
  name's entry can come only from the initial store.
- `hp_of_com`'s argument (`JitLowerStep.fr_name`: Com gives every primitive name its primitive) covers
  `+` and `-` too.

**Affected:** 6 definitions:

- `shen.x.type-annotations.function-type`
- `shen.initialise-environment`
- `shen-jit.nonempty-vector?`
- `tlv`
- `shen.typecheck`
- `shen.declare-with-signature`

The count comes from three sources that agree: features.tsv (fold-arith family, census),
`d00_inline_census.py` MODE=5 (the 6 fold-needing inline sites are in the same 6, census), and
JitFrontD's Rocq inline-site run (522 of 528 marker definitions accepted without fold, 528 with,
test).

**Options:**

- (a) D_wf admits an entry `(f, FPrim p)` when `is_fixed_name f` holds and `prim_of_name f = Some p`,
  with a `fixed_stable` lemma like `sealed_stable`, and with KRef's uses of D_wf re-proved.
  `call_preservation_src_statement` stays byte-identical, but D_wf, its hypothesis, admits more D.
  That makes the theorem stronger, not weaker, and it must be re-proved. Reuben should see that the
  meaning of a byte-identical statement changes.
- (b) A store premise discharged from Com, as `hp_of_com` does. But the front soundness quantifies
  over SRel stores, and DoD (1) forbids strengthening SRel. So (b) needs a KRef variant.
- (c) A residual.

**Recommended default:** (a). It also lets HP (item 5) hold on the real D, whether or not `hd` and
`tl` are sealed.

**Cap:** 0 if approved. Under (c), 6 non-gated residuals out of the 20. Their counterexample is
`fold_arith_needs_store`. Their `vm_compute` rejection traces do not exist yet.

### 10. Corrected SMs / `m_next` statements (r21-sms-fresh-fix)

Added by `r21-decision-intake` on 2026-11-11. **OPEN.**

**What is asked.** The task text names "the corrected SMs/m_next statements from r21-sms-fresh-fix" for
Reuben's decision. Replacing the statements would change the statement of DoD (1)'s
`call_preservation_src'`. That is Reuben's call, not an agent's.

**What was found.** On 2026-11-11 no `r21-sms-fresh-fix` branch or worktree existed. These searches
found nothing by that name:

- `git branch -a`;
- `git worktree list`;
- `git log --all -i --grep=fresh --grep=SMs`.

No corrected statement text exists for Reuben to approve. This packet does not propose any.

**Evidence that the current statements are false.** All of it is in Rocq, first on p2/r22-emit-sim `82679ef`.
When this item was written that branch was unmerged (`82679ef` was not an ancestor of `91718d4`). The
refutation is now on `p2/int`: r22-sim-land (branch `p2/r22-sim-land`) merged `p2/r22-emit-sim` `45dc6dc`
unchanged, so `rocq/JitEmitSim.v` and the lines below are in p2/int's Audit_Jit. The merge's lane evidence
is in docs/STATUS.md under r22-sim-land. This adds evidence only; it answers nothing, and the item stays OPEN.

- `preservation'_false`, `call_preservation'_false` and `call_preservation_src'_false` refute the three
  statements at `cx_E`, `cx_pt`, sealed `[]`. `raise_resolve_false` refutes that branch's own premise.
- The cause is that SMs says nothing about the machine's allocation pointer `m_next`, and
  `JitBytecode.alloc` writes at `m_next` without looking.
- The witness `fx_m` is SM-related with `m_next` pointing at do's closure. On
  `(defun f (X) (hd X))` with 1, its first step raises with no handler. The exception overwrites do's
  closure (`fx_next`). `FunRel'` then fails for every store (`fx_no_funrel`).
- `sim'_statement` is **not** refuted.
- The fix that branch names belongs to emit-spec: SMs keeps `m_next` fresh, meaning every key at or
  above it is unused. The mutant `ShenJitEmitSimFreshNext` gives the witness a fresh pointer, and the
  lane rejects it.

**What stands while OPEN.** The three statements stay as they are in `rocq/JitEmitInv.v`, and the
refutations stay as the record. DoD (1) asks for `call_preservation_src'` to be proved, and as stated it
cannot be. Two things are needed before Reuben can decide:

- a branch that states the corrected SMs and the corrected statements;
- that branch's Rocq evidence.

**Ledger:** OB-JIT-LOWER-FRAGMENT, which owns the emit-spec statements.

**Update, 2026-11-12 (r21-sms-fresh-fix, branch p2/r21-sms-fresh-fix, fix round 2).** The corrected
statements now exist. This entry was written on that branch, because `r21-decision-intake` is not an
addressable agent; the integrator carries it into the intake record. Status: **OPEN**. No answer from
Reuben was received. "we are back early -- resume the workflow" answers no item.

What Reuben is asked to sign off, all in `rocq/JitEmitInv.v` unless named otherwise:

- `Fresh m` (no heap key at or above `m_next` in use) and the new field `sm_fresh` of `SMs`. SM, MS',
  Ends' and EndsSrc' inherit it. This strengthens the relation; it weakens no conclusion.
- `preservation'_statement`, `call_preservation'_statement`, `call_preservation_src'_statement` and
  `JitEmitSim.raise_resolve_statement`: text unchanged, over the corrected SMs. Their conclusions,
  including the observation equivalence (`map Some tS = tT`), are unchanged. Truth UNKNOWN (not refuted,
  not proved).
- The refuted text is kept as `*_statement_v1` over `SMs_v1`, and `preservation'_false`,
  `call_preservation'_false`, `call_preservation_src'_false` and `raise_resolve_false` refute the `_v1`
  text (closed).
- `sm_embed` and `ms_embed` take a new premise, `Fresh m`. Their base text is false over the repaired
  relation (`JitEmitSim.sm_embed_text_false`, `ms_embed_text_false`, closed). The base text over the old
  relation is kept as `sm_embed_v1` and `ms_embed_v1`.
- The old-fragment recovery reached through the corrected statements is
  `call_preservation_src_old_fresh_statement`: the 4a7346e `JitKRef.call_preservation_src_statement`
  with `GvalsRel [] s m` and `Fresh m` added, conclusion verbatim, and conditional on
  `old_reflect'_statement` (truth UNKNOWN), as at the base.

What is NOT reached: a corollary from the corrected `call_preservation_src'_statement` to the
byte-identical `JitKRef.call_preservation_src_statement` that uses its hypothesis.

- `JitEmitSim.fresh_needed` and `JitEmitInv.gvals_needed` (closed) refute only direct instantiation: the
  old premises hold at a machine the new invariant relates at no mu.
- They are not counterexamples to recovery. The byte-identical statement is proved outright
  (`JitKRefFund.call_preservation_src`), so the implication holds trivially. That is why the base-named
  `*_old_of_new` corollaries typecheck with their hypotheses unused. They are kept for name preservation
  and are not evidence.
- A non-vacuous route would normalize the machine (`m_next` above every key, globals from the store),
  apply the corrected statement and transfer the run back. It was not built. Its obstacles are named in
  `rocq/JitEmitSim.v` ("after the repair").

Options for Reuben:

- (a) accept `Fresh m` and `GvalsRel [] s m` as extra premises of the recovery target;
- (b) fund the normalize-and-transfer lemma (a new task; its feasibility is UNKNOWN);
- (c) change the relation or the requirement.

**Carried into p2/int's record by `r22-decide` on 2026-11-12.** The update above is the docs text of
`4ff09d1`, applied to this file only. No Rocq file from that branch was brought in. On p2/int `5f7fc96`:

- `rocq/JitEmitInv.v` still has the pre-repair SMs;
- `rocq/JitEmitSim.v` does not exist;
- neither `4ff09d1` nor `82679ef` is an ancestor (checked with `git merge-base --is-ancestor`).

The Rocq claims in the update are as those branches reported them. They were not re-run on this branch,
so they are UNKNOWN here. On 2026-11-12 item 10 was presented to Reuben through main, and no answer came
back. It stays **OPEN**. Options (a), (b) and (c) are listed in the order the branch gave them and are
not ranked.

**Merged into p2/int after `r22-decide`.** The r22-sim-land merge (branch `p2/r22-sim-land`, `f802162`)
brought `rocq/JitEmitSim.v` from p2/r22-emit-sim `45dc6dc` (a descendant of `82679ef`) into p2/int, so the
refutations listed above are now in p2/int's Audit_Jit; its lane evidence is in docs/STATUS.md under
r22-sim-land and under the integration entry for this merge. `4ff09d1` (the corrected statements) is still
not an ancestor of p2/int, and `rocq/JitEmitInv.v` still has the pre-repair SMs. This adds evidence only;
item 10 stays **OPEN**.

**r22-sms-land, 2026-11-12: not approved, nothing landed.** Task r22-sms-land (branch `p2/r22-sms-land` off
p2/int `52898d1`) was to land the corrected SMs (`Fresh m_next`) and the corrected `preservation'`,
`call_preservation'` and `call_preservation_src'_statement` from p2/r21-sms-fresh-fix `d2041f6` only if
item 10 was answered with approval. At `52898d1` item 10 is OPEN: no answer from Reuben is recorded
here, in `spec/obligations.json` or on any `p2/*` branch tip (checked with `git grep`). So no statement in `rocq/JitEmitInv.v` changed and
no Rocq file changed on that branch. The `*_v1` text, the re-review against JitEmitSim's
counterexamples, mutant `ShenJitEmitInvFreshDropped` and `old_reflect'_statement` were not touched.
`call_preservation_src'` (DoD (1)) stays **unmet**: on p2/int it is refuted as stated
(`JitEmitSim.call_preservation_src'_false`), and over the corrected SMs its truth is UNKNOWN.
`old_reflect'_statement` stays unsettled (UNKNOWN).

## Ledger

Each item has a dated `history` entry in `spec/obligations.json` saying "awaiting Reuben's decision,
docs/decisions/p2-decisions.md". No status changed. All stay `open`, and nothing is discharged.

| item | ledger entry |
|---|---|
| 1 | OB-JIT-PORT-PRIMS |
| 2 | OB-JIT-LOWER-GENERAL |
| 3 | OB-JIT-IDENTITY-MODEL |
| 4 | OB-JIT-NAN-IDENTITY and OB-JIT-EQ-CYCLE |
| 5, 6, 8, 9 | OB-JIT-LOWER-FRONT |
| 7 | OB-JIT-LOWER-FRAGMENT |
| 10 | OB-JIT-LOWER-FRAGMENT |
| Q0 | OB-JIT-STAGE0 |

Task `r21-decision-intake` added one more dated `history` entry for Q0 and for each of items 1 to 10.
Each one records the item as OPEN, with no answer from Reuben, and states the default that stands. No
`status` changed.

Task `r22-decide` added one more dated `history` entry on 2026-11-12 to each of the same 12 entries:

- Q0, and items 1 to 10;
- the item 4 cycle half, under OB-JIT-EQ-CYCLE.

Each entry records that the item was presented through main and that no answer from Reuben came back.
It also states that the item stays OPEN with its default. No `status` changed.

The front items have their own ids on unmerged branches: OB-JIT-SHARE-THAW on r1-share-ht and
OB-JIT-FRONT-UNCURRY on r1-f-copy-fold-apply. This branch does not create them, to avoid duplicate ids
at merge. The integrator can move the history entries there.

## Not run, or UNKNOWN

- This branch made no Rocq change, so the Audit_Jit "Closed" status of the branch-only theorems was
  not re-run here.
- The full-pipeline validated count is UNKNOWN.
- Cycle reachability for `=` was not measured.
- Whether the pinned sealed list holds `hd` and `tl` was not checked.
- The lane result for this branch is in the task report.
