# fstar-jit: an F* port of the Shen/JIT Phase 2 Rocq development (pilot)

This is a pilot port of `rocq/` (base `shen-jit-phase0`, commit 4cba179) and of
`rocq/JitLowerEquiv.v` (branch `pass/equiv`, commit 670d29d) to F*. It exists to compare the two
provers on effort, check time and proof stability for this project. It is a comparison artifact.
It does not replace any Rocq evidence, and nothing here verifies Shen/JIT.

## Toolchain

| item | value |
|---|---|
| F* | v2026.10.25, commit 362e792b3aa882f1766b95c7450e3fe63081163d, OCaml 5.3.0 build |
| release tarball | `fstar-v2026.10.25-Darwin-arm64.tar.gz`, sha256 `cdd215b977380b7b0b3c8a5e628a556042789406d8684128e4e074a3d2ecf1e1` |
| Z3 | 4.13.3, the copy bundled in the release (`fstar/lib/fstar/z3-4.13.3/bin/z3`), not Homebrew's |
| install | `~/opt/fstar-v2026.10.25/`; wrapper `~/opt/fstar-v2026.10.25/fstar-run` |

The release binary links `/opt/homebrew/opt/{zstd,gmp}`, but this machine's Homebrew lives in
`~/.local/Homebrew`. The wrapper sets `DYLD_FALLBACK_LIBRARY_PATH` to those two library directories.
It runs `fstar.exe --z3version 4.13.3 --smt <bundled z3>`. Defaults in this F* version are
`--fuel 2 --ifuel 1 --z3rlimit 5`.

This F* version differs from older F* documentation in ways that cost time:
- `squash` takes a `prop`. A proof-relevant type `t` is made a proposition with
  `exists (_ : t). True` (`JitLowerRel.inhabited`).
- `introduce`/`eliminate` no longer bind hypothesis names or take `returns`.
- `--split_queries` does not exist.

## Running

All checks are `nice -n 19` and verify one module at a time.

- `./check.sh Buri.X.fst [opts]` verifies one module. Dependencies are cached in `_cache/`. The
  module's own `.checked` file is deleted first, because a current `.checked` file makes F* skip
  the module silently. That made early timings meaningless until it was fixed.
- `./check_all.sh` verifies every module from an empty cache, in dependency order, and writes
  `timings-all.txt`.
- `./run_stage0.sh` runs the stage 0 judge on all 24 files and writes `stage0-timings.txt`.
- `./seeds.sh` reruns the three hardest modules with `--z3seed 1..5` and writes `seeds.txt`.
- `./gen_stage0.sh` regenerates `stage0/` from pinned Shen/JIT d3348ce (see Stage 0 below).

## Fidelity rules kept

- No `admit`, `assume`, `assume val` or `--admit_smt_queries` anywhere. Check with
  `grep -rn "admit\|assume" *.fst`: the only hit is a comment saying that nothing is assumed.
- Statements say what the Rocq statements say. Every place where the form differs is listed
  under "Encoding differences", with the reason it is the same proposition.
- Theorems that Rocq proves but this port does not take the missing theorem as an explicit
  argument (`sim`) and are called "from sim". `Buri.Unfinished` lists every unported statement.

## Per-file table

In the table below:
- "Lemmas" counts Rocq `Lemma`/`Theorem`/`Corollary` items as ported-and-proved / Rocq total.
- A missing lemma is counted as "subsumed" when its content is discharged inside a ported lemma
  rather than stated on its own.
- CPU is F* plus Z3 for one module, from the clean nice'd run in `timings-all.txt` (load average
  22 to 34 on this machine throughout).
- "rlimit" is the largest `--z3rlimit` the module sets; "used" is the largest rlimit a query
  actually consumed (`--query_stats`).

| Rocq file | Rocq lines | F* lines | Lemmas proved / Rocq | rlimit (max used) | CPU s | Notes |
|---|---:|---:|---|---|---:|---|
| Observation.v (slice) | 399 | 64 | 1/1 needed (`star_trans`) | 5 | 0.3 | Coinductive behaviours and refinement theorems not ported: no Jit file uses them. |
| KLSyntax.v | 116 | 116 | 6/6 | 20 (fuel 37) | 0.3 | `all_prims_complete` needs fuel 37 to unroll the 36-element list. Rocq does it in one line (`destruct p; cbn; tauto`). |
| KLValue.v | 214 | 185 | 7/7 | 5 | 0.7 | Nested induction comes free from `<<`; Rocq needed the hand-written `value_rect'`. |
| KLSemantics.v | 387 | 377 | 0/0 (definitions) | 5 | 0.8 | `parse`'s local fixpoints become mutual functions. |
| KLPort.v | 391 | 310 | 16/24 (8 subsumed) | 5 (fuel 3) | 1.1 | `next_r_agreed` and `step_r_agreed` are proved. The eight `rule_*_agreed`/`prim_move_r_agreed` lemmas are discharged by SMT inside `prim_rule_r_agreed`. |
| JitFloat.v | 224 | 198 | 0/0 | 5 | 0.4 | Plus 869 `assert_norm` test vectors against host IEEE-754 (`Buri.JitFloatTest`, 11.4 s). |
| JitBytecode.v | 1351 | 1442 | 0/0 (definitions) | 5 | 3.4 | Line for line. `prim_step` is matched on the primitive, then on argument shape, with one shared fallback. |
| JitMeta.v | 144 | 87 | 17/17 | 60 (used 20.1) | 2.1 | `excluded_prims_stuck` is the hardest query in the port (a 130-way match, by SMT). |
| JitProfile.v | 190 | 155 | 10/10 | 5 | 0.8 | `vm_compute` facts become `assert_norm`. |
| JitLowerRel.v | 176 | 230 | 0/0 (definitions) | 5 | 2.4 | Mutual inductive types; `vrp` (VR as a prop, proved equivalent) added. |
| JitLowerCheck.v | 477 | 615 | 17/22 (5 subsumed) | 40 (used 9.7) | 19.3 | `check_fn_sound` is proved. The soundness proof is a mirror of the checker that returns the `comp` derivation, and checked first try apart from 2 binding fixes. |
| JitLowerStage0.v | 50 | 67 | 0/0 | 5 | 0.6 | Plus `stage0_to_fstar.py` (90 lines, the twin of `stage0_to_rocq.py`). |
| JitLowerKont.v | 170 | 194 | 3/3 | 5 | 3.8 | KD/TK/KC/RK are mutual inductive types; MEnv is restated with a pattern (see below). |
| JitLowerStable.v | 99 | 120 | 6/6 (`K_stable`) | 40 (used 1.3) | 2.6 | `K_stable` is a mutually recursive function on the derivation, with no combined scheme. About 70 lines against Rocq's 60, with no tactic scripting. |
| JitLowerPrim.v | 176 | 227 | 15/16 (1 subsumed) | 100 (used 1.3) | 6.8 | All `p_*` lemmas and `prim_agree`. |
| JitLowerStep.v | 1242 | 169 | 8/83 | 5 | 1.5 | Definitions (msr, Sstar, TStar, FunRel, Com, MS, Out) and 8 small lemmas. **`sim` and its 75 supporting lemmas are not ported.** |
| JitLowerThm.v (670d29d) | 96 (base) / 104 | 131 | 5/5, from `sim` | 5 | 2.1 | `preservation`, `related_progress`, `call_preservation` and `Ends_final`, each taking `sim` as an argument. |
| JitLowerEquiv.v (670d29d) | 953 | 1010 | 41/52 (+1 Rocq leaves open) | 100 (used 2.6) | 8.3 | All definitions. Premise specs, worlds, ground relation, `KRel_top`, `vrefl`, `store_refl_of_fundamental`, `adequacy_of_fundamental`, `call_preservation_src_of_fundamental` (also from `sim`). **`compat_type`, unproved in Rocq, is proved.** |
| Helpers (`Buri.Lib`, `LibTest`) | n/a | 189 + 388 | n/a | 5 | 1.0 | Rocq standard-library semantics: truncated N subtraction, `Z.quot`/`Z.div`, two's-complement bit ops, list edge cases. 380 test vectors. |
| **Total, without tests or generated data** (F* includes `Buri.Lib`, `Buri.Unfinished`) | **6,855** | **5,909** | | | **69.9 for all modules** | Rocq's `JitLowerStep` proof (about 1,100 lines) is the missing bulk. |

The whole port, every module from an empty cache, took 76 s wall and 70 s CPU, nice'd on a loaded
machine.

## Stage 0 judge (item 3)

- Data: `gen_stage0.sh` exports Shen/JIT d3348ce with `git archive` and runs its stage 0 recipe
  with the bootstrap 0.1 binary and kernel 43.4 from `~/projects/shen-jit/.deps`. All 48 outputs
  match d3348ce's `generated.sha256`, so this is exactly the pinned stage 0.
  - The local `shen-jit/build/stage0` directories are from a newer commit (b7f68e2) and differ.
    For example, `lower` has 123 definitions there against 120 at the pin.
  - `stage0_to_fstar.py` tokenizes the files into `sx` trees. The tokenizer and real-to-bits code
    are copied unchanged from `stage0_to_rocq.py`.
- Result: the F* judge's (accepted, rejected, unparsed) counts equal
  `tests/shen-jit/stage0-accepted.txt` for all 24 files: 61 accepted, 889 rejected, 0 unparsed,
  of 950.
  - This is the same gate `check-shen-jit.sh` applies, and the strongest check that the
    transliteration of KLSemantics.parse, JitBytecode's loader and JitLowerCheck is faithful.
  - Negative controls fail as expected: changing the expected counts of `declarations` or
    `extension-features` makes the `assert_norm` fail.
- Method: `assert_norm (counts forms sbc == (a, r, u))` under `--use_nbe true` (normalization by
  evaluation). The trust base is F*'s NbE normalizer, as Rocq's is its VM.
- Timing (clean run, nice'd, loaded machine): 147 s wall in total.
  - Elaborating the 24 data modules takes 104 s CPU; `init` alone (one huge `defun`) takes 18.6 s.
  - The 24 judge `assert_norm`s take 28.4 s CPU.
  - Rocq's figure, given in the task, is roughly 5 minutes. It was not measured here, because the
    machine was busy.
- The default normalizer is not usable at this scale: 160 s CPU for the 4-definition
  `extension-features`, against 0.4 s under NbE. At that rate the full run would take hours.

## Stability (z3seed 1 to 5)

The three hardest lemmas, by consumed rlimit, are:
- `JitMeta.excluded_prims_stuck` (20.1 used of 60);
- the mutual `JitLowerCheck.chk_sound` block (9.7 of 40);
- `JitLowerEquiv.compat_type` (2.6 of 100).

`seeds.sh` reran each of their modules with `--z3seed` 1 to 5: **15 of 15 runs pass**. Module CPU
spread was 2.1 to 2.9 s, 18.5 to 26.2 s and 6.8 to 9.7 s respectively.

## Encoding differences (statements unchanged in meaning)

- **Props vs. types.** Rocq inductive Props become `noeq` inductive F* types (proof-relevant).
  This covers VR, Comp and its companions, KD/TK/KC/RK, DoneR/ArgsAt/ParamAt, step, step_r, star,
  Sstar, TStar, MS, Out, TN, Ends, runs, PR's list form `vrs`, and `fo`. Where Rocq states
  "a derivation exists", F* takes or returns a derivation value, or states `inhabited t`.
  - `preservation`/`call_preservation` return the informative type `pres_result` (or its
    inhabitation). That is at least as strong as Rocq's Prop disjunction.
  - Out's `TPlus m m' \/ (m' = m /\ msr c' < msr c)` is an `either`. The multi-step proof branches
    on it to build a Type-valued result, which Rocq can do from a Prop because its result is a Prop.
  - Two-constructor Props with no recursion become prop disjunctions: `PR`, and `fo` as a
    recursive prop.
- **Prop premises** inside constructors are `squash` fields. The write sets `N -> Prop` are
  `nat -> prop`.
- **Termination.** Fuel arguments are kept exactly as in Rocq (`chk*`, `build_code`, `eq_val`,
  `hash_go`, `show`). Rocq's nested `fix` over lists becomes mutual functions with a list companion,
  proved equal to Rocq's form where Rocq states the generic version (`eq_depth_list_is_list_eq`,
  `eq_val_list_is_eq_list`, `to_value_list_fold`). Lexicographic measures (`%[d; a]`) replace
  Rocq's structural nesting.
- **positive** is `pos`, with the tree recursing on `k/2`. **N** and **nat** are both `nat`.
  Rocq-specific arithmetic (truncated subtraction, `Z.quot` vs `Z.div`, `Z.to_nat` of negatives,
  unbounded bitwise operations) is in `Buri.Lib` and tested against Python's unbounded integers.
- **MEnv** is stated as `forall x, match lookup x g with Some s -> ... | None -> True`, with an SMT
  pattern, where Rocq has `forall x s, lookup x g = Some s -> ...`. The two are the same
  proposition. The two-variable form was not reliably instantiated by Z3 inside larger contexts
  (see findings). For the same reason `slotv` is `unfold`, and `vrp` (VR as a prop, with
  `vrp_of_vr`/`vr_of_vrp`) is used inside MEnv.
- **FunRel** is stated over the machine's function table and heap (`funRel_gh`), which are the
  only machine fields it reads.
- **VRel_unfold and VRelF_index** are pointwise (`vRelF k j w a b <==> vRel j w a b`), where Rocq
  has equalities of relations. Z3 does not prove equalities between function values here.
  KRel_with_ext/ERel_with_ext transport along pointwise equivalence (`equiv_upto`) instead of
  Rocq's `rewrite`.
- **adequacy_statement** uses named `adequacy_pre`/`adequacy_post` with conjoined premises, which
  is the same proposition as Rocq's curried form. Stated inline, Z3 could not match the 5-binder
  quantified statement against the proved instance lemma.
- **JitLowerThm** follows 670d29d, where `Ends` takes the finishing machine `m1` as a parameter.
  JitLowerEquiv needs this form. At the base (4cba179), Ends bound m1 inside its constructors, so
  the second disjunct of `preservation` said nothing about m's run. This port noticed that
  independently; it is ShenJitLowerEndsDecoupled, already fixed on pass/equiv.
- **Section variables** (`sealed`, `D`, `E`, `pt`, the code `c`) are explicit parameters.

## Findings: is F* faster for this project?

1. **Executable spec and judge: yes, if NbE is used.**
   - The 1,351-line bytecode machine ported nearly line for line and checks in 3.4 s.
   - The stage 0 judge gives identical verdicts on all 950 definitions in 147 s wall (28 s for the
     normalization itself), against Rocq's roughly 5 minutes.
   - The default normalizer is about 400 times slower and unusable.
   - Elaborating the large data literals (104 s CPU) is now the dominant cost.
2. **Inversion-style proofs over the emission relation: about the same effort, written very
   differently.**
   - `check_fn_sound` (Rocq: a `crush`/`use` tactic pipeline) became a total function mirroring
     the checker that returns the derivation. It checked almost first try, but the soundness part
     is about 350 lines against about 200 in Rocq (the decision lemmas plus the 145-line
     soundness section).
   - `K_stable` and the `Prim` lemmas were shorter to write and needed no tactics.
   - Check times are small: 70 s CPU for every ported module.
3. **Step-indexed Kripke relation: better than expected, with two kinds of SMT trouble.**
   - Most of JitLowerEquiv's proved implications went through with little effort, and one
     compatibility lemma Rocq leaves open (`compat_type`) was proved in about 70 lines. That
     includes KRel_top, vrefl, store reflexivity, adequacy and the composition with
     call_preservation.
   - The cost is in two places:
     - Z3 does not equate lambdas or function values. Several statements failed until subformulas
       were named: `glob_rel`, `fo_binding`, `bottom_rel`, `adequacy_pre`/`adequacy_post`, and
       pointwise `VRelF_index`.
     - Quantifier instantiation is fragile. MEnv's two-variable form with three existentials
       failed deterministically in one module and passed in another with the same text. It
       needed a restatement with an explicit pattern.
   - Diagnosing each failure took 10 to 30 minutes. The equivalent Rocq step would have been a
     mechanical `rewrite`.
   - Once stated well, all hard modules passed 5 of 5 seeds.

**Overall:** for computation-heavy validation and for definitional or structural proofs, F* looks
faster both to write and to check. For the still-unproved compatibility lemmas the outcome is
still open:
- they are multi-step simulations over a nondeterministic `step_r`;
- the one proved here (`compat_type`) is the easiest, with one step on each side;
- `if` and `let` need continuation-relatedness for pushed frames, as `KRel` for `KIf`/`KLet`
  frames, and those are exactly the quantifier-heavy shapes where Z3 was brittle.

## What remains unported

- **`JitLowerStep.sim`** (Rocq: about 1,100 lines, 75 lemmas such as `step_eval0`, `step_ret`,
  `ret_prim`, `ret_call`, `ret_tail`, `tail_fire`, `ta_start` and `run_moves`). This is the largest
  gap. `preservation`, `related_progress`, `call_preservation` and
  `call_preservation_src_of_fundamental` are proved here only from it.
- **JitLowerEquiv:**
  - The unproved Rocq statements are not ported, not even as definitions: `eq_budget`,
    `jit_eq_per`, `sealed_stable`, `storehas_stable`, `VRel_down`, `VRel_wext`, `ERel_down`,
    `KRef_refl`, `KRef_scope`, and the `compat_*` statements other than `compat_type`.
  - These small helper lemmas are not needed by the ported proofs: `nodup_fst_uniq`,
    `filter_fst_nil`, `GVal_partial`, `VBody_partial`, `leb_S_false`, `SRel_with_wf`,
    `Forall2_refl_env` and `lookup_In`.
  - `fundamental_statement` is defined but not proved, in Rocq or here.
- **Observation.v:** the coinductive part (behaviours, refinement theorems).
- **KLValue:** Rocq's `value_rect'` is not needed and was not ported.

## Effort

- **Wall clock:** about 1 h 55 min of one agent, 11:08 to 13:05 CST, including downloading F*,
  regenerating the pinned stage 0, and the clean timing and seed runs.
- **Tokens:** not measured. A rough estimate is 0.15 M output tokens and about 6 to 8 M input
  tokens processed across the session; most of the input is re-reading the growing context, not
  new reading.
