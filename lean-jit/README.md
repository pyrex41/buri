# lean-jit: pilot port of the Shen/JIT Phase 2 Rocq development to Lean 4

A pilot, to compare effort and check time with Rocq. Base: `shen-jit-phase0` at 4cba179, plus
`rocq/JitLowerEquiv.v` from branch pass/equiv at 670d29d. Branch `pilot/lean`.

## Toolchain

| | |
|---|---|
| elan | 4.2.4 (227caca13 2026-08-25), installed in `~/.elan` |
| Lean | `leanprover/lean4:v4.35.0` (commit eb6cafb7290e), pinned in `lean-toolchain` |
| Libraries | core Lean only. No Mathlib, no Batteries. `JitLowerCheckSound.lean` also imports `Lean.Elab.Tactic` (part of core) for its proof tactic |

Build, one file at a time, single-threaded:

    export LEAN_NUM_THREADS=1
    nice -n 19 lake build LeanJit.<Module>           # one module
    nice -n 19 lake build LeanJit                    # everything (root file LeanJit.lean)
    tools/run_stage0.sh                              # stage 0 judge (see below)

## Axioms

Every ported theorem prints `[propext, Classical.choice, Quot.sound]` under `#print axioms`
(checked for `check_fn_sound`, `next_r_agreed`, `tget_tset_other`, `jit_compare_exact`,
`KD_stable`, `KRel_top`, `store_refl_of_fundamental`, `adequacy_of_fundamental`, `VRel_down`,
`compat_type`, `compat_if`). `canonical_kl_surface` depends on none. There is no `sorry`, no
`axiom` and no `native_decide` anywhere.

The three are Lean's standard axioms. They come in through the tactics (`simp`, `omega`,
`split`, `decide`), not through the statements. The Rocq development uses no axioms, so its
proofs are constructive. These Lean proofs are not, as written. Nothing here was checked for
whether it could be made constructive.

## What was ported, file by file

Check time is the user CPU of `lake env lean <file>`, single-threaded and nice'd, with
dependencies already built. Rocq check times were not measured: the machine was running a large
Rocq workflow, and the `buri-lps` container was off limits.

| Rocq file | Rocq lines | Lean file(s) | Lean lines | Rocq thms | Ported and proved | Left | Lean check | Notes |
|---|---:|---|---:|---:|---:|---:|---:|---|
| Observation.v | 399 | Observation.lean | 65 | 25 | 1 (`star_trans`) | 24, not needed | 0.6 s | Only the vocabulary, `outcome` and `star` are ported. Behaviors, refinement and the determinism lemmas are unused by the Jit files |
| KLSyntax.v | 116 | KLSyntax.lean | 111 | 6 | 6 | 0 | 1.5 s | `expr` is a nested inductive, as in Rocq. `canonical_kl_surface` by `decide` |
| KLValue.v | 214 | KLValue.lean | 212 | 7 | 7 (+2 helpers) | 0 | 0.8 s | `vok`'s `fold_right`s become mutual `vok_env`/`vok_list`. `value_rect'` is not needed: structural recursion over the nested type works directly |
| KLSemantics.v | 387 | KLSemantics.lean | 379 | 0 | – | – | 0.8 s | `parse`'s inline fixes become mutual functions. Its last case is bound by a `let` before the match, to keep the recursion structural |
| KLPort.v | 391 | KLPort.lean | 335 | 24 | 24 (+1) | 0 | 1.7 s | `eq_depth_r_agreed` is a recursive theorem over values |
| JitFloat.v | 224 | JitFloat.lean, ZOps.lean | 211 + 51 | 0 | – | – | 0.5 + 0.2 s | ZOps: `Z.land`/`lor`/`lxor`/`testbit`/`log2`/`shiftl` on `Int`, missing from core |
| JitBytecode.v | 1,351 | JitBytecode1/2/3.lean | 1,335 | 0 | – | – | 4.0 s | Split in three for size. Local `fix`es lifted to top-level helpers |
| JitMeta.v | 144 | JitMeta.lean | 114 | 17 | 17 (+2) | 0 | 1.1 s | The map laws are proved over the `Nat`-keyed trie (see "encodings") |
| JitProfile.v | 190 | JitProfile.lean | 165 | 10 | 10 | 0 | 0.4 s | `vm_compute` becomes `decide +kernel` |
| JitLowerRel.v | 176 | JitLowerRel.lean | 161 | 0 | – | – | 0.6 s | 6 mutual inductive `Prop`s port directly |
| JitLowerCheck.v | 477 | JitLowerCheck.lean, JitLowerCheckSound.lean | 262 + 323 | 22 | 22 (+5), including `check_fn_sound` | 0 | 2.3 + 48 s | See finding 2 |
| JitLowerStage0.v | 50 | JitLowerStage0.lean, tools/stage0_to_lean.py, tools/run_stage0.sh | 58 + 44 + 15 | 0 | – | – | 0.3 s | The emitter reuses the Rocq emitter's tokenizer |
| JitLowerKont.v | 170 | JitLowerKont.lean | 148 | 3 | 3 | 0 | 0.4 s | 4 mutual inductives (`KD`, `TK`, `KC`, `RK`) |
| JitLowerStable.v | 99 | JitLowerStable.lean | 115 | 6 | 6 (+4) | 0 | 1.3 s | `K_stable` is 4 mutual structural theorems over the mutual inductives, not a `Scheme` and `Combined Scheme` |
| JitLowerPrim.v | 176 | – | – | 16 | 0 | 16 | – | Not ported |
| JitLowerStep.v | 1,242 | – | – | 83 | 0 | 83 | – | Not ported, apart from `Sstar` (copied into JitLowerEquiv.lean) |
| JitLowerThm.v | 96 | – | – | 4 | 0 | 4 | – | Not ported: `preservation` and `call_preservation` need JitLowerStep |
| JitLowerEquiv.v (670d29d) | 953 | JitLowerEquiv.lean, JitLowerEquivProofs.lean | 182 + 337 | 52 proved, 38 statements | 28 proved. Statements: the ones the proofs use, plus `compat_if`/`compat_let`/`compat_type` | 24 proved lemmas, about 30 statements | 0.4 + 1.5 s | The `KRef` relation is complete (`world`, `GVal`, `GStore`, `ObsT`, `SRel_with`, `KRel_with`, `ERel_with`, `VBody`, `VRelF`, `KRef`). Proved: runs, worlds, `VRelF_index`, `VRel_ground`, `SRel_ground`, `KRel_top`, `store_refl_of_fundamental`, `adequacy_of_fundamental` |
| (beyond Rocq) | | JitLowerEquivCompat.lean, JitLowerEquivIf.lean | 125 + 101 | – | `VRel_down`, `compat_type`, `compat_if`, all unproved in Rocq | – | 0.5 + 0.4 s | See finding 3 |

Total: about 6,850 Rocq lines in scope, counting Observation, KLPort and the Equiv file. About
4,000 of them are ported completely; on top of that come about half of JitLowerEquiv.v and the
vocabulary of Observation.v. The Lean side is 4,810 lines, including the files that go beyond
Rocq. Checking the whole port takes about 66 s of CPU, single-threaded.
Of that, 48 s is `JitLowerCheckSound`.

`LeanJit/Unported.lean` lists everything not ported. It is comments only, because the
definitions those statements need (`MS`, `Com`, `TN`, `Ends`, …) live in the unported files.

## Stage 0 judge

- **Data.** `generated/stage0` from the release tarball `shen-jit-0.4.tar.gz`. Tag v0.4 is
  d3348ce, the pin the Rocq files name. The tarball's SHA-256 is
  235840a8663a54d4ce671e1144fad3e8efba75a719f51e5705e10821513efd61, which matches the release's
  SHA256SUMS. These are the same 24 file pairs and 950 definitions that `scripts/check-shen-jit.sh`
  reads from `/lps/p4/sj/build/stage0`.
- **Method.** `tools/stage0_to_lean.py` writes one module per file. It imports
  `tokens`/`parse`/`is_number` from `tests/shen-jit/stage0_to_rocq.py`, so both systems trust the
  same reader. Each module ends in
  `theorem counts_ok : counts forms sbc = (A, R, U) := by decide +kernel`, where the numbers are
  that file's row in `tests/shen-jit/stage0-accepted.txt`. The kernel evaluates the parser, the
  loader (`build_code`) and the checker, the same way Rocq's `vm_compute` does.
- **Result.** All 24 theorems check, so the counts match the record exactly: 61 accepted, 889
  rejected, 0 unreadable. A mutation check, changing `types` from `0 7 0` to `1 6 0`, fails as
  expected.
- **Time.** A clean run of all 24 modules took 420 s wall and 405 s user CPU, single-threaded and
  nice'd, with load average about 10 to 12. Rocq's figure is about 5 minutes; the conditions behind
  that number are not known. `init` alone takes 151 s, because of the large
  `shen.initialise-environment`. Elaborating the data is only about 22 s of that.
- **Not usable: `#eval`.** Running `counts` in Lean's interpreter (`#eval`) on `init` had not
  finished after more than 60 minutes, and was stopped. The kernel took about 3 minutes on the same
  file. `native_decide` and `precompileModules` were not tried: the first adds an axiom
  (`Lean.ofReduceBool`), and the second needs a C compile.

## Encodings that differ from Rocq

Each item says whether it changes what a statement means.

- `N` is `Nat` and `Z` is `Int`. `Z.quot`/`Z.rem` are `Int.tdiv`/`Int.tmod`, `Z.div` is `Int.fdiv`,
  and `comparison` is `Ordering`. ZOps defines Rocq's bit operations on `Int`, with two's-complement
  meaning. The meaning is the same.
- **`positive`.** It becomes `JitBytecode.Pos`, a structure holding `p - 1 : Nat`. That is a
  bijection, so every map law keeps its Rocq statement (`tget_tset_other` needs only `k ≠ j`). The
  trie functions take the key's value: 1 is xH, even is xO, odd is xI. `tset` recurses on a fuel
  equal to the key, because halving is not structural on `Nat`. The point of all this is that keys
  and symbols compute with the kernel's GMP `Nat`. A binary inductive would make the stage 0 judge
  far slower in the kernel. The meaning is the same.
- **Local recursion.** Rocq's nested local `fix`es are lifted to top-level functions, given what
  they close over: `eq_depth`/`eq_val`'s inner loop, `hash_walk`, `show_tail`, `dec_exp_up`,
  `deref_go`, and the dictionary helpers. `vok`, `vars`, `GVal` and `VBody` become mutual
  definitions for their list parts. The functions compute the same thing.
- **Lists.** `Forall P l` is `∀ x ∈ l, P x`, and `NoDup` is `List.Nodup`. Core Lean has no
  `Forall2`, so JitLowerEquiv defines its own. These are equivalent.
- **Implicit variables.** The constructors of `Comp`/`CompT`/…, `KD`/`TK`/`KC`/`RK` take their
  variables implicitly, where Rocq takes them explicitly. The hypotheses and their order are
  unchanged.
- **Strings.** `of_string` and `t` map `Char.toNat` over the string. This is the same as Rocq's
  byte strings for the ASCII literals used. The stage 0 `XSym` carries a Lean `String`, as Rocq's
  does.
- **Unused constants.** JitBytecode's `S_*` symbols that nothing references are omitted.
  `KLPort` keeps its own copy of the `=` loop (`eq_go_r`), as Rocq does, so drift still breaks
  `eq_depth_r_agreed`.
- **Counts statement.** `JitLowerStage0.counts` is `tally` without the name list, which is what
  the kernel theorem states.

No positivity, universe or `Prop`/`Bool` problems came up. Nested inductives (`expr`, `value`,
`code`), the mutual inductive predicates, and structural recursion over all of them were
accepted as written.

## Findings: would Lean be faster for this project?

1. **Kernel computation is competitive, but only through the kernel.** The full stage 0 judge,
   with a soundness theorem behind it, took 405 s of CPU against Rocq's reported 5 minutes. That
   relied on encoding `positive` over GMP `Nat`. The interpreter is not an option: `#eval` was more
   than 20 times slower than the kernel. The fast compiled route (`native_decide`) costs an extra
   trusted axiom.
2. **Specification code ports almost line for line, and checks fast. Ltac-style proofs need
   tooling.** The trusted slice (about 3,000 Rocq lines) ported at about 1:1 lines, mostly
   compiling first time, and checks in seconds. The one Ltac-heavy proof, the checker's soundness,
   took most of the debugging. Core Lean has no `match goal`, so Rocq's `crush`/`use` became a
   70-line meta tactic (`use_all`). It needed three fixes, each worth knowing:
   - elaborate at reducible transparency, or unifying `chkW …` with `chk …` unfolds both and
     times out;
   - turn off error-to-`sorry`, or a failed `by assumption` "succeeds" with `sorry`;
   - split conjunctions with `MVarId.cases`, not `obtain`.

   After that, the proof checks in 48 s. That is the slowest file of the port.
3. **The logical relation was easier to extend than expected.** `KRef` and its machinery ported
   directly. `adequacy_of_fundamental` and `store_refl_of_fundamental` compiled after one round of
   fixes. Then three statements Rocq leaves unproved went through quickly:
   - `VRel_down`, the downward closure of the index;
   - an anti-reduction lemma for `ObsT` (one internal step on each side, with the target's
     resource raise matched by the source's);
   - `compat_type` and `compat_if`.

   Together that is about 230 lines, with no file needing more than three build attempts. The
   automation that did the work was `simp`, `omega`, `cases … <;>` and structural recursion; no
   `grind` or `aesop` was needed. One caution: compatibility in a simple case, where both sides
   take one step, is not evidence for the hard ones (call, app, trap, lambda). Those need
   `VRel` monotone in the world and the `=` budget lemma.

On balance: for the spec and checker, Lean was not slower to write, and it is fast to check. The
stage 0 run costs about the same. The cost is that Ltac-style automation over big generated
case splits has to be built in Lean's meta language. The big unported piece is the simulation
(JitLowerStep, 1,242 lines of Ltac), and that is where this would matter most.

## What remains unported

- `JitLowerPrim.v`, `JitLowerStep.v` and `JitLowerThm.v`: the simulation, `preservation` and
  `call_preservation`. That is 1,514 lines and 103 theorems.
- In `JitLowerEquiv.v`:
  - `call_preservation_src_of_fundamental` (needs `call_preservation`);
  - `GVal_trans` and `GStore_trans` (with `compose_world`/`wf_compose`);
  - the premise checks and their specifications;
  - the compatibility statements other than `if` and `type`;
  - the `eq_budget`, `sealed_stable` and `storehas_stable` statements.
- Most of `Observation.v`.

## Effort

- Wall-clock: 11:18 to about 15:45 CST on 2026-11-09, about 4.5 h. That includes two outages
  (an API error and a network loss) and long waits under a load average of 25 to 33 for most of
  the session. Early on, starting a Lean process alone took about 90 s wall.
- Tokens: not metered. A rough estimate is 1 to 1.5 M tokens processed and 150 to 200 k
  generated.
