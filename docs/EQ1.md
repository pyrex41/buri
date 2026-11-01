# BURI/EQ-1 checker correspondence

This note records what is proved about the original EQ-1 acceptance kernel
(`shen/kernel.shen`, sorted rewriting plus structural induction over `expr`)
and what is still open. Package: E2E-09, first item.

## Capture and lineage

The kernel and every helper it calls are captured from the pinned Shen-Scheme
image with the existing provenance machinery (`buri.observe-constructor`): each
source file is compiled by the loaded compiler, the target Scheme forms are
evaluated (so the captured code is what runs afterwards), and the forms are
written as typed wire bits. There is one capture per source file:

| profile | source | capture | Rocq input |
| --- | --- | --- | --- |
| `eq1_base` | `shen/base.shen` | `ports/eq1-base.bits` | `EqualityInductionBaseInput` |
| `eq1_equations` | `shen/equations.shen` | `ports/eq1-equations.bits` | `EqualityInductionEquationsInput` |
| `eq1_theory` | `spec/arithmetic.shen` | `ports/eq1-theory.bits` | `EqualityInductionTheoryInput` |
| `eq1_kernel` | `shen/kernel.shen` | `ports/eq1-kernel.bits` | `EqualityInductionKernelInput` |

`make prove` regenerates all four, diffs bits, transcript and source copy
against the checked-in files, repackages them (the literal is split into
ordered 40000-character chunks because a single literal overflows Coq's
parser; `check-provenance-package.py` checks the chunk order and the exact
concatenation), and Rocq decodes every definition of each file (`*_exact`,
`*_complete`, `*_names`). Python only moves bytes.

Runtime functions that are not captured are explicit contracts, as in EQ-2:
`kl:=`, `kl:_scm.assert-boolean`, `kl:symbol?` and `kl:str` are the pinned
helper templates of `NativeHelpers`; `kl:not` is the contract
`(if x #f #t)` (Scheme `not`). `kl:=` is modelled by `equal?` (`same`); the
runtime's numeric `=` also identifies `1` and `1.0`. Well-sorted EQ-1 terms
contain no numbers, so this cannot change which sorted equations are accepted,
but it is a stated contract difference, not a theorem. `trap-error` compiles to
a Chez `guard` whose handler is the literal `[rejected malformed-evidence]`; the
Native evaluator has no `guard`, so only the guard's body and its handler
syntax are reasoned about.

## Evidence, by kind

Universal theorems (all axiom-free, listed in `rocq/Audit.v`):

* `EqualityInductionOracle.eval_oracle` — for any decoded program, every value
  the actual Native evaluator returns is the value of a fuel-free oracle
  semantics built from the same bodies.
* `EqualityInductionSpecs` / `EqualityInductionHelpers` — the captured code of
  `member? unique? append rev rev-h get keys remove nat? all-symbols? sig
  signature constructors rules theory sort sort-app args? context-h? context?
  subst substs subst-var rule fresh? zip zip-h variables induction-hyps resolve
  replace-head replace-tail replace-app` computes the reference functions of
  `EqualityInductionModel` (partial correctness over arbitrary raw values:
  decoding, exact shape tests, malformed input, variable binding and theory
  lookup included). `native_*` restate several of them for `Native.run`.
  `ask_rules`/`ask_theory` pin the captured theory data to the literal
  `rules_value`/`theory_value`.
* `EqualityInductionModel` — standard model of BURI/ARITH-1 (Arithmetic.v),
  `rules_value_true` (all 18 definition rules are true), `sort_sound`,
  `subst_sound`, `replace_sound`, `substitution_env`, `instance_sound`,
  `branch_sound` and `induction_sound` (structural induction over `expr`,
  with hypotheses generalised over the other variables).
* `EqualityInductionKernel` — a reference kernel `r_check_bundle` mirroring
  `kernel.shen` clause by clause, and `check_bundle_sound`: if it accepts, the
  theory equals the loaded theory value and every listed theorem has a
  symbol name, passes `goal?`, and is `valid` (both sides denote, and denote
  the same value, under every well-typed assignment). `stale_theory_rejected`,
  `false_lemma_never_accepted` (no accepted output, however forged, contains
  `x = succ x`), and verdict lemmas (`steps_verdict`, `cases_verdict`,
  `theorem_verdict`: the drivers never produce an acceptance label).

Ground derivations (vm-checked on the actual captured Native program):

* `acceptance_excludes_search`, `acceptance_closed`,
  `acceptance_reaches_drivers` — the transitive call graph of the captured
  `check-bundle` contains no normaliser, matcher, `eval` or loader; every
  callee is captured code, a runtime contract or a primitive.
* `sample_accepted`, `sample_injected_rule`, `sample_forged_label`,
  `sample_ill_sorted` — the captured `bundle-h` accepts a correct direct proof
  and rejects a `[definition trust-me]` injection, an input containing a
  forged `[accepted ...]` label, and an ill-sorted theorem.

Sampled agreement: `samples_agree` (the captured `bundle-h` and the reference
kernel agree on those four bundles). This is not a refinement theorem.

Proof mutations (`tests/mutate-eq1.py`): a reference kernel without the
conclusion check, without freshness, without the theory check, a model with an
injected false definition rule, and induction hypotheses for `nat` arguments
are each refused by Rocq.

## Open obligations

* **EQ1-DRIVERS**: prove that the captured recursive drivers (`check-steps`,
  `check-step-result`, `after-rewrite`, `check-cases`, `check-case-bound`,
  `check-theorem`, `bundle-h`, `bundle-next`, `check-bundle`) and the helpers
  `substitution?`, `instantiate`, `replace`, `replace-arg`, `goal?` refine the
  reference kernel. The symbolic executor used for the helpers produces
  proof terms whose kernel check (`Qed`) did not finish within ~10 minutes
  for `substitution?`; the drivers are larger. Until this is closed, the
  soundness theorem is about the reference kernel and sampled agreement is
  the only link to the captured drivers.
* **EQ1-GUARD**: a semantics for the Chez `guard` produced by `trap-error`
  (the handler syntax is fixed; its semantics is not modelled by Native).
* **EQ1-NUMERIC**: `kl:=` numeric equality and `buri.nat?` digit-spelling are
  stated contracts (the reference kernel takes any non-negative integer
  budget). The `kl:=` half is narrowed by E2E-17:
  `SchemeWrappers.stock_matches_replacement` proves that the stock pinned
  `kl:=` equals the `equal?` replacement used here on first-order data, under
  named Chez contracts ([PRIMITIVES](PRIMITIVES.md)). The two differ on mixed
  exactness, which lies outside the proved data fragment; that EQ-1 inputs
  stay inside the fragment is not yet proved. The digit-spelling half remains.
* **EQ1-TERM**: termination of the captured kernel on finite certificates is
  not proved (the reference kernel is total by construction).
* Chez-to-Native simulation, as for every Native result (E2E-32).

Thornet/Vör proof search is outside acceptance: nothing in the captured
call graph reaches search (`acceptance_excludes_search`), and search output
enters only as an inert bundle that the kernel checks.
