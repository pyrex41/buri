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

## Captured drivers refine the reference kernel (EQ1-DRIVERS, closed)

Universal theorems, axiom-free, about the bodies decoded from
`ports/eq1-kernel.bits` (`EqualityInductionDrivers`, `EqualityInductionRefinement`):

* Technique. Each captured body is evaluated once, symbolically, under an
  abstract call oracle `o` constrained only by the partial-correctness
  contracts of its callees (section hypotheses). Branch positions are wrapped
  in an identity marker `hide` so that strong reduction only expands the
  current evaluation frontier; tests split on their boolean outcome and learn a
  variable's shape only when the test succeeds; name comparisons stay folded
  (`simpl nomatch`) and a successful comparison with a literal substitutes the
  literal. `step_agree` replaces the program's name table by a three-character
  test equal to it on every called name (vm-checked per body). Leaf goals
  split only on variables and literal name comparisons, so a false leaf fails
  quickly. Proof terms stay small: the whole module (20 bodies) checks in
  about three minutes on one core, the largest body (`replace`) in under a
  minute including `Qed`; `EqualityInductionRefinement` checks in seconds.
* `body_cb` (guarded body of `check-bundle`), `body_bundle`, `body_next`,
  `body_goal`, `body_theorem`, `body_cases`, `body_bound`, `body_steps`,
  `body_csr`, `body_after`, `body_inst`, `body_substn`, `body_replace`,
  `body_rarg`: for every input, if the body returns a value, it is the
  reference value (`r_check_bundle`, `r_bundle`, `r_goal`, `r_theorem`,
  `r_cases`, `r_steps`, `r_inst`, `r_substitution`, `r_replace`, `r_rarg`, or a
  one-step fragment `next1`/`bound1`/`csr1`/`after1` of those functions).
* EQ1-NUMERIC for `buri.nat?`: `body_str`, `body_digits`, `body_unsigned`,
  `body_ispell`, `body_exact`, `body_nat` and `spelling_ok` prove that the
  captured `nat?` (through `exact-integer?`, `integer-spelling?`, `digits?`
  and the pinned `kl:str` template) returns exactly `0 <= z` on an integer and
  `false` on non-numbers; on non-integer numbers it never returns.
* `EqualityInductionRefinement.drivers`: by induction on oracle fuel, all of
  the above hold for the oracle of the actual program at every fuel. The
  `native_*` corollaries restate them for `Native.run`
  (`native_bundle`, `native_steps`, `native_theorem`, `native_cases`,
  `native_instantiate`, `native_substitution`, `native_replace`, `native_goal`,
  `native_nat`).
* `captured_bundle_sound`: if the captured `bundle-h`, run by the Native
  evaluator on `[B;[];Integer z]`, returns `[accepted generic-equations out]`,
  every entry of `out` is valid in the standard model.
* `check_bundle_captured` pins the captured `check-bundle` body to
  `guard [handler; g_cb]` with the literal handler `[rejected malformed-evidence]`.
  `guard_model` is the stated contract for that guard (a raised error becomes
  the handler value, anything else passes through). Under it,
  `captured_check_bundle_refines` (the result is the reference verdict or the
  handler's rejection), `captured_check_bundle_sound` (acceptance implies the
  loaded theory and validity of every output theorem) and
  `captured_false_lemma_never_accepted`.

These are partial-correctness statements: they constrain every value the
Native evaluator returns; they do not say a value is returned.

Driver mutants (`tests/mutate-eq1.py`): a captured `check-steps` without the
conclusion check, `check-step-result` with swapped rewrite directions,
`check-cases` without the freshness test, `check-bundle` without the theory test, and a
`check-bundle` guard whose handler accepts are each refused by Rocq.

## Termination: total correctness under Native (EQ1-TERM)

Universal theorems, axiom-free, about the same decoded program
(`EqualityInductionTrace`, `EqualityInductionTotalBase`,
`EqualityInductionTotalTerms`, `EqualityInductionTermination`; audited in
`rocq/Audit_Termination.v`).

* Technique. `stepT` runs one captured body against the reference call table
  `oref` and records every program call with the value the reference function
  gives. `traced` (generic): if that run succeeds and every recorded call
  terminates under the actual `Native.run` with the recorded value, the body's
  Native evaluation terminates with the same value. Each captured body is run
  once symbolically, with the same lazy-branch technique as the drivers
  (`hide`, tests split on their outcome, shapes learnt on success, `eq?`
  against a literal kept as a two-way test). Recorded calls are discharged by
  the termination lemma of the callee, or, for recursion, by the structural
  induction hypothesis (`vind`) on the step list, case list, theorem list,
  path, argument list, term or string the run has exposed. Partial
  correctness (`EqualityInductionRefinement`, `Specs`, `Helpers`) supplies the
  value.
* Domains. The Shen code has helpers without a fallback clause (`member?`,
  `get`, `rule`, `subst`, ...); they are only called on data the kernel has
  validated. The predicates `lst`, `kv`, `tm`, `wfr`, `zok`, `sigok` describe
  that data and are propagated (`goal_ok`, `kv_app`, `wfr_ihyps`,
  `rl_resolve`, `substitution_kv`, ...). The only condition on the input is
  `idata` (no fractions or inexact numbers anywhere in the bundle) and
  `numok` on the budget: Native's number primitives are integer-only.
* `ok_*` (per captured function): terminates with its reference value on its
  domain, e.g. `ok_member`, `ok_nat`, `ok_sort`, `ok_ctx`, `ok_subst`,
  `ok_substitution`, `ok_inst`, `ok_goal`, `ok_replace`, `ok_steps`,
  `ok_cases`, `ok_theorem`, `ok_bundle`. The four argument-free theory
  constants are ground computations of the actual evaluator.
* `native_guarded_body_total`: for every `T`, `B`, `N` with `idata B` and
  `numok N`, there is a fuel `n` such that for every `m >= n` the Native
  evaluation of the captured guarded body returns `r_check_bundle T B N`.
  `captured_check_bundle_total`, `captured_check_bundle_decides` (under
  `guard_model`: the captured check-bundle always decides, with the reference
  verdict, and what it accepts is valid in the standard model),
  `native_bundle_total`, `native_steps_total`.
* Ground derivation (not universal): `fraction_budget_unsupported`; with the
  loaded theory and budget `1/2` the Native evaluation is `Unsupported`
  (Chez would raise inside the guard and reject), so `numok` is necessary for
  the Native statement.

Mutants (`tests/mutate-termination.py`): a `member?` whose recursive call
passes the whole list, linked into the program, fails the inductive
termination step whose unmutated control is accepted; dropping the budget
condition is refused.

Per-module times on this machine (shared, 4 cores): Trace 3 s, TotalBase
~35 s, TotalTerms ~150 s, Termination ~215 s.

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

* **EQ1-GUARD**: the Chez `guard` produced by `trap-error` is modelled only by
  the stated contract `guard_model`; Native has no guard. That Chez's guard
  behaves this way is not proved.
* **EQ1-NUMERIC** (remaining): `kl:=` is modelled by `equal?`; the runtime's
  numeric `=` also identifies `1` and `1.0`. Well-sorted terms contain no
  numbers, but this is a stated contract difference. (`nat?` is now proved.)
* **EQ1-TERM**: proved under the Native evaluator for integer-only inputs (see
  below). Remaining: inputs with non-integer numbers are outside the Native
  numeric model, and the fuel bound is existential, not a closed formula.
* Chez-to-Native simulation, as for every Native result (E2E-32). A theorem
  about the Native evaluation of the decoded capture is not a theorem about
  Chez executing it.

Thornet/Vör proof search is outside acceptance: nothing in the captured
call graph reaches search (`acceptance_excludes_search`), and search output
enters only as an inert bundle that the kernel checks.
