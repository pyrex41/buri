# E2E-08: the application contract logic BURI/KL-CONTRACT-1

Status: **in progress**. A contract calculus over the formal KLambda
semantics (`KLSemantics.next`, `KLMetatheory`) is defined and every rule is
proved sound. The meaning of each judgment is proved in terms of KLMetatheory
maximal behaviors and of the fuel evaluator `run`. A certificate grammar has a
Rocq checker with universal theorems and a Shen checker. One recursive
higher-order example is proved: it has a mutable global and is transported to
the verdicts of the captured `shen/klambda.shen`. There is no completeness
claim and no decision procedure for validity.

A theorem here is about the formal KLambda semantics, or about the captured
evaluator run by the Native model (the transport). It is not a theorem about
Shen-Scheme, Chez or either port.

## Files

| Module | Content |
|---|---|
| `rocq/ContractLogic.v` | Assertions, modes, semantic predicates, triples, the calculus (`deriv`/`dargs`/`appj`), `soundness`, `rec_partial`, `rec_total`, `total_meaning`, `partial_meaning`, `total_run`, `partial_run` |
| `rocq/ContractPrims.v` | Proved primitive call contracts (`prim_spec_valid`, `io_spec_valid`), `write_byte_visible`, refutations of dropped premises |
| `rocq/ContractExample.v` | The `map` contract derived once, validated by `rec_total`; mutable-counter instance `main_mut` |
| `rocq/ContractTransport.v` | Pure instance in KL-PURE-1, transported to the captured evaluator's verdicts |
| `rocq/ContractCert.v` | Certificate grammar, fingerprint, Rocq checker `check`, universal checker theorems |
| `rocq/ContractCertExample.v` | Ground runs of `check` on the example certificate and on mutants |
| `shen/contract-cert.shen` | The executable Shen checker `buri.contract-check` (acceptance stays in Shen) |
| `tests/contracts.shen` | 19 sampled-agreement cases between the two checkers |
| `tests/mutate-contracts.py` | 7 proof mutations refused by Rocq |

## Assertions and judgments

* **Assertions** are shallow Rocq predicates. A precondition is `store -> Prop`.
  A postcondition is `value -> store -> trace -> Prop` and an exception
  postcondition is `exn -> store -> trace -> Prop`. The `trace` argument is the
  local trace of the expression in the `Observation` vocabulary, so IO
  postconditions see each request/response event, including failed and partial
  writes. Exceptions are postconditions (E), not failures of the triple.
* **Modes.** There are three distinct judgments: `Partial` (partial
  correctness), `Total` (total correctness) and `Always I` (temporal safety:
  every event emitted on every execution satisfies `I`). The semantic predicate
  `G` is the step-indexed `safe` for the two partial modes and the inductive
  "every path terminates" predicate `term` for `Total`.
* **Triple.** `triple m Pre rho e Q E` is stated in continuation-passing form.
  Take any continuation `k` and observer `Phi` that admits the policy's
  resource failures. If returning a value in `Q` (resp. raising in `E`) to `k`
  satisfies `G`, then `Eval rho e` on top of `k` satisfies `G`. Stack framing
  is therefore built in, since every `k` is quantified.
* **Resource failure** is never merged with a result. It is the outcome
  `ResourceOut r` and is admitted only for `r` in the recorded policy `RP`.
  `policy_ok P RP` requires `RP` to cover every limit that the profile `P`
  actually has: stack when `stack_limit P <> None`, heap when
  `heap_limit P <> None`. Going wrong is never admitted, in any mode.
* **Heap assertions use explicit footprints**, in the style of dynamic frames.
  This was a deliberate choice over separation logic. The KLambda heap is an
  append-only list of vectors with integer locations and no deallocation, and
  `=` (`kl_eq`) may read the whole reachable heap. Partial heaps with disjoint
  union would need a heap-splitting model that the semantics does not have.
  A footprint names the locations, global values and global functions an
  expression may change; fresh allocation is always allowed (`agree`). An
  assertion is framed when it is `stable` under `agree`. Rule `r_frame` is
  proved sound.

## Rules (each with a soundness case in `soundness`)

`r_val` (atomic expressions: literals, variables, lambda, freeze),
`r_unbound`, `r_let`, `r_if`, `r_type`, `r_defun`, `r_defun_bad`, `r_trap`
(the handler value is applied to the exception), `r_app`, `r_app0`, `r_call`,
`r_call0`, `r_conseq`, `r_exists`, `r_frame`; argument lists left to right
(`da_one`, `da_cons`); applications `aj_sem`, `aj_ctx`, `aj_partial`,
`aj_lam`, `aj_frozen`:

* `aj_sem`: a semantically established application fact, such as a closure
  parameter.
* `aj_ctx`: a call that saturates a contract of the context.
* `aj_partial`: currying.
* `aj_lam`, `aj_frozen`: closure bodies.

Left-to-right evaluation, lexical environments and exception unwinding come
from the machine. Nothing is inferred from agreement between programs.

**Calls and external operations.** Calls through the global function namespace
are judged against a context of call contracts `cspec`. A contract has a name,
a precondition on the arguments and the store, and relational postconditions
that also receive the pre-call store. Soundness takes `ctx_at m n Gamma`
(every contract in the context is valid) as an explicit premise. Contracts
come in three kinds:

* **primitive contracts** are *proved* (`prim_spec_valid`, `io_spec_valid`,
  for every profile and every mode);
* **user functions** are discharged by the recursion theorems;
* **every other contract** (a host or port operation) remains a named premise.
  The certificate checker reports these premises and never discharges them.

**Recursion.** Partial and total recursion use separate theorems:

* `rec_partial` (modes `Partial` and `Always I`) proves validity at every step
  index by induction on the index. No measure is used and termination is not
  claimed.
* `rec_total` attaches an explicit `nat` measure to each function. Each body is
  derived against `ctx_below`, the context restricted to calls whose measure is
  strictly below the current call's. The proof is by well-founded induction on
  the measure.

Two theorems show that these premises are necessary.
`unmeasured_recursion_unsound` exhibits the self-call loop `f x = (f x)`: its
body is derivable from its own unrestricted contract, but no call terminates.
`if_nonbool_premise_needed` shows the same for `r_if` without its non-Boolean
premise.

## Meaning in KLMetatheory (universal theorems)

* `total_meaning`: take any environment relation that answers every request,
  with any responses (failed and partial writes included), and no pending
  signals. Every maximal behavior of the closed program terminates, with an
  outcome admitted by `top Q E`: a normal value in `Q`, an exception in `E`, or
  a resource failure in `RP`. Exit, kill and cancel are not admitted. At least
  one behavior exists. Divergence, infinite reaction and going wrong are
  excluded.
* `partial_meaning` (modes `Partial`, `Always I`): no behavior goes wrong.
  Every terminating behavior has an admitted outcome. Under `Always I`, every
  event that occurs in any behavior satisfies `I`. This covers terminating,
  diverging and reacting behaviors, through `reacts_events`, which proves that
  every event of an infinite stream occurs in a finite prefix. Termination is
  not claimed.
* `total_run`: with a deterministic environment, `KLMetatheory.run` returns a
  decided `VDone t o` for some fuel, with `o` admitted.
* `partial_run`: every decided verdict is admitted, and `VWrong` never occurs.
  `VExhausted` makes no claim.

## Worked example (universal theorems)

`map f xs` is the KLambda translation `R.tr` of a `klambda.shen` definition.
It recurses over a list and applies the closure `f`. Its contract is
parametric in `f`'s effect, which is one `Step` on the store preserving an
invariant `Inv`. The contract is derived once (`map_body_ok`) and validated by
`rec_total` with the measure "length of `xs`" (`map_ctx_valid`). Two instances
are proved:

* `main_mut` (`ContractExample`). It sets a global counter to 0 and maps a
  closure that reads and writes the counter with `value`/`set`. It returns the
  mapped list paired with the final counter value. `main_mut_behaviors`: for
  every integer list, every profile and every policy covering the profile's
  limits, every behavior terminates. The outcome is
  `(cons (doubled list) (length list))` with an empty trace, or an admitted
  resource failure. There is no exception, divergence or wrong state.
  `main_mut_run` gives the evaluator form.
* The pure doubling instance (`ContractTransport`), whose program is in the
  KL-PURE-1 subset. Composed with `klambda_refines_ext` and
  `klambda_complete`, it gives two theorems about the actual captured
  evaluator run by the Native model:
  * `contract_verdict_sound`: at every budget and fuel, a value returned by
    `buri.eval` is `[unknown evaluation-budget]` or `[returned v]` with `v` the
    doubled list. It is never `[raised ...]` and never `[unsupported ...]`.
  * `contract_verdict_exists`: there is a bound `m` such that, for every
    budget `z > m` and all large enough fuel, `buri.eval` returns exactly that
    `[returned v]`.

  These inherit the E2E-07 boundary. They are theorems about `buri.eval` under
  the Native model, so the Chez-to-Native simulation (E2E07-NATIVE) remains
  open. The `buri.evaluate` guard is not involved.

**Transport blocker.** The mutable instance cannot be transported. KL-PURE-1
(`shen/klambda.shen`) has no `set`/`value`/`absvector`, so no captured
evaluator verdict exists for `main_mut`. This is recorded in
`OB-CONTRACT-TRANSPORT`. The mutable-state contract is a theorem about the
KLambda semantics only.

## Certificates (BURI/KL-CONTRACT-1)

A certificate carries:

* the format;
* the theory identity: the name plus a fingerprint of the rule list;
* the program identity: a fingerprint of the canonical serialization of the
  exact resolved program;
* the captured evaluator identity: `e2e07_klambda` plus the same hash over the
  bytes of `ports/e2e07-klambda.bits`;
* the statement: a name and a mode;
* the declared host contracts;
* the measures;
* one derivation skeleton per body and one for the main expression.

Skeleton leaves are `SHyp` (a declared host contract), `SPrim` (a KLambda
primitive), `SRec` (a function of the program) and `SSide` (a named semantic
side condition). The checker (`ContractCert.check`, `buri.contract-check`)
decides only the following, without proof search, eval or loading:

* identity binding;
* that declarations are distinct and complete;
* that primitive names are known;
* that recursive leaves name program functions;
* that total certificates have measures;
* the exact rule-to-syntax fit.

The verdict is `Accepted stmt premises prims obligations` or
`Rejected reason`. Premises and side obligations are reported, never decided.
The fingerprint is a tamper-evidence aid (polynomial hash modulo 2^61-1), not a
cryptographic commitment.

Proved (universal): `check_identity`, `check_hyps_declared`,
`check_hyps_distinct`, `check_prims_known`, `check_recs_defined`,
`check_total_measures`, `check_shapes`, `check_obligations`,
`stale_program_rejected`, `stale_theory_rejected`, `stale_evaluator_rejected`,
`fits_rule_shape` (a rule node fits only the conclusion form of the calculus
constructor of the same name).

**Correspondence plan:**

1. *Proved:* the Rocq checker's theorems above.
2. *Ground:* `ContractCertExample` runs the Rocq checker on the example
   certificate (accepted) and on mutants: stale program, theory and evaluator;
   undeclared host contract; unknown primitive; missing measure; misfitted
   body. A partial certificate without measures is accepted.
3. *Sampled:* `tests/contracts.shen` runs the same cases against the Shen
   checker. It also covers inputs the typed Rocq input cannot express: forged
   `accepted` labels, malformed certificates and programs, and unknown modes.
   Both checkers compute the same fingerprints (987574484711662929,
   825557597746994086, 1927390069043521096). The suite recomputes the evaluator
   pin from the capture file.
4. *Open:* OB-CONTRACT-CERT-SHEN (capture `shen/contract-cert.shen` and prove
   it computes `check`, as EQ-1 did for `shen/kernel.shen`) and
   OB-CONTRACT-CERT-SEM (an accepted skeleton plus proofs of its side
   obligations yields a `deriv`; this needs a deep-embedded assertion language).

## Reuse of older work

* **`EffectContract.v`** is not reused. It is a contract theory for the Native
  first-order generated-Scheme evaluator: fuelled, immutable environments, no
  closures, heap or continuations. Its approximation and congruence lemmas are
  about `Native.eval_with`, not about `KLSemantics.next`.
* **`Equality.v`** (`check_sound_under_rules`) supplies the pattern used here:
  supplied rules are hypotheses of the soundness theorem, never automatic
  truth. Its term language is not KLambda, so its checker is not reused.
  `OB-EQ-RULE-VALIDITY` is unchanged.

## Evidence, by kind

* **Universal theorems:** everything in `ContractLogic`, `ContractPrims`,
  `ContractExample`, `ContractTransport` and the `ContractCert` checker
  theorems. They are audited in `rocq/Audit_Contracts.v` (59 lines, of which
  12 are ground).
* **Ground derivations:** `ContractCertExample.*`, which are single computed
  checker runs.
* **Sampled agreement:** `tests/contracts.shen`.
* **Identity:** the evaluator pin, recomputed from the capture bytes by the
  Shen suite.

Proof mutations: 7 (`tests/mutate-contracts.py`), each refused by Rocq.

## Open obligations

* **OB-CONTRACT-RULES-COVERAGE.** Rules for `and`/`or`/`cond`,
  multi-argument closure application and over-application, `eval-kl`,
  history-dependent temporal properties, signals/cancellation, and liveness
  under fairness or input-availability premises. Higher-order specifications
  inside step-indexed recursive bodies are also open: `app_sem` facts used by
  `aj_sem` must hold at every index.
* **OB-CONTRACT-CERT-SEM** and **OB-CONTRACT-CERT-SHEN**, as above.
* **OB-CONTRACT-TRANSPORT.** Mutable-state transport, a generic transport
  theorem for every accepted certificate, and E2E07-NATIVE.
* Host contracts named in certificates must be discharged by the port/host
  packages (E2E-14 to E2E-17). Until then they remain premises.
