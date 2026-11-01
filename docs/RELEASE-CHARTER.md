# Release charter and obligation graph (E2E-01, E2E-02)

This page describes three machine-readable files and the Shen checker that
reads them. None of the three is proof evidence. A checker verdict of
`ledger-consistent` means the bookkeeping rules below hold. It does **not**
accept any theorem. Only `make prove` decides theorem validity.

| File | Content |
|---|---|
| `spec/release-charter.json` | Charter v1: pins, endpoints, threat model, semantics targets, property definitions, required features, excluded extensions, version history |
| `spec/obligations.json` | Obligation graph: 97 obligations with stable IDs, two joint invariants, and a map from the older `buri.obligations` inventory |
| `spec/end-to-end-plan.json` | The existing 36-package plan. Its package IDs are the only valid owners |
| `shen/ledger.shen` | Inert JSON reader, coverage/closure rules, and the frozen charter fingerprint registry |
| `tests/ledger.shen` | Enforcement tests for provisional exclusions, the real-ledger check, and hostile variants (`make test`) |

## Charter v1 (frozen 2026-11-01)

**Target endpoint:** closed deployment on both ports. The plan's three endpoints
(language/port, hosted ARM process, closed deployment) are recorded separately.
Reaching an earlier endpoint does not complete the charter.

**Pins.** The charter records only facts that already exist in the repository.
The table states its status honestly:

| Pin | Status | What is recorded |
|---|---|---|
| Shen kernel | identity-only | 43.1, checked through the `*version*` string; embedded in the host archive. No hash of the kernel source tree |
| PR117 overlay | pinned | `ec16a9fa…/sources/t-star.shen`, sha256 `480e26c6…`, checked on every launch |
| Shen-Scheme release | pinned | v0.52 archive hashes for linux-x64 and macOS-arm64 only |
| Shen-Scheme source | pinned | `8d261518…` plus three blob IDs. These are review targets; no build relation is proven |
| Chez Scheme | identity-only | Bytes are fixed by the archive hash. **The Chez version/revision is unrecorded** |
| Shen-CL source | pinned | `4844072d…`, for the guard capture gate only. Not in `toolchain.lock.json`; no CL binary is pinned |
| SBCL | **unpinned** | Must be selected by E2E-03/E2E-23. The gate uses whatever SBCL is on `PATH` |
| Rocq | pinned | Coq 8.18.0, OCaml 4.14.1, `rocq-packages.lock` |
| ARM architecture revision, ABI, CPU features | **unpinned** | Must be selected by E2E-20 |
| OS/runtime profile | **unpinned** | Must be selected by E2E-20/E2E-31 |
| Linux AArch64 host archive | **unpinned** | `scripts/bootstrap` supports only Linux x86_64 and macOS arm64. The macOS-arm64 archive is not the target profile |
| Compiler modes (Chez optimize/safety, SBCL policy, boot flags) | **unpinned** | Must be recorded by E2E-03 |

The checker rejects an `unpinned` record that carries a value
(`invented-pin-value`). Every non-pinned record must name a closure package.

**Property kinds.** Each kind has its own definition and a separate
`not_implied_by` statement: functional correctness, memory safety, confinement,
termination, liveness, confidentiality and resource adequacy. Termination is
never inferred from fuel results, and liveness is never inferred from
termination. Each kind names a semantics target and an owning package.

**Features.** There are 74 required features: KLambda and Shen constructs,
primitive families, kernel library modules, effects, numeric and encoding
policies, concurrency modes, compiler modes and platform layers. Features are
listed whether or not any checker handles them today. Each feature names one
of 26 semantics targets (`SEM-*`), and each target has an owning package.

Sixteen features are **provisional exclusions**. Each exclusion names
enforcement tests and a closure package. The checker verifies that every named
test is registered as `(buri.test NAME …` in its file; `make test` runs the
tests. Most exclusions are enforced only by the BURI/KL-PURE-1 reference
admission (`buri.expression?`), and one is enforced only by the sealed capsule.
The native ports do **not** enforce these exclusions: stock Shen-Scheme runs
everything. That gap is `OB-HOST-EXTENSION-ADMISSION`.

**Excluded extensions** (scm./lisp. FFI, StLib) are outside the required set.
Each one names either enforcement tests or a tracked enforcement-gap obligation.

**Minimal experiment.** The charter records the minimal experiment as
`is_final_coverage: false`. It is blocked on the six unpinned platform/SBCL pins.

## Fingerprint and version rule

The required set is the list of `feature:`, `property:` and `pin:` IDs. Its
fingerprint is an order-independent sum, modulo 2^61−1, of polynomial byte
hashes, computed in Shen using exact integer arithmetic. Charter v1 has the
fingerprint `lh61:95:414996911908889189`. The checker rejects the charter when:

- the recorded fingerprint differs from the computed one;
- the current required set differs from the latest history entry;
- a history step drops an ID without a `removed` record (`silent-feature-removal`);
- the computed fingerprint is not the frozen row for this version in
  `buri.ledger-frozen-charters` (`shen/ledger.shen`).

The last rule means a data-only edit can never change the required set. This
holds even if the history and recorded fingerprint are rewritten consistently,
because the frozen row will no longer match. Any such change needs a new
charter version and a reviewed code change. The fingerprint is tamper evidence,
not a cryptographic commitment. Someone with write access to `shen/ledger.shen`
can still add a row; review is the control.

## Obligation graph

Each obligation records the following fields: `id`, `kind`, `scope`
(universal/instance), `owner` (an E2E package), contributing `packages`,
`status`, `boundary`, exact `identity`, `statement`, `premises`, `depends_on`,
`evidence`, `completion_evidence`, `sources` and `history`.

`kind` is one of four separately tracked categories:

- model proof;
- implementation correspondence;
- artifact correspondence;
- deployment identity.

`status` is one of:

- open;
- partial;
- assumed (an explicit trust assumption);
- discharged;
- refuted (needs counterexample evidence and `replaced_by`);
- superseded;
- foundation.

A foundation obligation must name one of the plan's four `ultimate_foundations`.
Foundations are never closed as tickets.

The sources harvested are TRUST, TRUST-AUDIT, SIX-STAGES (with
`spec/six-stages.json`), STATUS, PORTS, SCHEME-PORT, CL-PORT and the plan.
Older statements are kept under `history` with a reconciliation note, not
deleted. Examples:

- "negative denominators outside the ratio profile" is kept with the later
  signed-normalization theorem;
- "ps metadata identifies code" is kept as a refuted obligation with its
  counterexample test;
- "unrestricted native halving" is kept as refuted and replaced by the
  byte-domain obligation.

Every entry of the old static `buri.obligations` inventory in `shen/claims.shen`
maps to a current obligation.

Counts at freeze:

| Status | Count |
|---|---|
| discharged | 8 |
| partial | 24 |
| open | 46 |
| assumed | 13 |
| refuted | 2 |
| foundation | 4 |

All eight discharged obligations are model proofs with no dependencies. For
example, the reference arithmetic compiler, wire codec, tagging protocol,
capture decoding, congruence admission and evaluator/instruction-machine core
equivalence are model results only. None of them is a port or implementation
claim.

**Joint invariants.** Two cycles are real and are tagged:

- `JI-HEAP`: GC correctness and the mutator heap invariant;
- `JI-BOOTSTRAP`: Shen checkers running on the host they validate, and host
  output validation.

A cycle is allowed only when every member of its strongly connected component
carries the same declared joint invariant. Members of a cycle, and the joint
invariant itself, can never be discharged. A joint invariant's member list must
equal its tagged set. The package plan must be acyclic.

## Checker rules (all decided in `shen/ledger.shen`)

**Coverage:**

- every obligation, feature, property, semantics target, joint invariant and
  non-pinned pin has an existing owner package;
- every package owns at least one obligation;
- every `depends_on` resolves, for both obligations and packages;
- all referenced source and evidence files exist.

**Evidence kinds:**

- `universal-theorem`, `ground-derivation` and `instance-validation` must cite
  a name that has a `Print Assumptions` line in `rocq/Audit.v`;
- a universal obligation is discharged only by a `universal-theorem` item whose
  `establishes` field equals the obligation's kind;
- an instance obligation also admits ground derivation and instance validation
  evidence;
- a deployment-identity instance obligation also admits identity hashes;
- `sampled-agreement`, `exhaustive-host-test`, `review` and `counterexample`
  never discharge anything.

**Closure:**

- a discharged obligation cannot depend on anything except discharged or
  foundation obligations;
- a `complete` package needs evidence, complete dependencies, and every owned
  obligation discharged, superseded or foundation;
- `full_plan_complete` needs every package complete.

**Distinct outcomes:**

- `ledger-consistent`;
- `rejected` with a list of violations;
- `malformed` (JSON or shape failure);
- `unsupported-schema`;
- `unknown host-error` (for example, a missing file).

**Inert input.** Ledger files are read with `read-file-as-bytelist` and parsed
by a small JSON reader. That reader admits integers only, rejects duplicate keys
and trailing data, and keeps `\uXXXX` escapes as literal text. No ledger byte
reaches `load`, `eval`, `read-from-string` or macroexpansion. Python is not
involved.

## What this does not establish

These limits apply:

- The checker confirms only that a theorem *name* is audited. It cannot confirm
  that the theorem states the obligation. The `establishes` field and `kind`
  are author-declared labels, so semantic fit needs review (E2E-36).
- The completeness of the harvest is a manual review claim. The checker can
  verify only the items that are recorded.
- The checker itself is unproved (`OB-LEDGER-CHECKER`); it is regression-tested
  only.
- The enforcement tests sample the reference admission. They are not proofs,
  and they say nothing about stock native ports.
- E2E-01 and E2E-02 remain **in progress**:
  - six platform/toolchain pins are unselected;
  - Chez and kernel source identities are unrecorded;
  - exclusions are not enforced on native admission paths;
  - the harvest has not had independent review.
