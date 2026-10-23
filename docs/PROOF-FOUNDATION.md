# Decision: Shen execution, Rocq foundation

## Decision

Use Rocq for the independent semantic theorems and checker soundness. Keep
executable domain definitions, proof certificates, and port adapters in Shen.
The user explicitly opened the choice of Rocq, Lean, or another proof language
during implementation; Rocq is now part of Búri's foundation, not an optional
badge attached after testing.

Rocq is suitable because this work is predominantly operational semantics,
induction, representation invariants, compiler simulations, and checker proofs.
CompCert is an established example of this approach:
https://compcert.org/man/manual001.html
https://compcert.org/doc/

Lean also has a small proof kernel and would support these theorems. It was not
rejected on logical grounds. Maintaining both would add another correspondence
boundary before either is connected to the real Shen runtime. We choose one.
https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/

The initial reproducible toolchain uses Coq 8.18.0, a pre-rename release of Rocq,
because its binaries and dependencies can be pinned and independently replayed
here. This is a tested compatibility pin, not a claim that it is the latest
release. Future upgrades must replay all proofs and the assumption audit.

## What this does and does not buy

A proof accepted only by a Shen checker depends on the Shen implementation under
investigation. Rocq removes that dependency for the formal-model theorem. It
does not automatically prove that Shen executes the formal model. That bridge
must be explicit and is a first-class work item.

Native compiler-output validation adds quantified proofs of selected actual
source/output pairs. The required raw-capture path now defines semantic decoding in Rocq and proves
lexical resolution and normalization. It still requires capture provenance and
lower-runtime correspondence.

The encoder adds a source-linked program proof: its exact Shen file is checked
against a canonical rendering, and its abstract executions have termination,
unique-output, and decoding round-trip theorems. Native reader/compiler and
primitive/runtime refinement remain explicit obligations. See [ENCODER](ENCODER.md).

The arithmetic equation bridge checks every exported equation and the exact
theorem conclusions. It does not yet prove the exporter or the Shen normalizer.
The Rocq equality checker has its own soundness theorem; its connection to the
Shen rewrite/induction checker remains open. This is deliberate transparency,
not permission to leave the bridge implicit in a future release.

## Root policy

- No `Admitted`, custom axioms, or native-computation trust shortcuts in released
  closed theorems. Explicit environmental premises are allowed and must appear
  in the claim, not be hidden in an assumed lemma.
- Audit exact theorem types and `Print Assumptions` outputs. Recheck `.vo` files
  with `coqchk` in addition to compiling proof scripts.
- Source/definition changes invalidate affected bridge results and admissions.
- Re-prove optimizations and compiler transformations against the same semantics.
- Keep the business specification in Vör. Búri formalizes the language machinery
  needed to execute it, rather than duplicating each business algorithm in Rocq.
