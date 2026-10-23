# Búri engineering contract

Build language implementation correctness, not a relabelled test suite.

- Executable semantics, certificate construction, and port adapters live in
  Shen. Rocq independently checks foundational theorems. Shell/Python may
  orchestrate processes and package bytes; they must not decide theorem validity.
- Keep proof search outside the acceptance kernel. Evidence is inert data.
- Bind every claim to its exact theory, source, dependencies, and assumptions.
- Never add an axiom or weaken a theorem to turn a failed proof green.
- A ground derivation, sampled agreement, and a universally quantified theorem
  are different evidence kinds. Reports must retain that distinction.
- Unknown, unsupported, exhausted resources, and rejected evidence are distinct.
- Preserve left-to-right evaluation, lexical scope, exceptions, and numeric
  semantics explicitly; never infer them from agreement between two programs.
- A theorem about the reference compiler is not a theorem about Shen-Scheme.
- Run `make test` and `make prove`. Run `make conformance` when changing the
  reference evaluator, port adapter, or primitive contracts.
- Keep the proof kernel small. No arbitrary loading/eval in artifact checkers.
- Update docs/STATUS.md whenever the proven boundary changes.
