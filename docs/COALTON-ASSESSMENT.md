# Coalton assessment for the Shen-CL lane

Assessment date: 2026-10-31. “Colton” in the discussion is interpreted as Coalton.

Coalton can improve the engineering of typed Common Lisp tooling. It does not
supply the Rocq preservation theorem connecting Shen, a port implementation,
its host compiler/runtime, and ARM execution. Keep Shen as the application and
specification language, and advance Shen-Scheme and Shen-CL against the same
explicit semantic obligations.

## Decision and repository contract

Coalton is **not adopted** into Búri's implementation or acceptance path.
`AGENTS.md` requires executable semantics, certificate construction, and port
adapters to live in Shen. Rocq independently checks foundational theorems;
evidence is inert data and proof search remains outside the acceptance kernel.

Accordingly, the accompanying optional Coalton experiment is an independent
language/tool assessment. Its toy arithmetic tree is not a Búri evaluator,
reference semantics, certificate format, or port adapter. It creates no Búri
certificate. No global gate or production component depends on Coalton.

Typed syntax trees, metadata, and developer inspection tools are plausible
future uses. Coalton certificate producers or semantic implementations are only
architectural candidates in the abstract: adopting them here would conflict with
the current Shen-only engineering contract. This assessment does not amend that
contract or authorize such a migration.

## What Coalton contributes

Coalton is a statically typed functional language embedded in Common Lisp, with
its own optimizing compiler that emits Common Lisp. Algebraic data types and
pattern matching can make internal tooling more explicit; static checking can
reject some malformed uses before execution. Its Lisp integration also permits
incremental adoption in an existing CL system.

These benefits do not establish application specifications, termination,
capability confinement, effects, semantic preservation, or correctness of the
host implementation. A well-typed tool can implement the wrong algorithm.
Likewise, a candidate proof producer's types cannot substitute for independently
checking the exact theorem and evidence.

Adding a mandatory Shen → Coalton → Common Lisp route would add a translation
boundary and optimization obligations. It would not discharge the existing
Shen → Common Lisp, SBCL/runtime, or machine-code obligations. Do not add that
route for this first verification milestone.

## Interoperation boundaries

The official [interop manual](https://coalton-lang.github.io/manual/topics/lisp-interop/)
distinguishes checked Coalton expressions from raw calls to generated Lisp
functions. Calling a generated function from arbitrary Common Lisp does not
apply Coalton's static checker to the caller.

The `lisp` escape carries a programmer-supplied output annotation. The manual
explicitly declines a guarantee of dynamic type checking at that boundary.
There is an important implementation nuance: the pinned compiler's
[`node-lisp` code generation](https://github.com/coalton-lang/coalton/blob/0b5c10fa14058a9460ee38e69634afa5c5bd10db/src/codegen/codegen-expression.lisp)
emits type assertions when enabled and requests SBCL type checks by default.
The experimental [`unsafe` form](https://coalton-lang.github.io/manual/operators/unsafe/)
can disable generated safety checks. Thus it would be inaccurate to claim that
this SBCL implementation never checks. It would also be inaccurate to turn those
checks into a portable semantic proof. The experiment uses explicit `check-type`
admission for its one integer boundary.

Coalton lists must be homogeneous and non-circular. Arbitrary Shen/Common Lisp
S-expressions do not acquire that property from sharing a cons representation.
A real adapter would need recursive validation and a representation relation,
including improper/cyclic lists, symbols, numbers, closures, mutable objects,
exceptions, and global redefinition as appropriate to its admitted fragment.

Development and release modes can use different representations (including
classes, structures, flattened values, and unwrapped values). Pin mode and
compiler version. Use documented construction interfaces, and do not build
proof assumptions on incidental object layouts. `repr :lisp` offers documented
interop properties but does not establish semantic correctness.

## Observed experiment

The optional [spike](../experiments/coalton/README.md) was actually run with
Coalton commit `0b5c10fa14058a9460ee38e69634afa5c5bd10db`, SBCL
2.2.9.debian on Linux x86-64, in development mode. It observed:

| Check | Result | Evidence kind |
| --- | --- | --- |
| Typed illustrative arithmetic tree | Evaluated to 42 | Single executable example |
| Integer supplied where tree required | `TC-ERROR` at macroexpansion | Negative type-check example |
| String passed to explicit Lisp integer admission | `TYPE-ERROR` | Negative runtime-check example |

The spike specifically catches `TC-ERROR` for its static rejection check;
unrelated compiler errors do not count as success. Dependencies and reproduction
instructions are recorded beside the code. No release-mode, alternative-Lisp,
ARM, or Shen integration result is claimed. These observations do not change
Búri's proven boundary, and no theorem is added by this assessment.

## Next decision point

Continue the two port lanes with shared Klambda semantics, exact source/version
binding, and independent Rocq obligations. The present Coalton result is enough
to retain it as an optional tooling candidate. Before integrating any component,
identify a concrete developer-tooling task that respects the Shen implementation
contract, its admitted input format, and how malformed input is rejected. Measure
its benefit against a small CL or Shen implementation. Keep acceptance validity
independent of the tool's static typing and execution success.

## Primary sources

- [Introduction](https://coalton-lang.github.io/manual/topics/introduction/): language and compiler overview.
- [Interop manual](https://coalton-lang.github.io/manual/topics/lisp-interop/): representations, calling boundaries, modes.
- [Pinned interop source](https://github.com/coalton-lang/coalton/blob/0b5c10fa14058a9460ee38e69634afa5c5bd10db/docs/manual/site/topics/lisp-interop.md): reviewed version of those promises.
- [Unsafe](https://coalton-lang.github.io/manual/operators/unsafe/): runtime-check escape hatch.
- [Debugging](https://coalton-lang.github.io/manual/topics/debugging/): generated-code inspection tools.
- [Coalton in a quantum compiler](https://coalton-lang.github.io/20220906-quantum-compiler/): an existing CL adoption example, not a formal-verification result.
