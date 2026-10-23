# Port preservation contracts

## First target: Shen-Scheme / Chez

Pinned upstream source: `tizoc/shen-scheme` at
`8d261518db17fbfec32d1b268b40ed216b925c74`.
The toolchain uses v0.52 / Shen 43.1 and a hash-checked kernel PR #117 overlay.
Source blob identities are in `toolchain.lock.json`. Binary/source equivalence
has NOT been established.

| Actual implementation area | Required contract | Current evidence |
|---|---|---|
| `src/compiler.shen`: `compile-expression`, `kl->scheme` | Simulation from KLambda evaluation to emitted Scheme | 12 actual-output schemas validated from raw data in Rocq for all integer inputs; general preservation open |
| `order-call-inputs`, `order-call` | Left-to-right effects and exceptions retained | Native fixtures; no proof |
| `emit-let`, `merge-nested-lets` | Lexical capture, order, and scope retained | Rocq proves a basic abstract let/lambda law; actual functions open |
| `emit-application`, `emit-dynamic-application`, `nest-call` | Direct/computed calls and partial application preserve meaning | Native fixtures; no proof |
| `emit-if`, `emit-cond`, `force-boolean` | Branch laziness and condition domain retained | Native fixtures; no proof |
| `emit-trap-error`, `emit-trap-error-optimize` | Error scope and handler behavior retained | Native fixtures; no proof |
| `emit-equality-check`, `src/primitives.scm: kl:=` | Equality implements the admitted value relation | Ground data fixtures; closure/vector cases open |
| `src/primitives.scm`: global access and `kl:eval-kl` | Separate namespaces, rebinding, dynamic loading | Outside admitted profile |
| Chez lowering, allocation, GC, native runtime | Representation/simulation/resource guarantees | Assumed |

Sources:
https://github.com/tizoc/shen-scheme/blob/8d261518db17fbfec32d1b268b40ed216b925c74/src/compiler.shen
https://github.com/tizoc/shen-scheme/blob/8d261518db17fbfec32d1b268b40ed216b925c74/src/primitives.scm
https://github.com/Shen-Language/shen-sources/blob/shen-43.1/doc/porting.md

## Later targets

Shen-Lua/LuaJIT, Shen-Go, Shen-CL, native LLVM, and BEAM implementations should
consume the same semantic contracts. There are no adapters, pins, or proof claims
for these ports in this release. Add one only with exact source identity and
an explicit representation relation; agreeing with Chez on a corpus is not
sufficient to inherit its eventual preservation theorem.

Each port claim must record:

1. admitted language profile and excluded forms;
2. pinned compiler/runtime source and deployment artifact;
3. value/environment/store/continuation representation relations;
4. forward simulation, error/divergence policy, and any backward direction;
5. numeric, host, GC, FFI, and resource assumptions;
6. proof objects and independent replay command;
7. conformance counterexamples, separately from the formal discharge.

Simulation direction matters. Preservation of successful source runs alone
must not conceal extra target behaviors. Full safety transfer needs the exact
behavior-refinement theorem and its definedness/progress assumptions.
