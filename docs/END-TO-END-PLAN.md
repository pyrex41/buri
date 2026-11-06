# Shen to ARM: complete verification and closure plan

Planning baseline: 31 October 2026, Búri PR #1, commit
`97b38751db00398621d0fb32e11068c0aa81864f`. This document is a plan, not a
completion claim. All 36 work packages below require their acceptance evidence.
Existing component proofs can satisfy parts of them; none is marked complete
merely because the repository has 357 audited statements.

**Update, 6 November 2026.** Five further packages, E2E-37 to E2E-41, form the optional Shen/JIT lane in
[SHEN-JIT](SHEN-JIT.md). They are not mandatory for closed deployment, and the 36 packages below are unchanged.

**Objective.** Keep Shen as the application, specification, and executable
semantic language. Establish checked preservation through both Shen-Scheme/Chez
and Shen-CL/SBCL to exact AArch64 deployment artifacts. Include the complete
reachable runtime, initialization, allocation, collection, errors, effects,
dynamic execution, and shutdown. Then close the supporting deployment software
and the certificate acceptance path. TLA+ supplies temporal specifications;
Shen supplies definitions and candidate derivations; Rocq checks the proofs.

This expands the earlier six-stage plan, which deliberately deferred Chez
internals. It does not retroactively change the status of those six stages.
The executable implementation and certificate construction remain in Shen under
AGENTS.md. Coalton remains optional developer tooling. Fenrir is not a required
replacement application language; its machine-code experiments may be reused
only after their semantic relationships are proved.

**What “nothing remains open” means.** Every software obligation for a precisely
versioned release is discharged by a checked theorem, or is proved unreachable
under enforced admission rules. No required feature can be silently removed to
get a green report. No whole-compiler, whole-runtime, truthful-IO, or correct-OS
oracle may remain in the final software closure. The small foundational trust
base is explicitly listed: chosen logic and ultimate checking root, specification
meaning, the bottom ISA/device model, and physical hardware correspondence.
These are foundations, not unfinished implementation tickets. Mathematical
proof cannot prove that a physical chip always follows its model or that a
business specification expresses the stakeholder's intent.

Universal automation is not the objective. General programs need not terminate;
termination, resource adequacy and application properties require suitable
certificates. A system can cover all constructs of a pinned language without
deciding every true proposition about every program. No promise of relative
completeness is made for arbitrary properties in a fixed effective logic.

**Release claims and profiles.** Maintain three separately named endpoints:

| Endpoint | Meaning | What it cannot be called |
|---|---|---|
| Language/port | Shen through generated Scheme or CL, under explicit host contracts | Native or ARM verification |
| Hosted ARM process | Exact executable and runtime through AArch64, under a specified OS/device environment | Verification of Linux or the whole machine |
| Closed deployment | Both supported execution paths plus their required supervisor/OS services and initialization, down to the declared hardware interface | All hardware, all operating systems, or arbitrary third-party libraries |

The final goal of this plan is the third endpoint. Earlier endpoints are useful
checkpoints, not substitutes. Start experiments on little-endian AArch64 Linux
with the existing pinned Shen 43.1 + PR117 language baseline. Select an exact
ARM architecture revision, ABI, CPU feature set and OS/runtime configuration in
step 01; there is no current proof-compatible ARM platform pin in this plan.
Use one mutator thread first, but retain dynamic evaluation and concurrency as
required later packages. Core Shen, pinned library modules, host extensions and
deployment services have separate coverage manifests. “Full Shen” means all
constructs and primitives of that frozen language definition, not every future
host extension. All such boundaries are visible to admission and reporting.

**The final theorem family.** For each port, bind source bytes S, decoded program
P, contract C, dependency/configuration manifest M, deployment bytes B, and proof
bundle pi. Acceptance must establish that loading exactly B under the modeled
environment executes behaviors that refine P, and that P satisfies C. Relate
values, stores, errors and external observations explicitly rather than equating
host representations. Use maximal behaviors, including divergence, exceptions
and modeled resource failure, with progress/non-stuttering obligations. Add
separate theorems for termination, liveness, resource bounds and information
flow. Plain finite trace inclusion does not establish all of those properties.
For nondeterministic specifications, prove only the directions required by the
claim; do not demand equality of all allowed source and implementation behaviors.

Other ARM programs can enter at the binary-contract layer in step 20, with direct
machine proofs and the same runtime, linking and environment closure. They need
not have Shen source. This gives a common verification framework, not automatic
proofs for arbitrary binaries. Later Shen ports reuse the shared semantics and
contract logic, but must supply their own complete target, representation,
compiler/runtime and artifact proofs before inheriting a release guarantee.

**01. Freeze the completion contract.** Dependencies: none.

Inventory the exact Shen kernel and overlays, both port versions, compiler modes,
host runtime configurations, language extensions, ABI, ARM instructions/features,
numeric/encoding policies, OS services, concurrency modes and threat model.
Record required features independently of the current validator's abilities.
Write separate definitions of functional correctness, memory safety, confinement,
termination, liveness and confidentiality. Specify an initial minimal experiment
without confusing it with the final coverage requirement.

Deliver: a versioned release charter and feature/property matrix. Exit: each
required feature and claim has a named semantics and an owning work package;
each provisional exclusion has an enforcement test and a scheduled closure step.
Removing a required feature changes the release charter rather than completing it.

**02. Replace prose-only gaps with an obligation graph.** Dependencies: 01.

Give every boundary a stable ID, exact source/configuration identity, statement,
premises, dependencies, proof objects, evidence kind and owner. Track component
proof, executable correspondence, generated artifact correspondence and deployed
identity separately. Include existing TRUST, TRUST-AUDIT, six-stage and port
documents; reconcile older statements against the newer evidence without erasing
history. Use conservative dependency closure: arbitrary dynamic reachability is
not decidable. Runtime admission handles later code, rather than claiming a
complete static call graph.

Deliver: a checked release ledger and coverage checker. Exit: every current gap
maps to a package below; no dependency cycles are discharged by assuming each
other. Joint invariants or well-founded constructions must close such cycles.

**03. Pin and reproduce the entire build.** Dependencies: 01–02.

Use Nix for exact dependency/toolchain environments and Earthly/Earthbuild for
build orchestration. Pin source trees, submodules, patches, boot images, kernel
overlays, compiler flags, build-time generators, native libraries and link inputs.
Produce Scheme and CL artifacts for the same declared ARM profile. Record which
compiler actually built each file. Introduce hermetic offline reconstruction and
independent builds early; retain their evidence throughout the project.

Deliver: build recipes, byte manifests and dependency inventory. Exit: the
release can be rebuilt and its differences explained. Reproducibility establishes
identity evidence, never semantic preservation; steps 20–32 discharge that gap.

**04. Define observations, failures and external interaction.** Dependencies: 01.

Specify returns, structured errors, divergence, allocation/stack failure, IO,
exit status, cancellation, signals, time and randomness. Keep proof-search budget
exhaustion distinct from program resource exhaustion. Define which internal steps
are unobservable and which allocations, writes, publications or exceptions are
observable. Model adverse environments, partial IO and failed dependencies.
Specify termination claims against explicit scheduling/input availability.

Deliver: common labeled transition and observation definitions in Rocq and Shen.
Exit: no later pass can hide an error, failed write or infinite internal loop by
choosing a weaker observation vocabulary.

**05. Complete the language value and store model.** Dependencies: 04.

Cover numbers, symbols, booleans, strings, pairs/improper lists, vectors, closures,
streams and mutable global state. Specify exact/inexact operations, promotion,
rounding, signed zero, infinities/NaNs where admitted, comparison and printing.
Specify byte versus character encodings, aliasing, object identity and cyclic
host objects at boundaries. Do not force Scheme and CL into identical native
representations; prove relations to one agreed semantic profile. Resolve actual
semantic disagreements explicitly instead of blessing differential agreement.

Deliver: value/store definitions and a per-port representation obligation matrix.
Exit: each primitive domain and every accepted boundary value has defined meaning.

**06. Complete KLambda semantics.** Dependencies: 04–05.

Define all constructs: lexical scope, globals and redefinition, direct/computed
calls, closures, currying/overapplication, recursion, freeze/thaw, errors and
handlers, mutation and IO. Give small-step semantics with heap and continuations;
connect any executable fuel evaluator to it. Prove determinism where appropriate,
well-formed-state preservation, substitution/environment laws and explicit stuck
states. Model divergent executions without equating a single fuel timeout with
divergence. State tail-position behavior before proving bounded stack use later.

Deliver: complete core semantics and reusable semantic lemmas. Exit: every
required KLambda form and primitive has a semantic rule; no full-language claim
is made from the existing first-order fragment alone.

**07. Verify the executable Shen semantics.** Dependencies: 06.

Prove that actual `shen/klambda.shen` and its dependencies implement the formal
semantics. Cover parsing/admission, environments, closures, stores, effects and
all verdicts. Bind exact source and installed code; do not substitute a similar
Rocq interpreter. Prove the semantic normalizer where its output is relied upon;
otherwise retain it as an untrusted candidate producer. Establish input-size and
depth handling independently of theorem truth.

Deliver: source-bound interpreter/refinement theorems. Exit: every accepted
execution result has a formal witness, with the promised converse/completeness
within the stated evaluator profile and sufficient resources.

**08. Specify and prove the application contract logic.** Dependencies: 04–06.

Define pre/postconditions, heap predicates, state invariants, effects, recursion
and external-operation contracts. Give their meaning in the execution semantics.
Prove soundness of the inference rules, including induction measures and framing.
Treat user-defined axioms or sequent rules as obligations, never automatic truth.
Keep partial correctness, total correctness and temporal properties distinct.
Specify certificates carrying theory, statement and program identities.

Deliver: a sound contract calculus and certificate grammar. Exit: checked
derivability entails the stated semantic property under exactly the recorded
premises. This does not assert a terminating decision procedure for validity.

**09. Close every certificate checker and admission path.** Dependencies: 07–08.

Finish EQ-1 induction-checker correspondence; retain and extend the EQ-2 work.
Prove raw decoding, exact input consumption, variable binding, canonical forms,
theory lookup, rejection and checker termination for finite certificates. Bind
actual Shen implementations to their Rocq counterparts. Rule injection, stale
programs, changed contracts, malformed terms and forged “accepted” labels must
not grant authority. Keep Thornet/Vör search outside acceptance; search failures
remain unknown, not disproof.

Deliver: verified source-level checkers and a single acceptance interface. Exit:
all acceptance routes imply the same soundness theorem; no alternate UI, cache,
serializer or fast path bypasses it. Native checker execution is closed in 32.

**10. Prove the Shen type/sequent and effect systems.** Dependencies: 06–09.

Formalize the actual pinned typechecker, its sequent judgments and PR117 changes.
Prove rule soundness, implementation correspondence and any elaboration/erasure
preservation. User-extensible theories require soundness certificates. An effect
discipline must account for globals, reflection, exceptions and runtime eval;
ordinary Shen typing does not automatically establish confinement or termination.
Define what `tc +` certifies and why switching to `tc -` preserves that claim for
the exact validated artifact and dependencies.

Deliver: type/effect metatheorems and source-bound implementation results. Exit:
each advertised “correct by construction” guarantee names a proved judgment;
post-check redefinition invalidates or revalidates dependent claims.

**11. Verify bytes, readers, codecs and tagging.** Dependencies: 05–07,09.

Finish exact source-byte decoding, package/symbol identity, escapes, numeric
syntax, improper data, complete consumption, canonical serialization and actual
tagging implementations. Separate reading inert proof data from macroexpanding
program text. Prove the exact codec arithmetic and decimal conversion domain;
close the known stock inexact-halving mismatch with a justified implementation or
an enforced sufficient domain. Do not infer installed executable identity from
`ps` metadata. Bound or model parser recursion and allocation failures.

Deliver: byte-to-AST and AST-to-byte implementation correspondence. Exit: the
artifact actually checked denotes the exact admitted bytes and no hidden suffix,
reader evaluation or metadata substitution can change their interpretation.

**12. Prove the complete Shen frontend.** Dependencies: 06–07,10–11.

Cover package processing, macros, parsing, pattern compilation/factorization,
arity registration, currying, type erasure and Shen-to-KLambda lowering. Account
for compile-time side effects and order of metadata updates. Macro processors
may execute arbitrary Shen: model that phase and validate its result, rather
than treating macros as harmless text replacement. Prove universal preservation
or a sound checked translation relation for every required frontend route.

Deliver: actual frontend-to-core preservation. Exit: source properties reach
KLambda without an unproved “the frontend did the right thing” premise, including
errors, partial installation and dynamic definitions.

**13. Close the standard and application library surface.** Dependencies: 06–12.

Inventory every required pinned Shen library and compiler/helper dependency,
including Prolog/YACC functionality used by the product. Prove module contracts
and their implementations, including stateful helpers and failure paths. Separate
the general language implementation theorem from stronger library API properties.
For foreign packages, verify their boundary and implementation, or reject them
from the claimed execution environment until this is done.

Deliver: a versioned library contract catalog and dependency-closed proofs. Exit:
no reachable helper is justified solely because it is “standard” or community code.

**14. Complete the generated Scheme and CL semantics.** Dependencies: 04–06,11.

Define the target constructs and library operations actually emitted by the two
ports. Include lexical/dynamic binding, host truth values, multiple values where
used, package identity, mutation, nonlocal exits and evaluation order. CL printer
methods invoked by diagnostics and any implicit Scheme runtime effects must be
modeled or removed by a proved implementation change. Support conservatively
all compiler output forms; reject unexpected output until coverage is added.

Deliver: target semantics and program/state/continuation relations. Exit: each
required emitted form has a meaning and a port-level refinement obligation.

**15. Finish the actual Shen-Scheme compiler.** Dependencies: 12,14.

Close all branches of argument ordering and fresh-name generation, including
occurrence counting; complete binding, symbol emission, conditionals, equality,
direct/computed calls, currying, closures, handlers, mutation and tail calls.
Extend the captured arbitrary-tail merge theorem through its surrounding passes.
Prove pass composition against the exact source or validate every generated
instance with a proved checker. Include compiler failure and partial definition
installation; preserve effects and error payloads, not just successful values.

Deliver: one general port-preservation theorem for all required KLambda input.
Exit: no required compiler branch remains an oracle or merely a sampled schema.

**16. Finish the actual Shen-CL compiler.** Dependencies: 12,14; parallel with 15.

Connect the strict-boolean guard to actual `emit-if` and boolean optimizations.
Then cover arithmetic specialization/bignum fallback, binding, direct/computed
calls, closures, currying, nonlocal exits, tail calls, packages, global redefinition
and module bootstrap metadata. Validate safety/optimization settings as part of
the theorem. Preserve Shen boolean/equality semantics despite different CL truth
and numeric predicates. The existing abstract continuation theorem alone does
not certify a generated condition expression.

Deliver: the corresponding full port-preservation theorem. Exit: the same Shen
contract can be transported through either port, with explicit port-specific
representation and platform premises and no missing compiler branch.

**17. Discharge every primitive and helper wrapper.** Dependencies: 05,13–16.

Enumerate primitive roots and their entire conservative dependency closure per
port/configuration. Prove arithmetic, classification, strings, symbols, pairs,
vectors, globals, streams, clocks, errors and conversion wrappers. Include all
supported signs/types, out-of-bounds cases, aliasing and cyclic inputs where
admitted. Replace abstract whole-helper contracts with actual body proofs. Keep
remaining lower host operations individually named for steps 21–27.

Deliver: a mechanically complete primitive coverage matrix. Exit: no root is
hidden behind an aggregate “runtime behaves correctly” assumption.

**18. Verify the whole observer and provenance pipeline.** Dependencies: 09,11–17.

Compose reading, frontend/backend compilation, snapshotting, tagging, encoding,
writes, installation and publication through the actual higher-order entry.
Prove every failure prefix and resource cleanup; preserve actual nontransactional
behavior unless a separately proved change introduces transactions. Bind actual
compiler input/output and installed executable in one lifecycle. Account for
mutable input data, stale files, changed bindings, interrupted writes and concurrent
observers. Hash equality alone is not a proof of where code originated.

Deliver: a complete source/target/install correspondence theorem at the semantic
level. Exit: successful evidence describes exactly the code installed, while
native IO and deployment identity obligations flow explicitly to 26–31.

**19. Verify dynamic eval, loading and redefinition.** Dependencies: 10–18.

Model runtime-generated programs, compilation, activation, redefinition and
dependency invalidation as state transitions. Validate new code before it gains
execution authority, or execute it through an already verified interpreter with
the same semantics. Existing application invariants require new-code contracts;
arbitrary `eval` cannot retain arbitrary old proofs automatically. Prove atomic
publication or the exact observable intermediate states. Preserve immutable
certificate bytes and sealed checker dependencies.

Deliver: a checked dynamic-admission protocol and preservation invariant. Exit:
all execution entry points, including REPL/FFI callbacks and mutable code objects,
are covered. A sealed-only milestone is not full dynamic Shen coverage.

**20. Establish the authoritative ARM proof foundation.** Dependencies: 01,03–04;
start this research gate early, in parallel with the language work.

Pin a Sail/Arm model, Rocq generation/toolchain and instruction-logic integration.
Evaluate Islaris/Isla on the exact chosen versions. Audit semantic translation,
symbolic execution, SMT use, trace generation and decoding: every relied-upon
result needs a checked witness or its own correctness proof. Prove raw-byte
instruction decoding and memory/register behavior, including flags, faults and
the selected memory model. Connect any Fenrir handwritten model to this one.

Deliver: an executable proof toolchain and byte-level proofs for a branch, call,
load/store, fault, allocation stub and required atomic operation. Exit: exact
instructions are checked against the selected ISA model; no disassembly-text or
toy-ISA agreement is substituted. Tool compatibility and missing mechanisms are
research deliverables, not assumed available integrations.

**21. Prove both native representation relations.** Dependencies: 05,14,20.

Specify tagging, integers/bignums/floats, pointers, headers, pairs, strings,
vectors, closures, stack frames, multiple values, globals and streams for the
actual pinned Chez and SBCL configurations. Prove layout validity, alignment,
object disjointness, aliasing and valid machine operations. Relate native states
to abstract heaps, environments and continuations, including corrupt-input
rejection and FFI admission. Track ownership across GC and asynchronous events.

Deliver: machine-checked representation invariants. Exit: all native values and
memory accesses used by the admitted execution paths have justified meanings.

**22. Close Chez compilation to ARM.** Dependencies: 14–15,20–21.

Inventory source passes, optimization, closure conversion, primitive expansion,
register allocation, calling convention, stack maps, instruction selection and
emission for the pinned backend. Begin with translation validation of actual
outputs: the compiler remains an untrusted producer; a sound checker establishes
preservation of each artifact. Add reusable pass theorems where they improve
coverage. Include incremental compilation and boot-image generated code.

Deliver: Scheme-to-exact-ARM artifact preservation. Exit: every required code
path/configuration is handled, or a universal compiler proof supplies the result.
A validator may reject an output safely, but cannot then claim universal coverage
of that unsupported required output. Generic closure uses compositional schemas,
not a test corpus. Proving outputs does not claim all unrelated Chez programs or
all possible compiler invocations are correct.

**23. Close SBCL compilation to ARM.** Dependencies: 14,16,20–21; parallel with 22.

Apply the same discipline to CL lowering, optimizations, representations, VOPs,
register allocation, frame conventions, conditions/unwinding, foreign calls and
machine emission. Account for declarations and optimization policies; erroneous
assertions cannot become unchecked proof premises. Cover saved cores, dynamic
compilation and actual dependency code used by Shen-CL. Certify machine output
directly where pass-level proofs are impractical.

Deliver: CL-to-exact-ARM artifact preservation. Exit: the SBCL execution path has
the same coverage standard as Chez, without treating SBCL as a trusted oracle.

**24. Verify native runtime code and support libraries.** Dependencies: 17,20–21.

Cover every reachable assembly, C and host-language routine: apply trampolines,
arithmetic libraries, conversions, intern tables, dynamic lookup, errors, stack
growth, IO adapters, signal bridges and foreign-call stubs. Include libc/libm,
dynamic-link support and other native dependencies actually linked or loaded.
For each routine prove source preservation plus compilation or validate its
exact machine code. Imported verified components require compatible semantics,
configurations and an audited theorem bridge.

Deliver: runtime/link dependency closure with concrete implementation proofs.
Exit: no opaque native call remains in a required path. Replacing a dependency
with smaller code requires a proved API refinement and an explicit version change.

**25. Verify allocation and garbage collection.** Dependencies: 21,24.

Prove allocation, object initialization, roots, stack maps, moving/compacting
collection, remembered sets/write barriers and interaction with closures and
foreign pointers. Include weak references/finalizers wherever reachable. Prove
live objects are preserved, references are updated and reclaimed storage is not
used. Model OOM, stack limits and fragmentation; safety under exhaustion is
different from proving a workload fits. For concurrent collectors, state the
synchronization obligations and close them with 28.

Deliver: per-runtime heap/GC preservation and resource-failure theorems. Exit:
successful collections and all modeled failure paths preserve the runtime
invariant; there is no implicit “GC works” premise.

**26. Verify the executable lifecycle and exact loaded bytes.** Dependencies:
19,22–25; OS composition uses 27 and final closure uses 31.

Cover object formats, relocation, linking, loader behavior, entry registers,
stack/environment/argv, image startup, initialization, runtime compilation,
memory permissions, shutdown and exit. Include code/data separation, patching,
instruction-cache synchronization and later loaded libraries. Validate final
bytes rather than trusting assembly text, source hashes or build success.
Prove the loader executes the checked artifact and that subsequent modification
either preserves its invariant or triggers revalidation before execution.

Deliver: startup-to-exit machine theorem for each concrete deployment image.
Exit: no gap remains between proved binary contents and modeled loaded code;
secure boot/physical identity roots are separately recorded in 31–32.

**27. Prove OS/ABI and IO boundary implementations.** Dependencies: 04,17,20–21.

Specify syscalls and ABI, file descriptors, mappings, signals, clocks, entropy,
partial reads/writes, EINTR, buffering, filesystem errors, cleanup and exit.
Distinguish write completion, atomic visibility and durable persistence. Prove
actual host wrappers refine those interfaces; include callbacks, signal frames,
thread-local state and dynamic library lookup. Treat network peers and input as
adversarial/nondeterministic unless the contract grants explicit guarantees.

Deliver: a complete hosted-process theorem under named OS/device relations.
Exit: every interaction is explicit and wrapper correctness is discharged.
The remaining OS implementation relations are mandatory inputs to step 31,
not a declaration that the whole deployment is finished.

**28. Close concurrency, scheduling and ARM weak memory.** Dependencies:
06,19,21,24–27.

Specify mutator threads, runtime workers, concurrent GC, callbacks, signals,
publication and global rebinding. Prove rely/guarantee conditions, synchronization,
linearization points and memory-order correctness on ARM. Show isolation between
immutable proof inputs, private checking authority and mutable application state.
Prove scheduler obligations for claimed fairness; do not assume an unfair host
scheduler magically implements a fair TLA+ action. Single-threaded Shen does not
automatically make its host runtime single-threaded.

Deliver: concurrent implementation refinement, race/ownership guarantees and
explicit scheduling theorem premises. Exit: all admitted interleavings and actual
runtime threads are covered; a sequential test cannot close this package.

**29. Connect TLA+ and distributed behavior.** Dependencies: 08,19,27–28.

Define the actual supported protocol/state machines, network faults, recovery,
crashes and storage persistence. Bind exact specification syntax to a Rocq
embedding or checked translation; a hand-copied model is a new correspondence
obligation. Prove initialization and step simulation, then non-stuttering,
fairness and progress conditions needed for liveness. Use TLC and ShenCheck for
counterexamples, never as general proof. Include serialization and external
service contracts in composition.

Deliver: implementation-to-temporal-spec refinement for the platform protocols
and declared applications. Exit: safety and conditional liveness are proved under
the exact fault/environment model; arbitrary permanent partition or hardware
failure is not hidden behind an unconditional availability claim.

**30. Prove security and resource claims separately.** Dependencies:
08,10,21,25,28–29.

Prove memory safety, effect/capability confinement and required application
integrity from actual execution. For confidentiality or constant-time claims,
use relational/hyperproperty reasoning with an explicit attacker observation
model; ordinary trace refinement alone is insufficient. Include speculative,
cache/timing or other microarchitectural observations only with an appropriate
model and implementation proof. Otherwise those properties cannot appear on
the certificate. Prove per-program termination measures and stack/heap bounds;
retain explicit failure semantics for workloads without adequacy bounds.

Deliver: a property-specific guarantee matrix and certificates. Exit: each
advertised guarantee has the right theorem, with environmental liveness and
physical side-channel assumptions exposed. No claim of universal termination.

**31. Close the deployment software below the process.** Dependencies: 20,26–30.

Choose the concrete closed-deployment route at step 01 and run its feasibility
work early. Recommended engineering route: a minimal supervisor/OS service set,
using an existing verified kernel where its exact ARM configuration and proofs
fit, plus verified compatibility services needed by both runtimes. This includes
boot code, memory management, IPC, scheduling, loader, required filesystem/network
services, drivers, interrupts, DMA/IOMMU isolation and recovery. Porting Chez/SBCL
to that environment is additional implementation and refinement work.

If the final requirement is Linux itself, verify its required behavior and
conservative dependency closure instead. Merely running Linux above a verified
microkernel does not prove Linux services correct. A hosted Linux result must
remain labeled conditional until that closure is achieved; switching environments
creates a separately identified deployment, not a Linux verification claim.

Deliver: boot-to-service-to-process system composition down to specified device
interfaces. Exit: no required software component is an unproved OS oracle.
Existing kernel proofs must be bridged into the checking trust story; assumptions
about unverified configurations, assembly or initialization are not inherited
silently. Hardware/device behavior remains an explicit physical foundation.

**32. Close checker execution and bootstrap trust.** Dependencies: 09,20,26,31.

Audit Rocq proof objects and dependencies, including unsafe axioms, oracle results,
plugins, extraction and native computation. Distinguish “no custom axioms” from
“no foundational assumptions.” Keep Rocq/coqchk as the initial checking root;
independent replay improves assurance but is not a proof of those binaries.
For the reduced-software-trust endpoint, build or integrate a verified small
checker with supported logic coverage and prove its extraction/compilation,
runtime, startup and exact bytes through the native chain. Audit MetaRocq or
other candidates for exact theorem scope and remaining obligations.

Avoid circular bootstrapping: a newly compiled checker cannot establish its own
initial trust merely by accepting its own certificate. Start from an explicitly
accepted checking root, validate successors, retain the chain and independently
replay where possible. Ultimately a logical/checking and physical root remains.

Deliver: checker-binary correctness, explicit trust-root document and bootstrap
chain. Exit: neither Shen execution nor an unproved extraction/compiler silently
decides theorem validity in the final acceptance route.

**33. Prove complete application examples on both ports.** Dependencies:
08–19,26–30,32; develop examples incrementally throughout.

Use a shared contract set: strict parsing/authorization, mutable vector/state
updates, recursive higher-order code, errors and recovery, allocation/GC pressure,
files/partial writes, dynamic code publication, concurrent work and a persistent
protocol with crashes. Prove functional contracts and relevant resource/liveness
properties for each application, then transport the identical statements through
both port chains to exact artifacts. Exercise failure cases as first-class runs.

Deliver: complete reproducible proof bundles and executable examples. Exit:
each example is end to end; finite examples demonstrate integration, while the
generic language/compiler results establish coverage beyond those examples.
Future applications still require their own contracts and certificates.

**34. Prove the composition theorem and close every premise.** Dependencies: 01–33.

Compose frontend, port, host compiler, runtime, GC, loading, OS and protocol
relations with matched state/trace/error definitions. Check initial and final
states, stuttering, foreign callbacks, faults and dynamic updates. Resolve
mutually dependent compiler/runtime proofs through a joint invariant or a proved
linking theorem, not circular assumptions. Derive the application-level theorem
from exact artifact acceptance. Compute the transitive assumption/dependency
closure and compare it with the small foundational allowlist.

Deliver: one release theorem family for each port, with property-specific
corollaries. Exit: zero unproved software premises outside the declared ultimate checking root for
the closed endpoint and
zero required coverage holes. Unsupported output safely rejected by a validator
remains a coverage failure until its required case is implemented and proved.

**35. Make closure enforceable in CI and deployment.** Dependencies: 02–03;
implement throughout, complete after 34.

Build proposed `check-language`, `check-scheme`, `check-cl`, `check-native`,
`check-system`, `check-assumptions` and `check-release` gates; these names describe
planned targets, not commands already available. Bind every claim to immutable
source, artifact, dependencies, proof objects, profile and checker identities.
Fail closed on missing/stale evidence, changed flags, skipped stages, unsupported
features and unverifiable proof objects. Distinguish invalid, unsupported,
resource-exhausted and successful outcomes. Collect completed process output
without treating marker text or mutation infrastructure failure as proof.

Deliver: a release verifier and deploy-time admission protocol. Exit: modifying
any correctness-relevant input invalidates the old proof bundle, and no mutable
label or forgeable success token authorizes execution. Nix/Earthbuild repeatability
and signed provenance support this process but do not replace semantic checks.

**36. Perform independent closure review and release.** Dependencies: 32–35.

Reconstruct from clean inputs, replay all proof objects, review theorem meaning
against actual code and intended contracts, test the supported hardware/profile
matrix and attempt adversarial certificate/runtime mutations. Review all
reachable initialization, teardown, failure and dynamic paths. Verify that every
historical gap is closed or explicitly outside the required charter with enforced
admission. Require a distinct reviewer of semantic fidelity and trusted-base
changes; theorem counts and green tests do not constitute this review.

Deliver: exact binaries, source/configuration/dependency manifests, specifications,
proof bundles, checker/bootstrap chain, assumption report, coverage report,
reproduction commands and operating procedures. Exit: every mandatory package
has its acceptance evidence and the final theorem applies to the bytes deployed.
Subsequent upgrades reopen affected obligations automatically. The release can
be complete even though future programs, platforms and hardware require new work.

**Execution order and parallel work.** The numbering specifies a dependency-led
plan, not a requirement to wait for every earlier number before starting research.
The companion [planning ledger](../spec/end-to-end-plan.json) lists every package
and its dependencies. All are marked planned; it is not accepted proof evidence
and does not alter the existing six-stage completion flags.

| Wave | Shared work | Scheme/Chez track | CL/SBCL track | Lower-system work |
|---|---|---|---|---|
| A | 01–06, ledger/builds | Inventory actual emitted forms | Inventory actual emitted forms | 20 and 31 feasibility; ARM pins |
| B | 07–14, contracts/checkers/frontend | 15 and primitive proofs | 16 and primitive proofs | 21 representations; 27 interfaces |
| C | 17–19, full observer/dynamic lifecycle | 22 host output validation | 23 host output validation | 24–26 runtime, GC, exact images |
| D | 28–30 concurrency, temporal/security/resource claims | Complete dynamic/concurrent path | Complete dynamic/concurrent path | 31 full deployment; 32 checker |
| E | 33–36 application transport, composition, closure review | Independent complete bundle | Independent complete bundle | Boot-to-exit system bundle |

Near-term sequence: first reconcile the existing ledger and common semantics;
close arbitrary argument ordering/freshness on Scheme and actual conditional
lowering on CL; finish primitive representation and diagnostic contracts; then
compose complete higher-order port preservation. In parallel, demonstrate a
small actual Chez-generated and SBCL-generated ARM function against the selected
ISA model, including a runtime call. Do not postpone discovery of ISA/toolchain
or runtime-platform incompatibility until after all source proofs are written.

**Mapping the existing six stages and trust gaps.**

| Existing gap | Closing packages |
|---|---|
| Full language/closure/mutation semantics | 04–07 |
| Primitive wrappers and native value contracts | 05,17,21,24–25 |
| General actual compiler preservation | 12,14–16,22–23 |
| Native representation, reverse/progress/divergence relations | 04,06,14,20–26,34 |
| Complete observer, capture, IO and installation | 11,18–19,26–28 |
| EQ-1, sequent/type rules and executable checker correspondence | 08–10,32 |
| Source metadata versus actual installed code | 11–12,18–19,26,35 |
| Codec exactness and tagging implementation | 05,07,11,17,21,24 |
| Concurrent rebinding and mutable certificates | 09,19,25,28,35 |
| Resource adequacy, signals, cleanup and failure prefixes | 04,17–19,24–30 |
| Host compiler/runtime and ARM model | 20–26 |
| OS services, durability, devices and boot | 27,29,31 |
| Extraction, checking binary and bootstrap | 32 |
| Distributed temporal claims | 28–29,33–34 |
| Exact artifact/theorem/deployment binding | 03,18,26,32,34–36 |

**Completion rules that cannot be traded away.** A theorem about a model does
not discharge implementation correspondence. A captured body does not establish
the bytes loaded into a process. A primitive-response oracle does not verify
the primitive. Passing two ports on the same corpus does not prove either port.
A per-output validator removes compiler trust only for the output it checks.
Typechecking a tool does not establish its logical soundness. Verified kernel
code does not automatically verify its configuration, drivers or user services.
No axiom, strengthened unverified precondition, narrower silent profile or
changed theorem statement may make a failed required obligation look complete.

The final release has no pending required software obligation outside that
declared ultimate checking root. It still names
its mathematical and physical foundations, the supported platform/profile, the
specific application property proved, and any necessary environmental premise
such as eventual input delivery. This is the strongest honest completion claim.

**Feasibility and scheduling.** Language and port closure build on existing
work; complete host-output/runtime/GC/system closure is a substantial research
and engineering programme. This plan is not evidence that every proposed proof
tool integration already exists or that automation will scale. Price and schedule
the host/native phases only after the early ARM, runtime-call, GC and platform
experiments establish proof size, compatibility and missing mechanisms. If a
required property is false, fix the implementation or explicitly revise the
requirement; if it is not provable in the selected foundation, the release stays
incomplete. Do not replace unresolved science with an invented delivery date.

**Primary references consulted for planning (not imported proof guarantees).**

- [Búri PR #1](https://github.com/pyrex41/buri/pull/1), [six-stage ledger](SIX-STAGES.md), [trust audit](TRUST-AUDIT.md), [Scheme scope](SCHEME-PORT.md), [CL scope](CL-PORT.md).
- [Sail Arm models](https://github.com/rems-project/sail-arm): architecture-model candidate; an exact revision and proof integration must be selected and audited.
- [Islaris](https://github.com/rems-project/islaris): machine-code proof infrastructure candidate; its documented workflow and pinned dependencies are not a turnkey Shen/Chez/SBCL chain.
- [Chez implementation structure](https://github.com/cisco/ChezScheme/blob/main/IMPLEMENTATION.md): compiler passes, backend and native runtime inventory starting point.
- [seL4 proof assumptions](https://sel4.systems/Verification/assumptions.html) and [proof coverage](https://sel4.systems/Verification/proofs): examples of configuration-specific foundations that must be audited before reuse; not whole-system guarantees.
- [MetaRocq](https://github.com/MetaRocq/metarocq): checker/metatheory candidate, subject to logic coverage, extraction and execution review.
- [Coalton assessment](COALTON-ASSESSMENT.md): optional tooling evidence; no additional compilation stage or trusted checker dependency is required.
