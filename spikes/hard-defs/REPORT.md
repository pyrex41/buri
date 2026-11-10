# Hard stage 0 definitions after round 2 (census, not proof)

**Nothing here is proof or validation.** Rocq validates 111 of 955 stage 0 definitions (source judge). Every other number is a census or forecast by spikes/hard-defs/hard_defs.py (Python) from T02's capture. Soundness remarks are readings of the sources, not Rocq results. "Validated" below always means forecast to validate.

## Inputs and commands
- Base: p2/int 551403dab3a118775d4ff7346f64dee05662d54f, read only. Branch study/hard-defs.
- T02's forecast (spikes/pass-split/FEATURES.md) was computed at 4a7346e. `git diff 4a7346e 551403d` on JitLowerRel.v, JitLowerCheck.v, JitLowerPrim.v and JitLowerStage0.v is empty, so it still holds.
- Data: T02's run in buri-lps (/tmp/p2-T02-capture, /tmp/p2-T02-judge), copied out read-only. Hashes rechecked: stage0 ec9b3872...ab736, norm witness e45add98...b69dd1. No Rocq run.
- Command: `python3 spikes/hard-defs/hard_defs.py STAGE0 CAPTURE JUDGE spikes/hard-defs/defs.tsv > spikes/hard-defs/tables.md`. Exit 0; two runs under different PYTHONHASHSEEDs are byte-identical.
- sha256 at 193cc56:
  - hard_defs.py b438cd4bf9619630e2a1683b2c166a0082ab4c40ca30a03e544236faf76832fd
  - defs.tsv 5eb19d09f57c43ea2e30190f81faa8d7778638260f1d240e5a9d3e06ab358f47
  - tables.md 0523c7e1440484ae733786dada019d847b914c876692753f3ea7ff139c02c84b
  - feature_census.py (imported unchanged) 73411de4...
- Reconciliation with T02, exact (direct / D-src / D-low):
  - current Comp: 111 / 46 / 46;
  - every part-A item: 564 / 235 / 235;
  - every item: 955 / 955 / 955.
  - Rocq verdicts read: src 111, nf 112, tf 133.
- Terms:
  - Plan: round 2 as written. It covers every T02 part-A item and every front family except eval-kl. The owner per item is in defs.tsv's planned_coverage column.
  - Direct: the definition's own normal form needs only admitted items.
  - D-src: the definition and its whole call-plus-marker closure are direct.
  - Self vs closure: "self" counts the definition's own needs; "closure" counts anything in its closure.

## 1. Summary
1. The plan alone: 564 direct, 235 D-src. The other 391 self-blocked definitions are blocked only by decision-gated items; no non-decision item is unplanned. A further 329 are self-clear but have a decision-gated definition in their closure (callee-link failures).
2. One cliff. 450 definitions reach a 181-definition SCC whose closure (409 definitions) needs 24 unplanned items. None of the 450 counts until all 24 are admitted.
3. eval-kl welds the lowerer into the SCC. Every kernel path into shen-jit.lower.* goes through shen-jit.eval-kl (the only other entry is shen-jit.code).
   - With a stop outcome there (P3), the SCC is 108 definitions (reader 34, core 31, sys 10, writer 10, shen-jit 8, track 6, macros 4, yacc 3, declarations 2), still reached by 448.
   - The cliff then needs NaN =, the proposed port primitives, tagged?, quiet? (get, shen.<-dict) and the byte buffers in pr.
   - pr is the last brick: adding P7 takes D-src from 460 to 868.
4. Ceiling (D-src): plan 235; cliff bundle 824; plus P4+P5 868; all but P9 876; all 955. Without P9, the Prolog core remains: 45 self-blocked and 34 callee-link.
5. P1, P3, P7a and P8 are one statement change to call_preservation_src': a third disjunct, "a related prefix ending at a named limit point". That is Reuben's decision.
6. Framing.
   - The DoD's 20 cap names callee-link failures. Read literally: 329 under the plan alone, 34 under all-but-P9.
   - Com contains FunRel, and FunRel ranges over every FUser in gfuns s (rocq/JitLowerStep.v:63-70). Read literally, the end-to-end statement at the image store needs all 955 plus the 7 code objects built at initialisation (OB-JIT-IMAGE-INIT). Closure counts, T02's included, assume a locality lemma that nobody owns.

## 2. Q1: which definitions are hard

### 2.1 Unplanned blocker classes
Counts are definitions: self / closure / closure with symbol edges / self inside the SCC.
| class | DoD decision item | self | closure | +sym | self in SCC |
|---|---|---|---|---|---|
| = on two computed operands | NaN = | 206 | 648 | 669 | 32 |
| proposed port primitive, no hash (12 operators) | port-prims | 139 | 544 | 566 | 26 |
| Prolog variables (deref, pvar, pvar?, pvar-offset) | identity/port-prims | 45 | 79 | 521† | 0 |
| same?, tagged? | identity | 16 | 468 | 499 | 4 |
| eval-kl | eval-kl | 16 | 450 | 482 | 4 |
| hashed primitives (hash, dict-find/put/remove) | port-prims | 11 | 454 | 486 | 5 |
| read-file | port-prims | 4 | 13 | 15 | 0 |
| sealed? | port-prims | 4 | 453 | 484 | 1 |
| byte buffers (string->bytes, bytes-length, write-bytes, u8) | port-prims | 3 | 456 | 488 | 0 |
| inline-body | port-prims | 2 | 452 | 484 | 0 |
| exit | port-prims | 2 | 6 | 6 | 0 |
| quiet? | port-prims | 2 | 450 | 482 | 2 |
| install | port-prims | 1 | 450 | 482 | 1 |
| mark-toplevel | port-prims | 1 | 5 | 5 | 0 |
| trace-text | port-prims | 1 | 5 | 5 | 0 |
| sealing | port-prims | 1 | 1 | 2 | 0 |
| any class | | 391 | 720 | | |

† Mostly noise: the lowerer and the Prolog compiler name shen.bind!, shen.lazyderef and is as data in the code they generate.

Vacuous at stage 0 (0 firings or uses):
- fn-sealed and fn-open: the (fn F) rewrites guarded by sealed?, arity and *property-vector*.
- open-inline (shen-jit.inlined?), curried-apply, lambda-app-more, cut-fail, deref-eq.
- foreign, threads, save-executable, the pointer primitives.
- Open callees.

Inlining chains are capped at depth 2 (lower.shen *inline-depth* < 2); 166 definitions reach depth 2. Not hard.

At claim level, not a blocker: OB-JIT-IMAGE-SEALING. 65 extension definitions are unsealed in the image, and 45 definitions have 115 call-sealed sites bound to them. The top theorem needs a no-redefinition premise.

### 2.2 Planned but at risk (defs.tsv at_risk column)
Columns: definitions / in the all-but-P9 forecast of 876 / forecast definitions whose closure has one.
- inline-int-arg: 30 / 27 / **447**.
  - The DoD lists it ("sealed inlining plus marker and inline-int-arg"), but r1-f-inline's spec names only aeq_sound, inline_site_sound and bind_site_sound. Nothing owns shen-jit.lower.subst.
  - The users are mostly reader byte-token rules (shen.<backslash>, ...) in the SCC's closure.
  - Read as sound (subst respects let/lambda shadowing; only integers are substituted). It just has no owner. The highest-value gap in the plan.
- share-chain: 4 / 4 / 7. r1-share-ht may name these residuals (the HT premise).
- frozen-late-hoist: 3 / 0 / 0. It evaluates C1 twice, and its simple-test? admits = and shen-jit.pvar?. All users are Prolog-blocked.
- inline-frozen, let-lambda, let-frozen-copy, bound-now(-frozen), unified-now: 4 to 6 definitions each, all t-star/Prolog and pvar-blocked. Copies of up to 1500 nodes make these the largest checker inputs.
- trap-other, protect, type: 1 each, all in shen.initialise-lambda-forms.
- D00's D_compiled' failures (deref=, unify=, unify=!, bind!, bindv, unwind) all fall inside the Prolog-variable class.

### 2.3 The SCC
- Call+marker edges: 181 definitions, reached by 450. Its closure is 409.
- With symbol edges: 244, reached by 482.
- With the eval-kl edge cut: 108, reached by 448. The lowerer's 123 definitions split into separate components (21, 14, ...).

Unplanned items in the 181-SCC's closure, and what clears them:
- NaN = (101 definitions; 32 inside; assoc, element?, occurrences, compile, shen.<s-exprs>): P1.
- symbol-kind, append, absvector3, integer?, symbol?, vector?, decimal, filled-vector, char-stream?, read-unit-string, write-string: P2.
- dict-find, dict-put (get, shen.<-dict, put, shen.dict->): P2 with hash.
- tagged? (tuple?, shen.linearise, shen-jit.lambda-form): P2b.
- eval-kl (eval, shen.record-and-evaluate, shen.track-function, shen-jit.lambda-form) and install (shen-jit.eval-kl): P3.
- sealed? and inline-body (shen-jit.lower.*): P4 and P5, or P3, which takes them out of the kernel's closure.
- quiet? (get, shen.<-dict): P6.
- string->bytes, bytes-length, write-bytes (pr): P7.

### 2.4 The closure is a lower bound
- 64 definitions do their own dynamic apply or thaw, and 499 have one in their closure.
- 115 carry a function-symbol constant naming a stage 0 definition outside their static closure.
- Adding symbol edges drops the plan's D-src from 235 to 216.
- A real bound needs a store-level argument over value reads, *property-vector*'s lambda forms and *macros*. Not computed here.

### 2.5 Size
In norm nodes (320,418 total):
- shen.initialise-signedfuncs (init): 50,935 (16% of the total), 1131 ticks, blocked by deref only.
- shen.system-S-h (t-star): 16,933.
- shen.initialise-lambda-forms (init): 7,698.
- shen-jit.lower.norm: 6,459.
- shen.l-rules: 5,856.
- shen.initialise-environment: 5,043 (callee-link only).
- shen.<s-exprs>: 4,434.

32 definitions have 1000 or more nodes, 11 have 3000 or more. No judge timing exists (UNKNOWN). The risk is the composed norm checker: if each anti-reduction step rebuilds the term, initialise-signedfuncs costs about 1131 × 51k node visits. r1-pipe-judge should measure it first.

## 3. Q2: the hardest definitions
Effort is rough agent-days.

1. **pr** (shen-jit, 116 nodes)
   - Needs: string->bytes, bytes-length, write-bytes (plus char-stream? and write-string, which P2 covers).
   - Why hard:
     - It is the last brick of the cliff; leaving it out costs 454.
     - The target's VBytes is a mutable heap object: = compares contents, and string? and absvector? are false. No KL value behaves like that, so a VStr or VVec carrier fails prim_compat on string? or absvector?.
     - write-bytes is one JWrites request where KL issues one write-byte per byte, so the traces differ.
   - Routes:
     - P7a: a stop outcome at string->bytes and u8. 1 to 2 days after P1. The claim ends at the first byte write.
     - P7b: take the kernel's own pr, shen.str->bytes and buffer->list as the source of record, and prove bespoke simulations to the port bytecode. The buffer never escapes. Needs a trace relation merging consecutive write-byte events into one JWrites, sound only because env_ok excludes IO failure. 8 to 12 days.
   - Recommendation: P7a now, P7b later.
2. **shen.str->bytes** (50 nodes) and **shen-jit.buffer->list** (49 nodes, u8)
   - Why hard: the same carrier problem. The buffer crosses a call.
   - Route: as pr. The u8 closure is 16.
3. **get** (367 nodes, in the SCC) and **shen.<-dict** (108 nodes)
   - Needs: dict-find and quiet?.
   - Why quiet? is hard:
     - A handler is quiet iff E does not occur in H (lower.shen:1116 omits [exception Top] otherwise).
     - quiet? only switches the message between "" and the text, but exn_ok compares XUser messages exactly (JitLowerPrim.v:10). So a constant source rule is unsound.
   - P6:
     - A jit_rules option reads E ∉ fv H from the source continuation's innermost ETrap frame (agreed_rules: none).
     - MS' needs an invariant tying handler quiet bits to source trap frames.
     - A checker side condition: E ∈ fv(H_src) iff E ∈ vars-of(H_lowered). Norm can drop an occurrence through cond-true truncation or type erasure; such sites are named residuals (expected 0, not measured).
     - 5 to 8 days.
   - Hash: instantiate the parameter as a KL transcription of JitBytecode.hash_go.
     - The target hash is content-based: closures hash to 80, streams to 9.
     - rule_param under the world bijection then holds with no premise.
     - 2 to 3 days, inside P2.
   - OB-JIT-DICT-ALIAS: the bytecode model replaces entries too, so it is a model-vs-binary limit, not a validation blocker.
4. **shen-jit.eval-kl** (63 nodes)
   - Needs: install. Relating it to the KL primitive is OB-JIT-LOWER-GENERAL.
   - P3:
     - The claim ends when the source steps eval-kl and the target is at call-sealed shen-jit.eval-kl with related arguments.
     - install is a second named limit point, so shen-jit.eval-kl itself validates up to install.
     - Sound, and deliberately weaker: every define goes through shen.record-and-evaluate.
     - Needs a norm rule (eval-kl X) → call at the stop point. The DoD currently rejects it in the sugar family.
     - 2 to 4 days after P1. Leaving it out costs 450.
5. **eval, shen.record-and-evaluate (also NaN =), shen.track-function, shen-jit.lambda-form (also tagged?)**: the eval-kl users inside the SCC; 12 more outside it. Route: P3.
6. **shen.dict (filled-vector), append, @p (absvector3), integer?, vector?**: one-line port wrappers inside the SCC.
   - Route: P2. Rules exist in JitProfile.v:295-316 with pp_*_ok lemmas.
   - Precedents: JitKRefPrim.port_compat_of (rule_param) and JitLowerPrim.PR.
   - 0.5 to 1 day per operator.
7. **assoc** (94) and **element?** (73): (= X (hd L)) inside the SCC's closure.
   - Why hard:
     - eq_val gives EqIdentity on two NaNs, so the model stops with RIdentity.
     - The binary says true for the same box; the source says false (num_cmp).
     - Out'_not_stuck forbids a stuck target.
     - No static guard helps.
   - Route: P1, 5 to 8 days. Decide it before r1-emit-assembly fixes preservation'.
8. **shen-jit.lower.norm** (6,459 nodes): sealed?, symbol?, NaN =.
   - P4: a rule In f sealed over jit_rules' sealed parameter.
   - Premises: the image's m_sealed = sealed (OB-JIT-IMAGE-SEALING, 890 vs 955), and m_seal_user false (P8 stops at sealing).
   - 2 to 3 days. After P3 it only matters for the lowerer's own 44.
9. **shen-jit.lower.inline-body** and **open-body**: inline-body.
   - P5: the source rule is inline-form over the callee's KL body (size ≤ 15, inlinable?), quoted as a datum.
   - Precedent: spikes/image-decode's check_def matched the inline field on 955 of 955 (spike, not lane).
   - 4 to 6 days, for 21 definitions.
10. **shen.read-evaluate-print** (mark-toplevel) and **shen.toplevel-display-exception** (trace-text)
    - Both are excluded in JitBytecode (MStuck RExcluded).
    - Route: P1 with RExcluded in it, 0 to 1 day. The claim covers no REPL iteration, already a limit of the model.
11. **shen-jit.repl-read** and **shen.x.launcher.main**: exit (FExit z). Route: a P8 stop, or a source exit outcome. 1 to 2 days.
12. **shen-jit.seal**: sealing changes later sealed? answers and defun admission. Route: a P8 stop; modelling the flag in the source store is larger.
13. **read-file, read-file-as-bytelist, read-file-as-string** (and initialise-lambda-forms by inlining)
    - One JReadFile per file, where KL has open, read-byte and close.
    - Route: a P8 stop, or a source request kind with a trace merge. Closure 13.
14. **shen.dict-fold, dict-keys, dict-values** (dict-entries)
    - C returns live pairs, so a fold that puts sees new values. Model against model it is consistent.
    - Route: P2 admits them; the binary gap stays OB-JIT-DICT-ALIAS. Closure 3.
15. **hash**: P2 with the hash_go transcription. Closure 3.
16. **The Prolog core**: shen.deref, lazyderef, bindv, unwind, shen-jit.undo, shen.bind!, newpv, pvar?.
    - Why hard: VPvar off is a target immediate with no KL value.
    - Carrier options:
      - a new KLValue constructor: large; it breaks case splits, as the exception-identity note says;
      - an encoding inside existing constructors, like KLPort's id_key for closure identity: medium-large. str ("Var N"), hash (off*256+250), = by offset and the type predicates (all false) must agree. Reserved stream handles come closest but need str/hash options and a handle-range invariant.
    - **Verified in the witnesses:** all 662 shen-jit.deref sites pass shen.-null- (a symbol) as the mark. JitBytecode.same is total when one side is a symbol, so deref never hits RIdentity.
    - 10 to 20 days (P9).
17. **shen-jit.unify=, unify=!, occurs-in?, deref=**: the only 4 users of same?.
    - Why hard: (same? X Y) on two pairs (shen-jit.kl:203) is undefined in the model, so under P1 the claim stops at every pair-pair unification.
    - Routes:
      - identity for pairs in both models (OB-JIT-IDENTITY-MODEL): large;
      - a definition-level proof that the fast path doesn't change the answer: unify X X gives Trail unchanged, by induction on the term. 3 to 5 days, inside P9.
18. **shen.system-S-h** (16,933 nodes, 322 ticks, closure 466): the semantically hardest single definition.
    - It has every Prolog rewrite (bound-now(-frozen), unified-now, let-frozen-copy, inline-frozen, frozen-late-hoist, let-lambda; 1500-node copies), plus pvar?, deref, pvar-offset and NaN =.
    - Route: P1 + P9. Use it as the composed checker's stress test.
19. **shen.initialise-signedfuncs** (50,935 nodes, 1131 ticks): only deref, but the checker-time outlier. Route: P9 plus a measured composed run.
20. **shen.initialise-lambda-forms** (7,698 nodes)
    - The only definition with trap-other, protect and type. It calls eval-kl.
    - Its 65 inlined callees bring in 16 unplanned items.
    - It builds the 6 lambda-form code objects of OB-JIT-IMAGE-INIT.
    - Route: it falls out of P1 to P9; its runtime product is a separate obligation.
21. **The 30 inline-int-arg definitions** (shen.<backslash>, shen.<bar>, @v, hdv, ...)
    - Each is easy, but 447 forecast definitions depend on them.
    - Route: an explicit inline_int_arg_sound rule, in r1-f-inline or a new task. About 2 days.

## 4. Q3: ceiling and ranking
Cumulative, each row on top of the previous: direct / D-src / D-low / D-src +sym.
| row | direct | D-src | D-low | D-src +sym |
|---|---|---|---|---|
| plan | 564 | 235 | 235 | 216 |
| +P1 limit (NaN =, mark-toplevel, trace-text) | 737 | 364 | 364 | 342 |
| +P2 wire (16 rules) | 869 | 453 | 453 | 423 |
| +P2b same?/tagged? | 879 | 455 | 455 | 423 |
| +P3 eval-kl/install stop | 895 | 457 | 457 | 423 |
| +P4 sealed? | 897 | 458 | 458 | 424 |
| +P5 inline-body | 899 | 460 | 460 | 426 |
| +P6 quiet? | 901 | 460 | 460 | 426 |
| +P7 bytes | 904 | 868 | 868 | 432 |
| +P8 exit/sealing/read-file | 910 | 876 | 876 | 435 |
| +P9 Prolog | 955 | 955 | 955 | 955 |

Bundles on the plan: direct / D-src / self-blocked / callee-link.
| bundle | direct | D-src | self-blocked | callee-link |
|---|---|---|---|---|
| P3 alone | 574 | 235 | 381 | 339 |
| P1+P3 | 749 | 365 | 206 | 384 |
| P1+P2+P2b+P3 | 895 | 457 | 60 | 438 |
| cliff bundle P1+P2+P2b+P3+P6+P7 | 900 | 824 | 55 | 76 |
| cliff bundle without P3 | 884 | 461 | 71 | 423 |
| cliff + P4+P5 | 904 | 868 | 51 | 36 |
| all but P9 | 910 | 876 | 45 | 34 |
| all | 955 | 955 | 0 | 0 |

Each proposal alone (direct / D-src gained), D-src lost if left out of the full set, effort in agent-days:
- P1: +173 / +129; lost 649; 5 to 8.
- P2: +117 / +41; lost 547; 8 to 12.
- P2b: +4 / +1; lost 466; 1.
- P3: +10 / +0; lost 450; 2 to 4.
- P6: +0 / +0; lost 448; 5 to 8.
- P7: +2 / +1; lost 454; 1 to 2 (P7a) or 8 to 12 (P7b).
- P4: +1 / +0; lost 44; 2 to 3.
- P5: +0 / +0; lost 21; 4 to 6.
- P8: +5 / +3; lost 19; 1 to 2.
- P9: +28 / +18; lost 79; 10 to 20.

Ranked, with the cliff accounted for:
1. P1 and P3 (7 to 12 days, one statement decision).
2. P2 and P2b (9 to 13 days).
3. P7a and P6 (6 to 10 days). These flip the cliff, 457 → 824.
4. P4 and P5 (6 to 9 days, +44).
5. P8 (1 to 2 days, +8).
6. P9 (10 to 20 days, +79).

The cliff bundle costs about 22 to 35 agent-days for 235 → 824.

## 5. Q4: decision items for Reuben
Numbers are self / closure / closure +sym / D-src lost if left out.
- **Wire jit_port_prims_proposed** (18 operators): 158 / 565 / 586 / 564.
  - Recommendation: wire it, with rule_param per rule and hash = a hash_go transcription (no free-hash premise).
  - Keep OB-JIT-DICT-ALIAS as a named model-vs-binary limit.
  - 14 of the operators are in the SCC's closure.
- **eval-kl**: 16 / 450 / 482 / 450 (16 under D-low).
  - Recommendation: a stop outcome (P3), not a named exception. As a stop it costs 0, and OB-JIT-LOWER-GENERAL stays open as the reason.
- **Identity**: split it.
  - tagged?: 12 self, inside same?+tagged? 16 / 468 / 499 / 466. Wire it with P2. **Verified:** all 14 sites take a symbol tag (13 shen.tuple, 1 shen-jit.lazy-form), and JitBytecode.same returns Some false or Some (Pos.eqb) whenever one side is a symbol, so tagged? is never undefined at stage 0.
  - same?: 4 / 52, all Prolog. Keep it residual with P9, or prove answer-independence.
  - deref: 37 / 69 / 509 / 69. It needs only the Prolog-variable carrier, since its mark is always a symbol.
  - Do not add identity to pairs.
- **NaN =**: 206 / 648 / 669 / 648; unguarded only 98 / 618.
  - Recommendation: P1. The model already stops there (EqIdentity → RIdentity, and RCyclic), and the binary's answer depends on box identity.
  - A static non-real guard recovers only 98 direct / 18 D-src (T02) and needs a pguard rework.

Also for his ruling:
1. **The 20 cap.** Callee-link failures: 329 under the plan, 34 under all-but-P9. Recommendation: a callee-link failure whose closure blockers are all decision-gated inherits decision status.
2. **The limit-outcome disjunct** (P1, P3, P7a, P8). Settle it before r1-emit-assembly.
3. **FunRel locality** (or restate Com). Otherwise the literal count is 0 until everything is accepted.
4. **inline-int-arg has no owner.**

## 6. Not done / UNKNOWN
- No Rocq was run. Soundness remarks are source readings. Each proposal's feasibility is a hypothesis for its task.
- Efforts are guesses.
- Checker time is UNKNOWN.
- The forecast inherits T02's assumption that each item admits exactly what lower.shen emits.
- The dynamic-call closure is unbounded; +sym is crude.
- defs.tsv's proposal column lists what clears the definition's own blockers, then, after "| closure:", what its closure also needs. The at_risk column lists risky planned ticks.
