# Reuben's Phase 2 decisions, verbatim

Recorded by the main session on 2026-11-12 from its transcript (session 2d420b2f). Each entry is the question exactly as
put to Reuben through the session's question tool, followed by the option he selected or the text he typed, exactly as
returned (`"question"="answer"`), with the UTC time the answer arrived. The main session's own summaries are not quoted.

## 2026-11-10T21:39:47.225Z

```text
"Should the end-to-end theorem be allowed to end at a named limit point? This is the 'stop outcome' behind P1/P3/P7a/P8: the claim becomes 'the target matches the source up to the point where it reaches = on a possible NaN, eval-kl, a byte-buffer primitive, exit, etc.' The study ranks this the most valuable single change: it takes 235 toward 824 validated with the other fixes."="No stops", "Should shen-jit's own port primitives be wired into the semantics (P2)? The model is already written (jit_port_prims_proposed). The study puts 564 definitions at stake."="Wire them, hash in KL (Recommended)", "FunRel ranges over every function in the store, so per-definition counts only mean something with a locality lemma (a definition validates if its own callees do). How should we handle it?"="Prove locality lemma (Recommended)", "The plan allows at most 20 named residual definitions. How should definitions be counted that fail only because a callee is blocked on one of your decision items?"="Inherit decision status (Recommended)"
```

## 2026-11-11T13:39:26.792Z

```text
"Round 2's share-rewrite proof needs two assumptions about the function store that can't yet be proved. HT: thaw is bound to its standard body. HP: hd and tl are bound to the primitives. Both can only come from the initial heap image, which is OB-JIT-IMAGE, still open. Rocq has proved that each is necessary: without them, the share rewrite is unsound. You approved HT in round 1; HP is new. How should these be treated?"="Named residuals (Recommended)"
```

## 2026-11-11T14:03:36.989Z

```text
"Phase 2 has three recommendations where Rocq has already settled the facts. (6) Uncurrying: Rocq proves no sound rule exists, so change the definition of done to 'uncurrying: no rule'. It affects 0 stage 0 definitions. (8) Inline/bind: Rocq refuted both old statements. Replace them with guarded versions that keep the refutations on record; the guard rejects nothing in stage 0, and this unblocks 528 definitions once proved. (9) Let D_wf admit fixed-name primitives like + and -. That makes call_preservation_src stronger, but it has to be re-proved, and its text stays byte-identical while its meaning widens. This fixes 6 definitions. Also: approve emit-spec's five statement-shape rows (env_ok, the 1-arg window, GvalsRel, the catch-up form, the index shape). Approve all as recommended?"="Approve all (Recommended)", "Making absvector a primitive frame requires answering one question: what bound applies to absvector? The bytecode raises at 2^48 elements, while the KLambda source model allocates without limit. This affects 17 definitions."="Bytecode bound in profile (Recommended)", "error-to-string: the source model returns the literal "error", while the bytecode returns the exception's real message text. This affects 3 definitions. How should error text be treated?"="Model real message (Recommended)", "IO primitives (open, close, read-byte, write-byte; 22 definitions) disagree with the source model on two points. open adds the home-directory prefix (*home-directory*), and reads or writes on closed or wrong-direction streams differ. Should the source port model these?"="Model prefix + stream state (Recommended)"
```

## 2026-11-12T13:27:11.819Z

```text
"Round 2's emit-sim work found that the old end-to-end statements were false: Rocq refutes them. A machine whose allocation pointer m_next points at an already-used heap cell meets every old premise, yet nothing relates it to the source. The fix adds `Fresh m`, meaning every heap address at or above m_next is unused, as a fifth invariant field of SMs, kept at every step and every end. It is a real machine invariant, already proved to hold for the empty heap (fresh_empty) and to be kept by allocation (fresh_alloc). The old false text and its four refutations stay on record as *_v1. The corollary back to the original call_preservation_src then needs `Fresh m` as an extra premise, alongside GvalsRel, which you already approved. The original statement itself stays proved outright. Approve?"="go".
```

## 2026-11-12T17:00:56.548Z

```text
"Decision record, item 2: eval-kl, meaning runtime lowering of code built at run time (OB-JIT-LOWER-GENERAL). Your 10 Nov 'No stops' answer rules out ending the theorem at eval-kl, but it didn't choose between the two remaining options. Which?"="Gated residual for now (Recommended)", "Item 3: identity primitives (same?/tagged?, OB-JIT-IDENTITY-MODEL; about 466 definitions depend on them). Source KLambda has no notion of object identity, but Shen/JIT compares pointers. Which?"="Model identity (Recommended)", "Item 4: `=` on two possibly-NaN operands (OB-JIT-NAN-IDENTITY; about 206 definitions directly, 648 forecast). Shen/JIT's = returns true for the same NaN object but false for equal NaN values. Which?"="Model it exactly (Recommended)"
```
