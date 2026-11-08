# Pass split, wave 1(a): share and norm witnesses, and where stage 0 rejections come from

This census counts things. It proves nothing. The witnesses are untrusted hints for Rocq to check later. Every
acceptance number below is a verdict of the **existing** judge (`rocq/JitLowerStage0.v`, `judge`), computed by Rocq.
Everything else (erasure, blocker classification, rewrite counts) is Shen or Python bookkeeping.

## Inputs (bound)

| what | value |
|---|---|
| Búri base commit | `4cba179` (branch `pass/capture`) |
| Shen/JIT source | `/lps/p4/sj` at `d3348cefbb2b209992039c1c0f55751241750364`. `src/lowerer` and `src/port` are clean; only `src/runtime/{heap,jit}.c` carry the rv64 arena patch |
| binary | `build/shen-jit`, sha256 `5eb9f4336aee535b93577c436f589b65262853defc2602aee41d8cc7d6c51872`, checked against `toolchain.lock.json` by `capture_passes.sh`; runs under `qemu-riscv64` |
| `src/lowerer/lower.shen` | sha256 `cf14473dc8b582277b6628f8c9020d973512d6c6f1dcce9c2af6d299b5f0eb05` |
| `build/tools/lower.shen` (the build's renamed copy) | sha256 `9ad221468580251012a6c12a597a05bb0eea5a52f35375a19bb2d68759c102e2`. Rechecked on every run to equal the Makefile's sed rename of `lower.shen` |
| `src/lowerer/host.shen` | `a3fd9c3b3dc7c5ebbea5945585a58308896abecf1ebd827c15cf5777ac6b4285` |
| `src/port/shen-jit.kl`, `build/port/lower.kl` | `0579fb17…8b3b8287`, `e6d64cdb…4795f083de` |
| `build/stage0/*.forms *.sbc` | sha256 of `LC_ALL=C sha256sum *.forms *.sbc` = `f896bc54f2bf5c891e97f7dd764c3ebb28d15e0346cf8edb9ea3628815c90c28`. The 48 files match upstream's `generated.sha256` |
| `.deps/kernel/klambda/*.kl` (kernel 43.4) | sha256 of `LC_ALL=C sha256sum *.kl` = `694236173d0655f12b4d468df79d148d92fe04b75bf70f49a5b24031cfcd71dd` |
| Rocq | 9.3, opam switch `lps`. Judge `.vo` files compiled from this commit's `rocq/` into `/tmp/capture-rocq` |

## How stage 0 is made, and how it is reproduced

Upstream's `make build/stage0/.done` runs `BOOTSTRAP script src/lowerer/stage0.shen KLAMBDA/ build/stage0/`. The
bootstrap is Shen/JIT 0.1, from `tools/ci-deps.sh`. `stage0.shen` does the following:

1. Loads `host.shen` and `build/tools/lower.shen`. This is `lower.shen` with `shen-jit.lower.` renamed to `stage0.lower.`, and with `shen-jit.sealed?` / `shen-jit.inline-body` calls renamed to `stage0.*`.
2. Reads 24 inputs unprocessed (`read-from-string-unprocessed`): the 22 kernel files, then `src/port/shen-jit.kl`, then `build/port/lower.kl`.
3. Drops each kernel defun the port overrides (`select-overrides`).
4. Seals every remaining defun name: `Sealed`, 950 names, including the 6 extension files.
5. Sets the host's sealed and inline tables from all of them (`shen-jit.host.set-tables`).
6. Lowers each defun with `stage0.lower.defun`. This resets `stage0.lower.*inline-depth*` and `stage0.lower.*fresh*` to 0 and then evaluates `code F Params (norm Params (share Body)) Sealed` ++ `[inline-form F Params Body]`, left to right. `share` therefore runs before `norm`, and the fresh counter carries on from `share` into `norm`.

`tests/shen-jit/capture_passes.shen` does exactly this inside the pinned binary. It loads the same `host.shen` and
`build/tools/lower.shen` as guest code, copies `stage0.shen`'s reading, override and printing functions (it does not load
`stage0.shen`, whose last form would write `build/stage0/`), and splits `defun` into its calls in the same order.

**Reproduction: 950 of 950 code objects, byte for byte.** Every regenerated `.sbc` line and every regenerated `.forms`
line equals the stored one, in all 24 files. The counting copy (below) also reproduces 950 of 950 byte for byte.

**The image's own lowerer is a different thing.** `capture_image_shim.shen` runs the same driver against the
`shen-jit.lower.*` sealed in the binary (measurement only). It reproduces **939 of 950**. The 11 that differ are all in
four extension files: features 2, launcher 3, namespaces 3, programmable-pattern-matching 3. In the image, `shen-jit.sealed?` and
`shen-jit.inline-body` are runtime primitives over the image's own sealing, and `src/runtime/main.c` seals only the first 18
files, so calls to extension functions take the open path. Stage 0 sealed all 24. With fresh-name prefixes normalised,
the image's `.share` equals the build's for all 950 definitions, and its `.norm` differs for 12. That is the 11 above,
plus `shen.macros`, where only the fresh numbering differs: the shim calls each pass through `eval-kl`, which resets
`shen-jit.lower.*fresh*` between `share` and `norm`. For that reason the witnesses come from the build's lowerer, not
the image's. Consumers should know that the globals that matter are `stage0.lower.*fresh*` and
`stage0.lower.*inline-depth*`, and that fresh names are `stage0.lower.*`.

## Witness format (for pass-ir's decoder)

The format is stage 0's output syntax (see `src/lowerer/stage0.shen`), which `tests/shen-jit/stage0_to_rocq.py`'s tokenizer
reads. Each file has one line per definition, in `.forms` order. 950 lines in total.

- `<f>.share`: `(defun F (P1 ... Pn) S)`, where S = `(share Body)` is KLambda.
- `<f>.norm`: `(F (P1 ... Pn) N)`, where N = `(norm (P1 ... Pn) S)`. The nodes are lists:
  - `(const V)`: V is a datum, never a node. It is a symbol, a number, a string, `true` or `false`, `()`, or a list (a folded constant list, printed as a list).
  - `(var X)`, `(if C X Y)`, `(and X Y)`, `(or X Y)`, `(let X V Body)`, `(do X Y)`, `(lambda X Body)`, `(freeze Body)`.
  - `(prim Op (A1 ... An))` and `(call F (A1 ... An))`: the arguments are one list, `()` when empty.
  - `(apply F)`, `(apply F X)`, `(trap X E Handler)`.
  - Variables made by the lowerer are `stage0.lower.argN`, `stage0.lower.elseN` (from `share`) and `stage0.lower.exceptionN`. N restarts at 1 for each definition and continues from `share` into `norm`.
  - `(let stage0.lower.inlining (const F) Body)` marks an inlined body of F. Emission gives it no slot and lowers Body in place (`lower.shen`: `expr`, `test`, `mark`; `mark` emits nothing when `Sealed` is non-empty). **A decoder must treat it as Body**, not as a `let`.
  - `lower.kl`'s own source contains `shen-jit.lower.*` symbols as data. They can't collide with the `stage0.lower.*` fresh names.
- `<f>.nforms` (census only): `(defun F Params erase(N))`, made by `pc.erase` in `capture_passes.shen`:
  - `(var X)` erases to X; a literal `(const V)` erases to V; a folded list erases to a `cons` chain, flagged `folded`.
  - `prim` and `call` erase to `(Op A...)`; `(apply F)` to `(thaw F)`; `(apply F X)` to `(F X)`; `(trap X E H)` to `(trap-error X (lambda E H))`.
  - The marker stays a `let` of the symbol F.
- `<f>.tforms` (census only): the same erasure, with the marker dropped to its body.
- `<f>.ncensus`: `(F (flags...))`, from `folded shadow applyhead callshadow inlined? inlining-marker fresh`.
- `<f>.ticks`: `(F ((key count) ...))`, from the counting run.

Erasure is faithful only while `shadow`, `applyhead` and `callshadow` stay off. **All three are 0 of 950.**

## Commands

All of these run in container `buri-lps`. The worktree is copied to `/work/capture`.

```
bash /work/capture/tests/shen-jit/capture_passes.sh /tmp/capture-run                 # ~21 s; CAPTURE_OK
# Rocq: Observation … JitLowerStage0 compiled into /tmp/capture-rocq, as check-shen-jit.sh does (~5 min)
JOBS=6 bash /work/capture/tests/shen-jit/judge_split.sh /tmp/capture-rocq /lps/p4/sj/build/stage0 \
     /tmp/capture-run/witness /tmp/capture-judge                                    # ~1-2 min; JUDGE_SPLIT_DONE
diff tests/shen-jit/stage0-accepted.txt /tmp/capture-judge/src.counts                # empty: src judge = recorded 61
python3 tests/shen-jit/pass_census.py /lps/p4/sj/build/stage0 /tmp/capture-run /tmp/capture-judge
```

The generated files (witnesses, ticks, logs, per-definition verdicts and the census output) are at
`/private/tmp/claude-502/-Users-reuben-projects/2d420b2f-bdd4-44a2-b787-ce4910b8299e/scratchpad/pass-capture/`. That
directory has 488 files plus `SHA256SUMS`, whose own sha256 is `e599080f1fa1c39f3ce89c9096c0e6a6dc7f814a1ac7b29040427c5b679291a5`.
They are not in git. Hashes of each witness set, all 24 files concatenated in C order:

| set | sha256 |
|---|---|
| share | `6b89749565ff07d60a2dd917b92951ad5a1c1b386e086230d84bf9eff58f1873` |
| norm | `3b73c06ba986f68397a2f75784f62d2f1e5500817ff267dd82940a416bb7d285` |
| nforms | `72fface09a7e98386be28cd7c591257d922ca5afced3a0db776431e64dfaf25d` |
| tforms | `e5593d36c4f57185792424ceed593a4ea2176ef32c20ef337ee418ef488172aa` |

## Findings

1. **Erasing norm unblocks nothing. Of the 889 definitions rejected on source, 0 are accepted on `.nforms`.** The
   accepted set is identical on both: the same 61 definitions. In the existing `Comp`'s terms, none of the 889
   rejections is caused by a front-end rewrite that `norm` removes. Every one still meets an emit-side construct.
2. **The inlining marker hides 11.** Treat it as its body (`.tforms`) and 72 are accepted: the 61, plus
   `shen-jit.lower.code`, `shen-jit.lower.apply-all?`, `shen.prolog-parameters`, `shen.alpha?`, `shen.<shortnatters>`,
   `shen.<whitespaces>`, `shen.<digits>`, `shen-jit.digits`, `eval`, `shen.partial-parse-failure?` and `shen.parse-failure`.
   On these 11 definitions, `Comp` accepts the code against the normal form but rejects it against the source. Their
   source differs from their code only through front-end rewrites (inlining, in these cases). They are the definitions
   that a proved front end plus the existing emit-side relation would cover with no new emit rule.
3. **The emit-side blockers are ranked in the tables below.** On `.tforms` (878 rejected), counting first blocker in evaluation order:
   - **prim `=`: 461.** It is in 587 rejected definitions and the only blocker in 154. `pmap` does not admit `=`.
   - **prim `value`: 59** first blocker, in 220, sole blocker in 36.
   - `<-address` 50; `simple-error` 39; `do` 36; `lambda` 32; `set` 25; folded constant list 21; `trap` 20.
   - Every rejected definition has at least one syntactic blocker. The category "none found (emit mismatch on admitted constructs)" is empty on both nf and tf.
   - There are no anomalies: no definition is accepted while having a blocker.
4. **What norm actually does to stage 0** (counting run, ticks):
   - Sealed inlining reaches 531 of 950 definitions, with 5395 inlines.
   - `cond` desugaring reaches 461. Constant `cons` folding reaches 98, with 1075 folds.
   - `share` chains reach only 4 definitions, all in `macros` (7 chains). `share` leaves the other 946 forms unchanged.
   - Open inlining and `shen-jit.inlined?` guards occur in **0**, because stage 0 seals every input.
   - `fn` rewrites (sealed and open), curried apply, and `((lambda X B) A1 A2 …)` occur in 0.
   - In 191 definitions no rewrite family fires.

## What the numbers do and don't mean

- Acceptance on `.nforms` or `.tforms` is **not** a proof of the front end. It says only that the emit side, as the
  existing `Comp`, relates the stored code to that untrusted erased term. To carry that over to the source still needs
  a proof that `share` and `norm` preserve meaning: inlining, folding, freeze and lambda copying, `cond` and `thaw` sugar,
  and the marker.
- "Rejected" means unvalidated, not wrong. The blocker classification (`pass_census.py`, `blockers`) is a syntactic walk
  of `.norm` that mirrors `JitLowerRel.pmap` and the node kinds `Comp` has rules for. Rocq computed none of it. "First"
  means first in evaluation order (preorder, left to right). "Uses" counts definitions containing the construct;
  "sole" counts definitions where it is the only blocker kind.
- **How the rewrite counts were made.** They are not inferred from witness diffs. They come from an **instrumented copy**
  of `lower.shen`: `tests/shen-jit/instrument_lower.py` wraps 28 rule results as `(do (pc.tick Key) …)` and then applies
  the build's rename. Only the counting run loads it, never the witness run, and it reproduces all 950 stage 0 lines byte
  for byte. Ticks include rewrites inside inlined bodies and inside the synthetic code that `unified-now` and `bound-now`
  normalise. `dynamic-apply` counts `norm-apply` entries; it is not a rewrite.
- Two cross-checks agree definition by definition (0 mismatches in each):
  - `share-chain` ticks: 4 definitions; definitions whose `.share` differs from `.forms`: 4.
  - `sealed-inline` ticks: 531 definitions; definitions that carry the inlining marker: 531.
- Fresh variables appear in 517 definitions. Folded constant lists appear in 98.

## Not done / UNKNOWN

- Witnesses were made under the pinned binary, not under the 0.1 bootstrap that actually produced stage 0. Byte-identical
  reproduction makes the difference immaterial for these inputs, so the bootstrap run was not repeated.
- The witness files are not in git and not checked by Rocq. That is wave 1(b).

---

The rest of this file is the output of `pass_census.py`, unedited.

## Split census (accepted per file)

src: the form as read (.forms); nf: erased normal form (.nforms); tf: erased normal form with
the inlining marker dropped (.tforms). both/either/only compare src with nf; tf only = accepted
on tf and not on src.

| file | defs | src | nf | tf | src and nf | src or nf | src only | nf only | tf only |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| core | 63 | 2 | 2 | 2 | 2 | 2 | 0 | 0 | 0 |
| declarations | 12 | 1 | 1 | 1 | 1 | 1 | 0 | 0 | 0 |
| dict | 10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| extension-expand-dynamic | 16 | 2 | 2 | 2 | 2 | 2 | 0 | 0 | 0 |
| extension-features | 4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| extension-launcher | 11 | 1 | 1 | 1 | 1 | 1 | 0 | 0 | 0 |
| extension-namespaces | 11 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| extension-programmable-pattern-matching | 16 | 1 | 1 | 1 | 1 | 1 | 0 | 0 | 0 |
| extension-type-annotations | 7 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| init | 4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| load | 16 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| lower | 120 | 8 | 8 | 10 | 8 | 8 | 0 | 0 | 2 |
| macros | 32 | 2 | 2 | 2 | 2 | 2 | 0 | 0 | 0 |
| prolog | 89 | 8 | 8 | 9 | 8 | 8 | 0 | 0 | 1 |
| reader | 123 | 7 | 7 | 8 | 7 | 7 | 0 | 0 | 1 |
| sequent | 50 | 3 | 3 | 3 | 3 | 3 | 0 | 0 | 0 |
| shen-jit | 78 | 6 | 6 | 10 | 6 | 6 | 0 | 0 | 4 |
| sys | 110 | 11 | 11 | 12 | 11 | 11 | 0 | 0 | 1 |
| t-star | 53 | 1 | 1 | 1 | 1 | 1 | 0 | 0 | 0 |
| toplevel | 15 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| track | 29 | 2 | 2 | 2 | 2 | 2 | 0 | 0 | 0 |
| types | 7 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| writer | 28 | 3 | 3 | 3 | 3 | 3 | 0 | 0 | 0 |
| yacc | 46 | 3 | 3 | 5 | 3 | 3 | 0 | 0 | 2 |
| **total** | **950** | **61** | **61** | **72** | **61** | **61** | **0** | **0** | **11** |

unreadable (Unparsed): src 0, nf 0, tf 0

Of the 889 definitions rejected on src: 0 accepted on nf, 11 accepted on tf.

## Blockers on nf, definitions rejected on nf (definitions: 889)

| construct Comp has no rule for | first blocker | uses | sole blocker |
|---|---:|---:|---:|
| prim = | 363 | 587 | 109 |
| inlining marker (let stage0.lower.inlining) | 242 | 531 | 11 |
| prim value | 51 | 220 | 34 |
| do | 36 | 126 | 5 |
| lambda | 32 | 99 | 7 |
| trap | 20 | 33 | 0 |
| folded constant list | 19 | 98 | 12 |
| prim <-address | 17 | 103 | 9 |
| prim set | 12 | 131 | 2 |
| let-bound freeze (goto label / thaw in place) | 11 | 24 | 0 |
| prim simple-error | 10 | 214 | 5 |
| prim address-> | 10 | 71 | 5 |
| apply (dynamic call) | 10 | 33 | 3 |
| prim intern | 9 | 90 | 0 |
| prim cn | 7 | 168 | 2 |
| prim absvector | 4 | 17 | 0 |
| apply (thaw) | 3 | 37 | 2 |
| freeze | 2 | 23 | 2 |
| prim shen-jit.tagged? | 2 | 12 | 1 |
| prim char-stream? | 2 | 11 | 0 |
| prim absvector? | 2 | 4 | 0 |
| prim shen-jit.read-file | 2 | 4 | 2 |
| prim shen-jit.symbol? | 2 | 4 | 0 |
| prim shen-jit.vector? | 2 | 4 | 2 |
| prim open | 2 | 3 | 0 |
| prim shen-jit.dict-find | 2 | 3 | 0 |
| prim shen-jit.same? | 2 | 3 | 0 |
| prim shen-jit.symbol-kind | 1 | 50 | 1 |
| prim shen-jit.deref | 1 | 36 | 1 |
| prim pos | 1 | 23 | 1 |
| prim shen-jit.absvector3 | 1 | 22 | 1 |
| prim shen-jit.integer? | 1 | 14 | 1 |
| prim read-byte | 1 | 13 | 0 |
| prim shen-jit.pvar? | 1 | 12 | 1 |
| prim error-to-string | 1 | 3 | 0 |
| prim shen-jit.dict-entries | 1 | 3 | 1 |
| prim shen-jit.dict-put | 1 | 3 | 1 |
| prim shen-jit.hash | 1 | 2 | 1 |
| prim shen-jit.pvar | 1 | 2 | 1 |
| prim shen-jit.dict-remove | 1 | 1 | 1 |
| prim str | 0 | 81 | 0 |
| prim shen-jit.append | 0 | 41 | 0 |
| prim tlstr | 0 | 21 | 0 |
| prim string->n | 0 | 19 | 0 |
| prim shen-jit.pvar-offset | 0 | 13 | 0 |
| prim n->string | 0 | 12 | 0 |
| prim read-unit-string | 0 | 9 | 0 |
| prim close | 0 | 4 | 0 |
| prim shen-jit.sealed? | 0 | 4 | 0 |
| prim / | 0 | 2 | 0 |
| prim get-time | 0 | 2 | 0 |
| prim shen-jit.decimal | 0 | 2 | 0 |
| prim shen-jit.exit | 0 | 2 | 0 |
| prim shen-jit.inline-body | 0 | 2 | 0 |
| prim shen-jit.quiet? | 0 | 2 | 0 |
| prim write-byte | 0 | 2 | 0 |
| prim write-string | 0 | 2 | 0 |
| prim shen-jit.filled-vector | 0 | 1 | 0 |
| prim shen-jit.install | 0 | 1 | 0 |
| prim shen-jit.mark-toplevel | 0 | 1 | 0 |
| prim shen-jit.sealing | 0 | 1 | 0 |
| prim shen-jit.trace-text | 0 | 1 | 0 |

## Blockers on tf, definitions rejected on tf (definitions: 878)

| construct Comp has no rule for | first blocker | uses | sole blocker |
|---|---:|---:|---:|
| prim = | 461 | 587 | 154 |
| prim value | 59 | 220 | 36 |
| prim <-address | 50 | 103 | 11 |
| prim simple-error | 39 | 214 | 6 |
| do | 36 | 126 | 6 |
| lambda | 32 | 99 | 13 |
| prim set | 25 | 131 | 2 |
| folded constant list | 21 | 98 | 13 |
| trap | 20 | 33 | 0 |
| prim shen-jit.symbol-kind | 14 | 50 | 1 |
| prim intern | 12 | 90 | 0 |
| prim address-> | 12 | 71 | 5 |
| apply (dynamic call) | 12 | 33 | 4 |
| let-bound freeze (goto label / thaw in place) | 11 | 24 | 0 |
| prim cn | 9 | 168 | 4 |
| prim shen-jit.tagged? | 9 | 12 | 1 |
| prim shen-jit.integer? | 7 | 14 | 3 |
| prim char-stream? | 7 | 11 | 0 |
| prim shen-jit.deref | 6 | 36 | 4 |
| prim absvector | 4 | 17 | 0 |
| apply (thaw) | 3 | 37 | 2 |
| prim shen-jit.absvector3 | 3 | 22 | 2 |
| prim shen-jit.read-file | 3 | 4 | 2 |
| freeze | 2 | 23 | 2 |
| prim absvector? | 2 | 4 | 0 |
| prim shen-jit.symbol? | 2 | 4 | 0 |
| prim shen-jit.vector? | 2 | 4 | 2 |
| prim open | 2 | 3 | 0 |
| prim shen-jit.dict-find | 2 | 3 | 0 |
| prim shen-jit.same? | 2 | 3 | 0 |
| prim pos | 1 | 23 | 1 |
| prim read-byte | 1 | 13 | 0 |
| prim shen-jit.pvar? | 1 | 12 | 1 |
| prim error-to-string | 1 | 3 | 0 |
| prim shen-jit.dict-entries | 1 | 3 | 1 |
| prim shen-jit.dict-put | 1 | 3 | 1 |
| prim shen-jit.hash | 1 | 2 | 1 |
| prim shen-jit.pvar | 1 | 2 | 1 |
| prim shen-jit.dict-remove | 1 | 1 | 1 |
| prim str | 0 | 81 | 0 |
| prim shen-jit.append | 0 | 41 | 0 |
| prim tlstr | 0 | 21 | 0 |
| prim string->n | 0 | 19 | 0 |
| prim shen-jit.pvar-offset | 0 | 13 | 0 |
| prim n->string | 0 | 12 | 0 |
| prim read-unit-string | 0 | 9 | 0 |
| prim close | 0 | 4 | 0 |
| prim shen-jit.sealed? | 0 | 4 | 0 |
| prim / | 0 | 2 | 0 |
| prim get-time | 0 | 2 | 0 |
| prim shen-jit.decimal | 0 | 2 | 0 |
| prim shen-jit.exit | 0 | 2 | 0 |
| prim shen-jit.inline-body | 0 | 2 | 0 |
| prim shen-jit.quiet? | 0 | 2 | 0 |
| prim write-byte | 0 | 2 | 0 |
| prim write-string | 0 | 2 | 0 |
| prim shen-jit.filled-vector | 0 | 1 | 0 |
| prim shen-jit.install | 0 | 1 | 0 |
| prim shen-jit.mark-toplevel | 0 | 1 | 0 |
| prim shen-jit.sealing | 0 | 1 | 0 |
| prim shen-jit.trace-text | 0 | 1 | 0 |

## Normal-form facts (definitions)

| fact | definitions |
|---|---:|
| inlined? | 0 |
| inlining-marker | 531 |
| fresh | 517 |
| folded | 98 |
| shadow | 0 |
| applyhead | 0 |
| callshadow | 0 |

share output differs from the source form: 4 definitions

## Rewrite families (count run)

| family | key | definitions | firings |
|---|---|---:|---:|
| share chains | share-chain | 4 | 7 |
| **share chains** | any | **4** | |
| sugar | cond | 461 | 617 |
| sugar | type | 1 | 1 |
| sugar | protect | 1 | 1 |
| sugar | thaw | 37 | 134 |
| sugar | trap-lambda | 32 | 36 |
| sugar | trap-other | 1 | 1 |
| sugar | lambda-app | 3 | 3 |
| sugar | lambda-app-more | 0 | 0 |
| sugar | curried-apply | 0 | 0 |
| sugar | fn-sealed | 0 | 0 |
| sugar | fn-open | 0 | 0 |
| sugar | eval-kl | 16 | 17 |
| **sugar** | any | **530** | |
| prim folding | fold-cons | 98 | 1075 |
| prim folding | fold-plus | 6 | 6 |
| prim folding | fold-minus | 0 | 0 |
| **prim folding** | any | **103** | |
| sealed inlining | sealed-inline | 531 | 5395 |
| sealed inlining | inline-int-arg | 30 | 30 |
| **sealed inlining** | any | **531** | |
| open inlining | open-inline | 0 | 0 |
| **open inlining** | any | **0** | |
| freeze copying | let-frozen-copy | 5 | 12 |
| freeze copying | let-frozen-keep | 17 | 31 |
| freeze copying | frozen-late-hoist | 3 | 11 |
| freeze copying | inline-frozen | 6 | 16 |
| **freeze copying** | any | **23** | |
| is!/bind! | unified-now | 4 | 7 |
| is!/bind! | bound-now | 6 | 25 |
| is!/bind! | bound-now-frozen | 5 | 12 |
| **is!/bind!** | any | **7** | |
| lambda copying | let-lambda | 6 | 23 |
| **lambda copying** | any | **6** | |
| (not a rewrite) dynamic application | dynamic-apply | 40 | 157 |
| **(not a rewrite) dynamic application** | any | **40** | |

no rewrite family fired (dynamic-apply aside): 191 definitions

anomalies (accepted with a syntactic blocker): 0
