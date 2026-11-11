# Feature predictor, callee-closure limit and residual decisions (census only)

**This file is a census. It proves nothing and validates nothing.** The forecasts below predict what future Rocq
checkers would admit if each named feature or front family were added to `JitLowerRel.Comp` and to the front-end
checkers. Python (`tests/shen-jit/feature_census.py`) computed everything here except the per-definition verdicts of
the existing Rocq judge (`rocq/JitLowerStage0.v`, `judge`). It only reads those. Progress stays as Rocq states it:
**148 of 955 stage 0 definitions are accepted by the src judge** (source form against code; no full-pipeline judge
exists, so the full-pipeline validated count is UNKNOWN). The only acceptance counts in this file are the Rocq verdict
counts: src 148, nf 150, tf 174, from the rerun after `=` against a symbol constant was admitted (below; src 111, nf 112,
tf 133 at the T02 run, before it). Every other number is a prediction or a count of syntax.

Family tasks use `features.tsv` for their count-floor checks. A definition counts toward a task's floor if its
`features` or `required_families` column names that task's item. The forecast assumes every other item the row lists
is also present.

## Inputs and commands (bound)

These ran on branch `p2/T02`, based on `p2/int` at `4a7346ec71d7419f593d57c3034ae6052f982660`. The worktree was
copied to `/work/p2-T02` in container `buri-lps` on 9 November 2026. Rocq 9.3.0 (opam switch `lps`), Python 3.12.3.

```
rocq-slot bash tests/shen-jit/capture_passes.sh /tmp/p2-T02-capture        # CAPTURE_OK
rocq-slot bash tests/shen-jit/judge_split_rocq.sh /tmp/p2-T02-crocq          # ROCQ_OK
JOBS=2 rocq-slot bash tests/shen-jit/judge_split.sh /tmp/p2-T02-crocq /lps/p6/sj/build/stage0 \
     /tmp/p2-T02-capture/witness /tmp/p2-T02-judge                            # JUDGE_SPLIT_DONE
diff tests/shen-jit/stage0-accepted.txt /tmp/p2-T02-judge/src.counts         # empty
python3 tests/shen-jit/feature_census.py /lps/p6/sj/build/stage0 /tmp/p2-T02-capture /tmp/p2-T02-judge \
     spikes/pass-split/features.tsv > tables.md                               # exit 0 (0 mismatches)
```

**Rerun, 10 November 2026 (branch `p2/eq-guard-merge`, on `p2/int` 335348c, rocq/ as at its commit 00071fe).** After
`JitLowerRel.eq_safe_val` was extended to symbol constants (port of `pass/eq` 906b389), `feature_census.py`'s
`BASE` gained `eq-symbol-const` (the feature set `Comp` admits today), and the judge and census were rerun on the
same stage 0 set and the T02 capture (whose witness hashes are the ones below):

```
rocq-slot bash tests/shen-jit/judge_split_rocq.sh /tmp/p2-eq-guard-merge-crocq2                     # ROCQ_OK
JOBS=2 rocq-slot bash tests/shen-jit/judge_split.sh /tmp/p2-eq-guard-merge-crocq2 /lps/p6/sj/build/stage0      /tmp/p2-T02-capture/witness /tmp/p2-eq-guard-merge-judge2                                      # JUDGE_SPLIT_DONE
diff tests/shen-jit/stage0-accepted.txt /tmp/p2-eq-guard-merge-judge2/src.counts                   # empty
python3 tests/shen-jit/feature_census.py /lps/p6/sj/build/stage0 /tmp/p2-T02-capture /tmp/p2-eq-guard-merge-judge2      spikes/pass-split/features.tsv > tables.md                                                     # exit 0 (0 mismatches)
```

Rocq verdicts src 148, nf 150, tf 174 of 955, none unreadable. The 37 definitions gained on src are exactly the rows
the T02 `features.tsv` gave `eq-symbol-const` as their only feature and no required family; none was lost (by name).
The T02 forecast's row A2 (`eq-symbol-const` after `value/set`) predicted this: the rerun's row A1 (`value/set`) equals
T02 row A2, and each rerun row A(k) for k >= 2 equals T02 row A(k+1). Rerun verdict files (`<v>/*.codes`, C order): src
`6a4816e8cec7cf5c5fe459f795bab1eb76bc5998bd49d42bde69339eebcc534c`, nf
`e5bb67fa37a3fe41e9aa37252c900af2d95a8da8cd2bcfc9f21de4a48b974560`, tf
`59bf05943b55fff986ab3a082dd104868e175801e3ddbef5c0f7029f44cd6f84`. `feature_census.py` sha256 `a870685cdbe6182497227b4bb2822b7fb4c99d2311b9e28594c690d9235973a4`,
`features.tsv` `6eeef6975e3aa820dc7668ce3df8b30ae92bba3ae40a4f63cde2b2baa47c98a3`. The generated tables at the end of
this file are the rerun's. The table below, and the analysis sections, are the T02 run's unless they say otherwise.

| what | value |
|---|---|
| capture | witness run 955 of 955, count run 955 of 955 code objects byte-identical to stage 0; image run 944 of 955 (a measurement); `CAPTURE_OK` |
| binary | `/lps/p6/sj/build/shen-jit`, sha256 `e0acd5132a9d876e7618bf1f400706abd82330d18458d209ee064d81d3c10c8d` (pinned v0.6 build, `934cfa5`) |
| stage 0 `*.forms *.sbc` | `ec9b387204471bfce36162019601b89493eb29abc4e42e8b8424d0ab903ab736`, as in CENSUS.md |
| witness sets (24 files concatenated in C order) | share `6881eb294f9a7c90641351ff1a487297e2a6828389354387519ebfc41e97902d`, norm `e45add983f619559649a087a3c8a2c9e4f1fd3061be5d95996d33449a1b69dd1`, nforms `e66ab01a5d023bcc40e67d827fd86e120b817a0f4359d94c00189004ab2d24d6`, tforms `b4a4e7465726007b71e92d2a06f6306ec97429bc425ee1f7bbe929e4d8c847aa`. All four equal CENSUS.md's 0.6 hashes |
| `.ticks` and `.ncensus` (24 files, C order) | `448696ddb99e6b55592c1bc2f5f9d337bb4d34bf5a763f0af647153e466ac88f`, `c44390eaa5b8e32eb1213cef4cb53d293b35a530b054d3860e23d4f569509ade` |
| Rocq verdicts (`<v>/*.codes`, C order) | src `c2c6ce45bc0f5e9f68b28fc8db477edd097018005032db21a7b0eff01c66200d`, nf `169fd9cd8b74c3cfc7e89449e6c7ac85d163e91c17630493f4cfecf3436eb4e3`, tf `d5f72366236895972f6fa60b4f9d804a939de6898228db446b21ed77361798e7`. Same verdicts as the CENSUS.md 0.6 run (`/tmp/p2-v06-judge`, identical `.codes`) |
| script, output | `tests/shen-jit/feature_census.py` `73411de40721f9114e6fb568418e0f0c52d8bec5d553e6a97080d8007b1e47a2`; `features.tsv` `fb4de549ac0a3d5556a8960df5922fdd835365092f34e47bfe17e0ffe6776d20`; a rerun from the same inputs reproduced both and the tables byte for byte |

## What the script computes, per definition

All features come from the `.norm` witness, with the inlining marker treated as its body, as emission does. The
judge's `tf` variant sees the same term.

- **Emit features** (`features` column). These are the constructs the erased normal form needs beyond what `Comp`
  admits today. Today `Comp` admits `+ - * > < >= <= cons hd tl cons? number? string?`, `if and or let`, cond and type
  on source, calls, the cons chain, and `=` with an `eq_safe_val` constant (fixnum, string, boolean, `()`, a non-NaN
  real).
  - `eq-symbol-const`: an `=` whose only constant operand is a symbol.
  - `eq-two-computed`: an `=` with no constant operand, or only a folded list constant.
  - `eq-two-computed-unguarded`: added on top of `eq-two-computed` when neither operand is statically known never to
    be a real. The known-non-real set is the script's `NONREAL` table, which is Python's guess and not a proved
    typing.
  - `prim:<op>`: a heap-free KLambda primitive (`cn str intern pos tlstr string->n n->string /`).
  - `value/set`, `io` (`open close read-byte write-byte get-time`), `vector` (`absvector <-address address->
    absvector?`), `simple-error`, `error-to-string`.
  - `do`, `lambda`, `freeze`, `let-freeze` (a `let` bound to a `freeze`), `trap`, `folded-const`, `apply-dynamic`
    (`(apply F X)`), `thaw` (`(apply F)`).
  - `port:<op>`: a primitive that is not in `KLSyntax.all_prims`. That means each `shen-jit.*` primitive, plus
    `char-stream?`, `read-unit-string` and `write-string`.
  - eval-kl is not an emit feature. `norm` rewrites `(eval-kl X)` to a sealed `call shen-jit.eval-kl`, which `Comp`
    already handles as a call, so eval-kl appears only as the front family `eval-kl`.
- **Front families**, from the ticks of the count run. `fired_families` lists every family that fired;
  `required_families` lists the ones a validation needs.
  - Families: `share` (share chains), `inline` (sealed inlining and the marker), `cond`, `sugar` (type, protect,
    lambda application, curried apply, fn), `trap-sugar`, `thaw-sugar`, `fold-cons`, `fold-arith`, `copy` (freeze and
    lambda copying), `bind` (shen.bind!), `cut-deref` (fired 0 times), `eval-kl`.
  - If only cond or type fired, the source form is validated directly. Comp has `C_cond_*` and `C_type`. Nothing is
    required.
  - If any other family fired, the definition goes source -> norm -> bytecode, and the front end has to justify every
    rewrite that fired, cond included.
- **Chain depth.** At one node, the number of inlining markers stacked with nothing between them except an inlined
  call's argument preamble. Add one if a folded list sits directly under the stack. The witness records only these
  rewrites at a node. Cond, sugar, copying and bind! leave no mark, so the histogram is a lower bound, and the
  per-definition tick counts are reported beside it.
- **Sealed-callee closure.** Edges are `call F` nodes and inlining-marker constants, restricted to the 955 stage 0
  names. Every call target is a stage 0 name; there are 0 open callees. `closure_all` uses both kinds of edge;
  `closure_marker` uses marker edges only. Dynamic application and function-symbol constants are not edges, so every
  closure is a lower bound.
- **Identity dependence.**
  - `yes`: uses `shen-jit.same?`, `shen-jit.tagged?`, `shen-jit.deref` or `shen-jit.deref=`.
  - `maybe`: none of those, but it has an unguarded two-computed `=`. The operands' static kind is unknown, so
    identity of heap objects or NaN may decide it.
  - `no`: neither.

### The consistency check, and what was tuned on it

The current-set prediction is compared with the Rocq verdicts for each of the 955 definitions:

- tf: predicted accepted when the emit features are empty.
- src: tf, and no rewrite fired except cond, type and dynamic-apply entries.
- nf: tf, and no inlining marker.

There are 0 mismatches on each. Two rules were fitted on src and tf:

- cond, type and dynamic-apply are transparent on src.
- eval-kl counts as a front rewrite to a plain sealed call. The first run had 2 tf mismatches,
  `shen.lambda-entry` and `eval`, until eval-kl was taken out of the emit features.

nf was not used for fitting. It is a held-out check, and it matches 112 of 112 accepted at T02 (150 of 150 at the
rerun), including `shen.lambda-entry`, accepted on nf and not on src (at the rerun also
`shen.x.expand-dynamic.expand-declare/checked`).

### `features.tsv`

The file is tab-separated, one row per definition, in `.forms` file order. Its columns are:

| column | meaning |
|---|---|
| `definition`, `file` | name, and the stage 0 file |
| `rocq_src`, `rocq_nf`, `rocq_tf` | the Rocq judge's verdicts: 1 accepted, 2 rejected (no 0s) |
| `features` | emit features beyond today's `Comp`, as above (`-` if none) |
| `required_families` | front families this definition needs (empty when it validates directly on source) |
| `fired_families` | every family that fired |
| `identity` | `yes`, `maybe` or `no` |
| `big_scc` | whether the definition is in the 181-definition strongly connected component |
| `closure_all`, `closure_marker` | transitive sealed-callee closure size, itself excluded |
| `inlined` | inlining-marker constants (the sealed callees inlined) |

## The two D designs, and what the closure limit does

The definition of done asks for `call_preservation_src` under `D_wf`, `D_compiled` and `store_ok`. A definition's
theorem only says something end to end if the store D is right about the callees it reaches. The forecast applies
that limit in two ways:

- **D-src: a store of source bodies with direct acceptance.** A definition counts if it and every definition in its
  call-plus-marker closure are predicted to validate source -> norm -> bytecode under the same feature set.
- **D-low: a lowered store.** D holds the normal forms. A definition counts if it validates directly and every
  definition in its closure is emit-accepted (norm -> bytecode) on its lowered body. The callees' front ends are not
  needed.
- **D-inl** is D-src restricted to marker edges. It is the reading where the closure is taken "from the marker
  constants" alone.

Findings:

1. **Today's 148 shrinks to 63 under the closure limit, in both designs** (rerun; at T02, 111 to 46). Of the 148, 85
   reach a definition the current judge rejects. All 25 accepted definitions in the giant component (18 at T02) are
   among them (next item). D-inl stays at 148: no accepted definition carries a marker.
2. **One strongly connected component holds 181 definitions, and 450 definitions reach it.** Most of it is the lowerer's
   own code (71, from `lower`), the reader (34) and core (31), with writer, sys and shen-jit (10 each) and a few
   others. Under D-src or D-low none of the 450 counts until all
   181 do, so the closure forecast stays near 500 until the last residual is admitted, and then jumps from 500 to 955.
   The last residual, in greedy order, is `shen-jit.write-bytes`, used only by `pr`. Inside the component the
   decision items are: two-computed `=` (32 definitions, 24 of them unguarded), `shen-jit.append` 10,
   `shen-jit.symbol-kind` 6, eval-kl 4, `shen-jit.absvector3` 4, `shen-jit.tagged?` 4, and the port's stream and
   dictionary primitives.
3. **The add-one counts understate what each residual costs.** The leave-one-out table measures from the full set,
   dropping one group at a time. Leaving eval-kl out costs 16 definitions directly but 450 under D-src, because 4
   eval-kl users sit in the giant component. Under D-low it costs 16, since only the callee's emit side matters there.
4. eval-kl adds +0 under D-src even against the full non-decision baseline. `shen-jit.eval-kl` itself needs
   `port:shen-jit.install`, and every eval-kl user has a call edge to it. (4 of the 16 users are also in the
   giant component.)

## Decisions for Reuben

Each item defaults to a **named residual**: the definitions it blocks stay unvalidated, each with an open ledger entry
and that item as its reason. The counts come from the "Decisions" tables below. "Baseline" means every non-decision
feature and family is admitted, the end of part A of the forecast: 564 direct, 235 under D-src, 235 under D-low.

| decision | options | adds (direct / D-src / D-low) | with everything else admitted, leaving it out costs (direct / D-src / D-low) |
|---|---|---|---|
| **Port primitives** (35 primitives outside `KLSyntax`; no ledger entry of its own yet, OB-JIT-LOWER-FRAGMENT is nearest) | model each in KLPort with a contract; or leave as residual (default) | all 35: +172 / +72 / +72. The 3 identity primitives alone: +22 / +9 / +9. The other 32 alone: +140 / +59 / +59 | identity 3: -48 / -480 / -480. Other 32: -178 / -581 / -581 |
| **eval-kl** (16 definitions; OB-JIT-LOWER-GENERAL) | admit through the shipped-checker option; or residual (default). Runtime eval-kl lowering correctness is out of Phase 2 scope | +9 / +0 / +0 | -16 / -450 / -16 |
| **Identity primitives** (`same?`, `tagged?`, `deref`; OB-JIT-IDENTITY-MODEL) | give pairs, strings and reals identity in the model; or residual (default). Covers the `port:` rows for these three plus identity `yes`: 48 definitions | +22 / +9 / +9, as the port row | -48 / -480 / -480 |
| **NaN `=`** (two computed operands, 206 definitions; OB-JIT-NAN-IDENTITY) | (a) model NaN identity, so every two-computed `=` is admitted; (b) a static non-real guard, which admits a two-computed `=` only when one operand is statically never a real; (c) residual (default) | (a) +171 / +129 / +129. (b) +98 / +18 / +18. (c) +0 | dropping all of `=` costs -206 / -648 / -648. Taking (b) instead of (a) costs -98 / -618 / -618 |

How to read it:

- The decisions are not independent once the closure limit applies. Every option is needed for the giant component,
  so under D-src or D-low no single option pays off much until the rest are taken too. With every option taken, the
  forecast is 955 of 955 under all three designs. That figure is a prediction, not a count of anything validated.
- (b)'s guard set (`NONREAL` in the script) is a Python heuristic. A Rocq version would need its own static kind
  judgment.
- `eq-symbol-const` (201 definitions) is **not** a decision item. OB-JIT-SYM-INJECTIVE is discharged, so `=` with a
  symbol constant is an ordinary emit feature. It was row A2 of the T02 forecast; `Comp` now admits it, so at the
  rerun it is part of row 0.

## Residuals, in short

With every non-decision feature and family admitted, 391 of 955 definitions are still predicted to be rejected. Each
is listed under the first decision item it needs:

- two-computed `=`: 171 (98 guardable, 73 unguarded)
- identity port primitive: 46
- other port primitives: 158, led by `shen-jit.symbol-kind` 43, `shen-jit.append` 35, `shen-jit.absvector3` 13 and
  `shen-jit.integer?` 10
- eval-kl: 16

The full list is below. These counts are predictions; nothing was accepted beyond Rocq's 148 (src judge).

## Not done, or UNKNOWN

- Chain depth is a lower bound. Node-level depth for unmarked rewrites (cond, sugar, copying, bind!) needs a tick that
  records the node. That means changing `instrument_lower.py` and `capture_passes.shen`, which are outside this task.
- The forecast assumes each feature, once added to Comp, admits exactly the code `lower.shen` emits for it. A feature
  whose rule turns out narrower than the emitted shapes would lower the counts. The current set's 0 mismatches do not
  test features that are not yet in Comp.
- The callee closure leaves out dynamic application and function-symbol constants, as above.
- `SKIP_DIFF=1 scripts/check-shen-jit.sh` passed on this branch: tables match, 70 audited statements closed, rocqchk
  passed, stage0 111 accepted of 955 as recorded. The differential was not run, and neither were `gate_tests.sh` or
  the full gate: UNKNOWN on this branch. This change adds no theorem, checker or relation. (That is the T02 run; the
  rerun's lane result is in the `p2/eq-guard-merge` commit message.)

---

The rest of this file is `feature_census.py`'s output, unedited.

<!-- generated by tests/shen-jit/feature_census.py; census, not proof -->

## Consistency with the Rocq judge (current feature set)

| variant | Rocq accepted | predicted | mismatches |
|---|---:|---:|---:|
| src | 148 | 148 | 0 |
| tf | 174 | 174 | 0 |
| nf (held out) | 150 | 150 | 0 |

definitions: 955; unreadable (verdict 0) in src, nf or tf: 0; unexplained mismatches: 0

## Forecast: cumulative feature sets in census rank order

Each row adds one emit feature or front family (`fam:`) to everything above it, picked
greedily: the one that admits the most further definitions on its own (ties by name; when
none admits any alone, the one blocking the most remaining definitions). Part A ranks the
features and families that family tasks own; part B then ranks the decision items, each of
which defaults to a named residual. Columns count definitions of 955 predicted to validate
source -> norm -> bytecode with that set: **direct** (the definition alone), **D-src** (direct,
and every definition in its transitive sealed-callee closure direct too: a store of source
bodies with direct acceptance), **D-low** (direct, and every definition in its closure
emit-accepted on its lowered body: a lowered store), **D-inl** (as D-src, closure over the
inlining-marker edges only), and **emit** (norm -> bytecode alone, front families ignored).
Census forecast, not proof.

| # | added | direct | D-src | D-low | D-inl | emit |
|---:|---|---:|---:|---:|---:|---:|
| 0 | (current Comp; row 0 direct = Rocq src, emit = Rocq tf) | 148 | 63 | 63 | 148 | 174 |
| A1 | `value/set` | 189 | 93 | 93 | 189 | 224 |
| A2 | `simple-error` | 225 | 119 | 120 | 225 | 264 |
| A3 | `vector` | 247 | 141 | 142 | 247 | 293 |
| A4 | `fam:inline` | 273 | 157 | 158 | 273 | 293 |
| A5 | `do` | 298 | 165 | 166 | 298 | 328 |
| A6 | `fam:cond` | 323 | 168 | 168 | 323 | 328 |
| A7 | `prim:cn` | 360 | 171 | 171 | 360 | 365 |
| A8 | `lambda` | 394 | 171 | 171 | 394 | 400 |
| A9 | `apply-dynamic` | 410 | 178 | 178 | 410 | 416 |
| A10 | `io` | 417 | 179 | 179 | 417 | 423 |
| A11 | `prim:str` | 425 | 181 | 181 | 425 | 431 |
| A12 | `prim:intern` | 455 | 191 | 191 | 455 | 462 |
| A13 | `freeze` | 459 | 191 | 191 | 459 | 468 |
| A14 | `prim:n->string` | 463 | 194 | 194 | 463 | 472 |
| A15 | `error-to-string` | 464 | 194 | 194 | 464 | 473 |
| A16 | `fam:fold-arith` | 465 | 194 | 194 | 465 | 473 |
| A17 | `fam:sugar` | 466 | 194 | 194 | 466 | 473 |
| A18 | `prim:/` | 467 | 197 | 197 | 467 | 474 |
| A19 | `prim:pos` | 468 | 198 | 198 | 468 | 475 |
| A20 | `prim:tlstr` | 477 | 203 | 203 | 477 | 484 |
| A21 | `prim:string->n` | 484 | 209 | 209 | 484 | 491 |
| A22 | `thaw` | 485 | 210 | 210 | 485 | 499 |
| A23 | `fam:thaw-sugar` | 492 | 213 | 213 | 492 | 499 |
| A24 | `fam:fold-cons` | 492 | 213 | 213 | 492 | 499 |
| A25 | `folded-const` | 533 | 224 | 224 | 533 | 542 |
| A26 | `fam:trap-sugar` | 533 | 224 | 224 | 533 | 542 |
| A27 | `trap` | 556 | 229 | 229 | 556 | 565 |
| A28 | `let-freeze` | 556 | 229 | 230 | 556 | 573 |
| A29 | `fam:copy` | 561 | 233 | 233 | 561 | 573 |
| A30 | `fam:share` | 564 | 235 | 235 | 564 | 573 |
| A31 | `fam:bind` | 564 | 235 | 235 | 564 | 573 |
| B1 | `eq-two-computed` (decision) | 662 | 253 | 253 | 642 | 672 |
| B2 | `eq-two-computed-unguarded` (decision) | 735 | 364 | 364 | 735 | 746 |
| B3 | `port:shen-jit.symbol-kind` (decision) | 778 | 405 | 405 | 778 | 789 |
| B4 | `port:shen-jit.append` (decision) | 814 | 415 | 415 | 814 | 826 |
| B5 | `port:shen-jit.deref` (decision) | 838 | 421 | 421 | 838 | 850 |
| B6 | `port:shen-jit.absvector3` (decision) | 852 | 424 | 424 | 852 | 864 |
| B7 | `port:shen-jit.integer?` (decision) | 865 | 433 | 433 | 865 | 877 |
| B8 | `fam:eval-kl` (decision) | 877 | 433 | 433 | 877 | 877 |
| B9 | `port:shen-jit.tagged?` (decision) | 888 | 435 | 435 | 888 | 888 |
| B10 | `port:shen-jit.dict-put` (decision) | 893 | 436 | 436 | 893 | 893 |
| B11 | `port:shen-jit.pvar-offset` (decision) | 898 | 443 | 443 | 898 | 898 |
| B12 | `port:shen-jit.pvar?` (decision) | 907 | 446 | 446 | 907 | 907 |
| B13 | `port:shen-jit.same?` (decision) | 911 | 458 | 458 | 911 | 911 |
| B14 | `port:shen-jit.dict-entries` (decision) | 914 | 461 | 461 | 914 | 914 |
| B15 | `port:shen-jit.read-file` (decision) | 917 | 463 | 463 | 917 | 917 |
| B16 | `port:shen-jit.symbol?` (decision) | 920 | 466 | 466 | 920 | 920 |
| B17 | `port:shen-jit.vector?` (decision) | 923 | 468 | 468 | 923 | 923 |
| B18 | `port:shen-jit.decimal` (decision) | 925 | 480 | 480 | 925 | 925 |
| B19 | `port:shen-jit.pvar` (decision) | 927 | 490 | 490 | 927 | 927 |
| B20 | `port:shen-jit.sealed?` (decision) | 929 | 491 | 491 | 929 | 929 |
| B21 | `port:shen-jit.inline-body` (decision) | 931 | 493 | 493 | 931 | 931 |
| B22 | `port:char-stream?` (decision) | 932 | 494 | 494 | 932 | 932 |
| B23 | `port:read-unit-string` (decision) | 939 | 495 | 495 | 939 | 939 |
| B24 | `port:shen-jit.exit` (decision) | 941 | 495 | 495 | 941 | 941 |
| B25 | `port:shen-jit.dict-find` (decision) | 942 | 496 | 496 | 942 | 942 |
| B26 | `port:shen-jit.quiet?` (decision) | 944 | 496 | 496 | 944 | 944 |
| B27 | `port:shen-jit.dict-remove` (decision) | 945 | 497 | 497 | 945 | 945 |
| B28 | `port:shen-jit.filled-vector` (decision) | 946 | 497 | 497 | 946 | 946 |
| B29 | `port:shen-jit.hash` (decision) | 947 | 498 | 498 | 947 | 947 |
| B30 | `port:shen-jit.install` (decision) | 948 | 498 | 498 | 948 | 948 |
| B31 | `port:shen-jit.mark-toplevel` (decision) | 949 | 498 | 498 | 949 | 949 |
| B32 | `port:shen-jit.sealing` (decision) | 950 | 499 | 499 | 950 | 950 |
| B33 | `port:shen-jit.trace-text` (decision) | 951 | 499 | 499 | 951 | 951 |
| B34 | `port:shen-jit.u8` (decision) | 952 | 500 | 500 | 952 | 952 |
| B35 | `port:write-string` (decision) | 953 | 500 | 500 | 953 | 953 |
| B36 | `port:shen-jit.bytes-length` (decision) | 953 | 500 | 500 | 953 | 953 |
| B37 | `port:shen-jit.string->bytes` (decision) | 954 | 500 | 500 | 954 | 954 |
| B38 | `port:shen-jit.write-bytes` (decision) | 955 | 955 | 955 | 955 | 955 |

## Feature and family usage (definitions needing each)

| feature or family | definitions | sole blocker |
|---|---:|---:|
| `fam:inline` | 528 | 13 |
| `fam:cond` | 462 | 0 |
| `value/set` | 242 | 41 |
| `simple-error` | 214 | 26 |
| `eq-two-computed` | 206 | 0 |
| `prim:cn` | 168 | 4 |
| `do` | 129 | 7 |
| `vector` | 118 | 19 |
| `eq-two-computed-unguarded` | 98 | 0 |
| `lambda` | 98 | 7 |
| `fam:fold-cons` | 96 | 0 |
| `folded-const` | 96 | 0 |
| `prim:intern` | 90 | 0 |
| `prim:str` | 81 | 2 |
| `port:shen-jit.symbol-kind` | 50 | 2 |
| `port:shen-jit.append` | 41 | 1 |
| `fam:thaw-sugar` | 37 | 0 |
| `port:shen-jit.deref` | 37 | 1 |
| `thaw` | 37 | 1 |
| `fam:trap-sugar` | 36 | 0 |
| `trap` | 36 | 0 |
| `apply-dynamic` | 33 | 7 |
| `let-freeze` | 24 | 0 |
| `fam:copy` | 23 | 0 |
| `freeze` | 23 | 1 |
| `port:shen-jit.absvector3` | 22 | 1 |
| `prim:pos` | 22 | 1 |
| `prim:tlstr` | 20 | 0 |
| `io` | 18 | 1 |
| `prim:string->n` | 18 | 0 |
| `fam:eval-kl` | 16 | 1 |
| `port:shen-jit.integer?` | 14 | 1 |
| `port:shen-jit.pvar-offset` | 13 | 0 |
| `port:shen-jit.pvar?` | 12 | 1 |
| `port:shen-jit.tagged?` | 12 | 1 |
| `prim:n->string` | 12 | 0 |
| `port:char-stream?` | 11 | 0 |
| `port:read-unit-string` | 9 | 0 |
| `fam:bind` | 7 | 0 |
| `fam:fold-arith` | 6 | 0 |
| `port:shen-jit.dict-put` | 5 | 1 |
| `fam:share` | 4 | 0 |
| `fam:sugar` | 4 | 0 |
| `port:shen-jit.read-file` | 4 | 2 |
| `port:shen-jit.same?` | 4 | 0 |
| `port:shen-jit.sealed?` | 4 | 0 |
| `port:shen-jit.symbol?` | 4 | 0 |
| `port:shen-jit.vector?` | 4 | 2 |
| `error-to-string` | 3 | 0 |
| `port:shen-jit.dict-entries` | 3 | 1 |
| `port:shen-jit.dict-find` | 3 | 0 |
| `port:shen-jit.bytes-length` | 2 | 0 |
| `port:shen-jit.decimal` | 2 | 0 |
| `port:shen-jit.exit` | 2 | 0 |
| `port:shen-jit.hash` | 2 | 1 |
| `port:shen-jit.inline-body` | 2 | 0 |
| `port:shen-jit.pvar` | 2 | 1 |
| `port:shen-jit.quiet?` | 2 | 0 |
| `port:shen-jit.string->bytes` | 2 | 0 |
| `port:write-string` | 2 | 0 |
| `prim:/` | 2 | 1 |
| `port:shen-jit.dict-remove` | 1 | 1 |
| `port:shen-jit.filled-vector` | 1 | 0 |
| `port:shen-jit.install` | 1 | 0 |
| `port:shen-jit.mark-toplevel` | 1 | 0 |
| `port:shen-jit.sealing` | 1 | 0 |
| `port:shen-jit.trace-text` | 1 | 0 |
| `port:shen-jit.u8` | 1 | 1 |
| `port:shen-jit.write-bytes` | 1 | 0 |

## Chain depth (rewrites stacked at one node; witness-structural lower bound)

Per definition, the most rewrites the witness shows stacked at one node: directly nested inlining
markers, plus one when a folded constant list sits directly under them. Rewrites that leave
no mark in the normal form (cond, sugar, freeze copying, bind!) are counted per definition by
the ticks (next table) but cannot be placed at a node from the capture, so this is a lower bound.

| chain depth | definitions |
|---:|---:|
| 0 | 427 |
| 1 | 362 |
| 2 | 166 |

| front families fired (per definition) | definitions |
|---:|---:|
| 0 | 194 |
| 1 | 387 |
| 2 | 308 |
| 3 | 54 |
| 4 | 8 |
| 5 | 3 |
| 7 | 1 |

| rewrite firings (ticks, per definition) | definitions |
|---|---:|
| 0 | 194 |
| 1 | 259 |
| 2-4 | 227 |
| 5-9 | 107 |
| 10-19 | 91 |
| 20-49 | 60 |
| 50-99 | 10 |
| 100+ | 7 |

## Sealed-callee closure (call edges and inlining-marker edges to the 955 stage 0 definitions)

| closure size (excluding itself) | definitions |
|---|---:|
| 0 | 219 |
| 1-9 | 233 |
| 10-99 | 53 |
| 100-299 | 0 |
| 300+ | 450 |

marker edges only: 0: 427, 1-9: 509, 10-99: 19, 100+: 0

largest strongly connected component (call + marker edges): 181 definitions; 450 definitions
(itself included) have it inside their closure. Other components of size > 1: 6, 6, 3, 3, 3, 2, 2.
Dynamic application and function-symbol constants are not edges, so every closure is a lower bound.

call edges 1836, inlining edges 1859; calls to names outside stage 0: 0 sites over 0 names: 

## Identity dependence

yes: uses shen-jit.deref, shen-jit.deref=, shen-jit.same?, shen-jit.tagged?; maybe: no such primitive, but an = on two computed operands of unknown static
kind (identity of heap objects or NaN may decide it); no: neither.

| identity | definitions |
|---|---:|
| yes | 48 |
| maybe | 84 |
| no | 823 |

## Decisions (counts each option unlocks)

Baseline: every feature and family except the decision items (564 direct; D-src 235; D-low 235).
Each row adds only that option to the baseline. Census forecast.

| option | adds | direct | D-src | D-low |
|---|---|---:|---:|---:|
| identity port primitives | `port:shen-jit.deref`, `port:shen-jit.same?`, `port:shen-jit.tagged?` | +22 | +9 | +9 |
| port primitives other than identity | 32 features | +140 | +59 | +59 |
| all port primitives | 35 features | +172 | +72 | +72 |
| eval-kl (shipped checker) | `fam:eval-kl` | +9 | +0 | +0 |
| NaN `=`: residual (default) |  | +0 | +0 | +0 |
| NaN `=`: static non-real guard | `eq-two-computed` | +98 | +18 | +18 |
| NaN `=`: model NaN identity | `eq-two-computed`, `eq-two-computed-unguarded` | +171 | +129 | +129 |
| all decision items | 38 features | +391 | +720 | +720 |

Leave one out: every decision item admitted except the named group (what that group costs).

| all decision items except | direct | D-src | D-low |
|---|---:|---:|---:|
| identity port primitives | -48 | -480 | -480 |
| port primitives other than identity | -178 | -581 | -581 |
| eval-kl | -16 | -450 | -16 |
| NaN `=` (residual: both two-computed items) | -206 | -648 | -648 |
| NaN `=` unguarded only (static non-real guard chosen) | -98 | -618 | -618 |

Decision items needed inside the largest component (181 definitions): `eq-two-computed` 32, `eq-two-computed-unguarded` 24, `port:shen-jit.append` 10, `port:shen-jit.symbol-kind` 6, `fam:eval-kl` 4, `port:shen-jit.absvector3` 4, `port:shen-jit.tagged?` 4, `port:char-stream?` 3, `port:read-unit-string` 3, `port:shen-jit.dict-put` 3, `port:shen-jit.symbol?` 3, `port:shen-jit.dict-find` 2, `port:shen-jit.quiet?` 2, `port:shen-jit.filled-vector` 1, `port:shen-jit.install` 1, `port:shen-jit.integer?` 1, `port:shen-jit.sealed?` 1, `port:shen-jit.vector?` 1.

## Residuals by reason (all non-decision features and families admitted)

Each definition still rejected is listed under the first decision item it needs, in this order:
eval-kl, port primitives (identity first), = on two computed operands.

| reason | definitions | examples |
|---|---:|---|
| = on two computed operands (static non-real guard applies) | 98 | `shen.<signature>`, `shen.<rules>`, `shen.<patterns>`, `shen.<constructor>` |
| = on two computed operands (unguarded) | 73 | `shen.<define>`, `shen.<pattern>`, `shen.arity-chk`, `shen.choicepoint` |
| identity port primitive | 46 | `shen.unprotect`, `shen.linearise`, `shen.free-var-chk`, `shen.custom-pattern-triple-stack` |
| port primitive shen-jit.symbol-kind | 43 | `shen.<name>`, `shen.extract-vars`, `shen.find-free-vars`, `shen.free-variable?` |
| port primitive shen-jit.append | 35 | `shen.factor-recognisors`, `shen.x.expand-dynamic.expand-lambda-entries`, `shen.x.programmable-pattern-matching.surface-application`, `shen.x.type-annotations.annotate` |
| eval-kl | 16 | `shen.lambda-entry`, `shen.x.expand-dynamic.expand-dynamic`, `shen.x.expand-dynamic.expand-declare`, `shen.x.expand-dynamic.expand-declare/checked` |
| port primitive shen-jit.absvector3 | 13 | `shen.<rule>`, `shen.pivot-on`, `shen.x.expand-dynamic.split-defuns`, `shen.x.namespaces.qualify` |
| port primitive shen-jit.integer? | 10 | `prolog-memory`, `shen.x.programmable-pattern-matching.remove-nth`, `shen-jit.lower.inlinable?`, `shen-jit.lower.inline-numbers` |
| port primitive shen-jit.dict-put | 5 | `shen-jit.lower.fill-table`, `shen-jit.lower.constant`, `shen.dict->`, `put` |
| port primitive char-stream?, read-unit-string | 4 | `lineread`, `read`, `shen.my-read-byte`, `y-or-n?` |
| port primitive shen-jit.pvar-offset | 4 | `shen.bind!`, `shen-jit.undo`, `shen.bindv`, `shen.unwind` |
| port primitive shen-jit.dict-entries | 3 | `shen.dict-keys`, `shen.dict-values`, `shen.dict-fold` |
| port primitive shen-jit.integer?, shen-jit.symbol-kind | 3 | `shen.x.expand-dynamic.expand-initializer-h`, `shen.use-history`, `shen.peek-history` |
| port primitive shen-jit.read-file | 3 | `read-file`, `read-file-as-bytelist`, `read-file-as-string` |
| port primitive shen-jit.symbol? | 3 | `shen-jit.lower.check-defun`, `shen-jit.lower.check-params`, `shen-jit.lower.literal?` |
| port primitive shen-jit.vector? | 3 | `vector?`, `shen.+vector?`, `shen.vector->str` |
| port primitive shen-jit.decimal | 2 | `shen.compute-integer`, `shen.compute-E` |
| port primitive shen-jit.dict-find, shen-jit.quiet? | 2 | `shen.<-dict`, `get` |
| port primitive shen-jit.inline-body, shen-jit.sealed? | 2 | `shen-jit.lower.open-body`, `shen-jit.lower.inline-body` |
| port primitive shen-jit.pvar | 2 | `shen.newpv`, `shen.make-prolog-variable` |
| port primitive char-stream? | 1 | `shen.process-read-byte` |
| port primitive char-stream?, read-unit-string, shen-jit.append | 1 | `shen.read-loop` |
| port primitive char-stream?, read-unit-string, shen-jit.exit | 1 | `shen-jit.repl-read` |
| port primitive char-stream?, shen-jit.bytes-length, shen-jit.string->bytes | 1 | `pr` |
| port primitive shen-jit.absvector3, shen-jit.append, shen-jit.symbol-kind | 1 | `shen.linearise-h` |
| port primitive shen-jit.absvector3, shen-jit.pvar? | 1 | `shen.x.type-annotations.reify-type` |
| port primitive shen-jit.append, shen-jit.symbol-kind | 1 | `shen-jit.lower.reuse` |
| port primitive shen-jit.bytes-length, shen-jit.string->bytes | 1 | `shen.str->bytes` |
| port primitive shen-jit.dict-find | 1 | `shen-jit.recorded?` |
| port primitive shen-jit.dict-remove | 1 | `shen.dict-rm` |
| port primitive shen-jit.exit | 1 | `shen.x.launcher.main` |
| port primitive shen-jit.filled-vector | 1 | `shen.dict` |
| port primitive shen-jit.hash | 1 | `hash` |
| port primitive shen-jit.install | 1 | `shen-jit.eval-kl` |
| port primitive shen-jit.mark-toplevel | 1 | `shen.read-evaluate-print` |
| port primitive shen-jit.pvar? | 1 | `shen.pvar?` |
| port primitive shen-jit.sealed? | 1 | `shen-jit.lower.named-call` |
| port primitive shen-jit.sealed?, shen-jit.symbol? | 1 | `shen-jit.lower.norm` |
| port primitive shen-jit.sealing | 1 | `shen-jit.seal` |
| port primitive shen-jit.trace-text | 1 | `shen.toplevel-display-exception` |
| port primitive shen-jit.u8 | 1 | `shen-jit.buffer->list` |

residual total: 391

