# Chez nanopass compilation to ARM: E2E-22 first lane (Wave C)

This is the first work on package 22 of [END-TO-END-PLAN](END-TO-END-PLAN.md),
"Close Chez compilation to ARM". The approach is translation validation. The
Chez compiler stays an untrusted producer. Rocq checkers accept or reject what
it actually produced. **The package is in progress. Its exit criterion is not
met.** Two pass steps are validated, for one function.

Every result below carries one of these evidence labels:

* **universal theorem**: a Rocq theorem quantified over all inputs of a
  checker, for example "for every pair of printed terms the checker accepts".
* **ground derivation**: a universal checker theorem applied to one captured
  artifact. It says nothing about other programs.
* **sampled agreement**: two captures compared. It is not a theorem.
* **capture**: bytes recorded from a real Chez process. Nothing about them is
  proved.

## 1. Pins

| Item | Pin |
|---|---|
| Chez Scheme | 10.3.0, the version shen-scheme v0.52 builds (`csversion ?= 10.3.0`). The release archive `csv10.3.0.tar.gz` has sha256 `d237d987...cbc2c`. The git tag is `v10.3.0`, commit `adfaf9e6d47a`. The checked-out `s/` files are byte-identical to the archive's (hashes in `spec/chez-passes.json`) |
| nanopass framework | the copy vendored in the release archive (`nanopass/nanopass/language.ss`, sha256 `47761671...`). The git checkout has an empty submodule here |
| `s/np-languages.ss` | sha256 `db2c01ec...9f2e`. It is stored in `ports/chez-np/upstream/` under Apache-2.0 (`LICENSES/Chez-Scheme.txt`) |
| Binaries | the ARM lane's build from `nix/arm/build-chez-10.3.0-aarch64.sh`. tarm64le `scheme` / `petite.boot` / `scheme.boot` are `21900313...` / `59c03809...` / `43adf79b...`, as in `ports/arm/README.md`. They run under qemu-user 11.1.2. The ta6le stage-1 host build is `e993641e...` / `fe07ceb2...` / `0e65ad29...` |
| Input form | `(define (kl:buri-arm-add V3015 V3016) (+ V3015 V3016))`, the exact Shen-Scheme v0.52 output for `(define buri-arm-add X Y -> (+ X Y))` |
| Parameters | the Chez defaults, which equal what a running Shen-Scheme v0.52 reports (`ports/arm/scripts/shen-scheme-params.shen`). The dump records them: optimize-level 0, debug-level 1, generate-inspector-information #t, enable-type-recovery #t, generate-interrupt-trap #t, compile-interpret-simple #t, commonization-level 0, compile-profile #f, `$lift-closures` #t, `$optimize-closures` #t, `$loop-unroll-limit` 0, `$enable-check-prelex-flags` #f, current-eval = compile |

## 2. The pipeline that actually runs (deliverable 1)

The machine-readable inventory is [`spec/chez-passes.json`](../spec/chez-passes.json).
`ports/chez-np/scripts/chez-passes.py` regenerates it from a Chez source tree
and the trace. Rocq re-derives the executed order from the packaged trace
(`ChezNpValidate.trace_pass_order`).

`eval` with current-eval = compile goes through `compile` (compile.ss
1784-1823). The steps are:

1. **Front end. These are not np-compile passes.** `sc-expand` (syntax.ss
   6783) runs first. Then `$cpvalid` runs, then `run-cp0`, whose default
   (cmacros.ss 2329) is `(cp0 (cp0 x))`. The cp0 / cptypes / cpletrec triple
   therefore runs **twice**: cptypes runs because enable-type-recovery is #t,
   and the prelex-flag checks are off. Then `$cpcheck` runs, then
   `$cpcommonize`, which is the identity at commonization-level 0
   (cpcommonize.ss 580-585). compile-interpret-simple is on, but the shortcut
   is not taken because a `define` of a lambda is not "simple".
2. **`c-compile`** (compile.ss 68-74) wraps the result as a library-like
   `main` case-lambda.
3. **`$np-compile`** (cpnanopass.ss 10795-10838). It runs 28 passes through the
   `pass` macro, then `np-after-calling-conventions` (10771-10793) runs 12
   more. The conditional ones resolve as follows for these parameters:
   * `np-lift-well-known-closures` runs (`$lift-closures`).
   * `np-expand/optimize-closures` runs (`$optimize-closures`), not
     `np-expand-closures`.
   * `np-profile-unroll-loops` is skipped (the unroll limit is 0).
   * `np-add-block-source!` and `np-insert-profiling` are skipped
     (compile-profile #f).
4. **`np-allocate-registers`** is the aggregate pass. It runs 13 traced
   sub-passes per lambda: `do-live-analysis!`, `record-call-live!`,
   `do-spillable-conflict!`, `assign-frame!`, `record-inspector-information!`,
   `assign-new-frame!`, `record-fp-offsets!`, `finalize-frame-locations!`,
   `select-instructions!`, `do-unspillable-conflict!`, `assign-registers!`,
   `finalize-register-locations!` and `expose-overflow-check-blocks!`.
   * `identify-poison!` is skipped (it needs more than 1000 spillables).
   * Here the 13 sub-passes run once for `kl:buri-arm-add` and once for
     `main`, because the spill loop is not re-entered.
   * Instruction selection (`select-instructions!`, with the `arm64.ss`
     instruction definitions) is one of these sub-passes.
5. `np-remove-repeater-blocks-again!` and `np-optimize-block-order!` run, then
   `np-generate-code` (cpnanopass.ss 8086-8359, using the `arm64.ss`
   assembler). It returns a `$c-func` whose code-list holds `(long . n)` words
   and relocation markers.
6. **These are not passes:** `c-mkcode` (compile.ss 102-190) lays out the
   code-list, and `arm64_set_abs` (c/fasl.c 1714-1735) writes absolute
   addresses into the relocation windows when the code object is installed.

In all, 40 nanopass passes and 26 sub-pass outputs were traced for this form.
`spec/chez-passes.json` gives each pass's language, file, line range,
condition, whether it ran, and whether its printed output changed for this
function. Languages run from Lsrc through L1 ... L4.9375, L5, L6, L7, L9 (there
is no L8), L9.5, L9.75, L10, L10.5, L11, L12, L12.5, L13, L13.5, L14, L15a-e and
L16. `$np-expand-primitives` is defined in cpprim.ss (106-305) and maps L7 to
L9. Note one property of this function: printed output did not change across
18 of the 40 traced passes.

## 3. Grammar capture (deliverable 2)

`scripts/package-chez-np.py languages` copies the exact bytes of
`np-languages.ss` into `rocq/ChezNpLanguagesInput.v`, together with the byte
spans of its 28 `define-language` forms. It is packaging only. Rocq then does
the following:

* `ChezNpReader` is an inert s-expression reader written in Gallina. It covers
  only the lexical forms that occur in the forms and the dumps. Anything else
  is rejected.
* `ChezNpGrammar` implements nanopass `extends` resolution in Rocq, following
  `language.ss` in the vendored framework: removals, additions, list orders
  and dropping a nonterminal that has lost all its productions.
* `ChezNpGrammarCheck` (ground derivations) proves four things:
  * the spans are exactly the occurrences of `(define-language ` in the file
    (`np_languages_spans_complete`);
  * there are 28 forms;
  * the language names in order (`np_language_names`);
  * `np_languages_resolved`: Rocq's own resolution of every language equals the
    grammar data from which `rocq/ChezNpSyntax.v` was generated.
* `rocq/ChezNpSyntax.v` holds one mutual inductive type per language, for all
  28 languages. Every `extends` is resolved, and this includes L15a-L16, which
  enter `np-generate-code`. Terminals are uninterpreted `sexp` data,
  `(maybe e)` becomes `option` and `x ...` becomes `list`. The Python generator
  is therefore not trusted for the grammars: a bug changes the data and fails
  `np_languages_resolved`. The mutant `ChezNpWrongGrammar` checks exactly this.
* `spec/chez-np-languages.json` is the same resolved grammar as a reading aid.
* `make prove` regenerates all three files and diffs them. It also checks
  `ports/chez-np/SHA256SUMS`.

## 4. Intermediate dumps (deliverable 3)

`ports/chez-np/scripts/np-dump.ss` runs the real `eval` with
`($np-tracer #t)`, so every pass prints its own output through Chez's
unparser. The printer settings are `print-gensym 'pretty/suffix` and
`print-graph #t`. It changes one printing rule: the `info` record writer now
prints the record's fields instead of `#<info>`. The script also replays the
untraced front end through the same internal entry points (`sc-expand`,
`$cpvalid`, `$cp0`, `$cptypes`, `$cpletrec`, `$cpcheck`, `$cpcommonize`, each
printed with `$uncprep`). The replay's result matches the real pipeline's
`expand/optimize-output` up to gensym suffixes.

| File | What |
|---|---|
| `ports/chez-np/tarm64le-buri-arm-add.np` | **capture**: the tarm64le native Chez (qemu-user) with parameters, front end and all 66 traced outputs, 151 KB. It is deterministic: two runs, and a rerun through `run-np-dump.sh`, are byte-identical |
| `ports/chez-np/ta6le-buri-arm-add.np` | **capture**: the same on the x86_64 host build |
| comparison | **sampled agreement**: the two traces are identical through the front end and the first 18 nanopass outputs, up to `np-unbox-fp-vars!`. They first differ at `$np-expand-primitives`: arm64 inserts `%store-store-fence` before the remembered-set store |

The register-allocator sub-passes print a block listing and a dot graph, not
an s-expression. They are kept as text and not read by Rocq.

**Limitation.** The unparse forms of L1-L13 omit most `info` fields. Examples
are call flags, lambda names and clause info. The dumps therefore cannot show
what `np-suppress-procedure-checks` changes. Their faithfulness to the
in-memory IR is the new obligation `OB-CHEZ-NP-PRINTER`.

## 5. First per-pass validators (deliverable 4)

All the code is in `rocq/ChezNpCore.v`, `ChezNpReloc.v` and `ChezNpValidate.v`.
The audit is `rocq/Audit_Nanopass.v`: 20 statements, all closed.

### 5.1 `np-recognize-mrvs` (L4 to L4.5): syntactic

* The semantics is a core big-step semantics with fuel (`ChezNpCore.eval`). Its
  values are data, primrefs and closures. Its environments have `letrec`
  frames.
  * It is parametric in an arbitrary primitive semantics over an arbitrary
    world type and an arbitrary truthiness test.
  * It is also parametric in an arbitrary **argument-evaluation-order policy**,
    because Chez leaves the order unspecified. A policy that is not a
    permutation makes evaluation fail.
  * `let` right-hand sides are evaluated in printed order.
* `denote` reads printed L4 and L4.5 terms into that core. It reads
  application `(e0 e1 ...)` in L4 and `(call #f e0 e1 ...)` in L4.5, plus
  quote, if, begin, let, letrec and fixed-arity case-lambda. Every other
  construct is rejected: foreign, profile, pariah, rest clauses, mvcall,
  mvlet and direct-call labels.
* **Universal theorem** `check_recognize_mrvs_sound`: if the checker accepts,
  both terms have the same denotation and, for every primitive semantics,
  order policy, fuel and world, the same result.
* **Ground derivation** on the captured function:
  `mrvs_buri_arm_add_checked`, and from it `mrvs_buri_arm_add_preserves`.
* `mrvs_rejects_wrong_pairs` shows that the checker rejects the swapped pair
  and a later pass's output.

### 5.2 Printed identity of same-language passes: trivially sound

`check_printed_identity_sound` is a universal theorem: equal printed terms
mean the same under any semantics of the printed form.

`identity_passes_checked` is a ground derivation. For this function, ten
passes print their input unchanged:

* `np-sanitize-bindings` and `np-suppress-procedure-checks` (L4);
* `np-optimize-direct-call`, `np-identify-scc` and
  `np-lift-well-known-closures` (L6);
* `np-simplify-if` and `np-unbox-fp-vars!` (L7);
* `np-rebind-on-ruined-path` (L9.5);
* `np-optimize-pred-in-value` (L9.75);
* `np-compute-loop-depth!` (L15a).

**This is identity of the printed form only.** `np-suppress-procedure-checks`
exists to change call info, which is not printed. This result is weak by
design. It is recorded because it is cheap and exact, not because it closes
those passes.

### 5.3 `np-generate-code` output to the exact 152 tarm64le bytes: relocation instance

`ChezNpReloc.layout` follows `c-mkcode` for the arm64 entries:

* `long` and `quad` entries are little-endian words;
* `code-top-link` writes its own offset plus `code-data-disp` (65);
* each `arm64-abs`, `arm64-call` or `arm64-jump` marker registers a window of
  16 or 20 preceding bytes.

`set_abs_word` and `get_abs` transcribe `arm64_set_abs` and `arm64_get_abs`.

**Universal theorem** `check_code_object_sound`: if the checker accepts, then
`captured = instantiate template relocs (items_of captured relocs)`, each
template window is `arm64_set_abs` of item 0, the size matches, and the
relocation offsets and targets match the code object's relocation table.

**Ground derivations** for `kl:buri-arm-add`:

* `code_shape`: size 152, windows at offsets 64, 112 and 132, for the library
  entries `event`, `+` and `doargerr`, which agree with
  `ports/arm/chez/chez1030-buri-arm-add.relocs`.
* `codegen_buri_arm_add_checked` and `codegen_buri_arm_add_instance`: the
  captured bytes are exactly np-generate-code's template with its three
  relocation windows instantiated.
* `codegen_rejects_tampering`: a flipped non-relocated byte, a flipped
  relocation-window bit and a missing relocation-table entry are all rejected.

The captured relocation items, such as 139972745212416, are one qemu
process's absolute addresses plus 65. The theorem does not say that they point
at the right library code. Only the relocation table names the targets.

Three proof mutants were added: `ChezNpWrongByte`, `ChezNpWrongMrvs` and
`ChezNpWrongGrammar`.

## 6. Feasibility and scale (deliverable 5)

Class definitions, as in `spec/chez-passes.json`:

* **syntactic**: the output relates to the input by a shape change that can be
  checked from the two printed terms.
* **witness**: the check needs a certificate that the pass can export.
  Examples are free-variable lists, frame and register maps, and liveness.
* **semantic**: the check needs a semantics of primitives, machine integers,
  effects, interrupts or the ISA.

| Class | Passes | Estimated effort |
|---|---|---|
| syntactic | cpvalid, cpcheck, cpcommonize (level 0); recognize-let/loops, discover-names, sanitize-bindings, suppress-procedure-checks*, recognize-mrvs, name-anonymous-lambda†, optimize-direct-call, identify-scc, simplify-if, rebind-on-ruined-path, finalize-loops, optimize-pred-in-value, remove-complex-opera*‡, push-mrvs, normalize-context, flatten-case-lambda, repeater-blocks (both), add-in-links!, compute-loop-depth!, weight-references!, propagate-pariahty!, optimize-block-order! | about 1-3 days each with the core semantics extended. * needs info-visible dumps. † needs a closure-value relation (freshness plus environment weakening); a substitution semantics avoids it. ‡ fixes the unspecified argument order, so the semantics must keep order as a parameter, as the current core does |
| witness | cpletrec, convert-closures (free-variable lists), lift-well-known-closures, expand/optimize-closures (closure layout), impose-calling-conventions (registers, frame, return points; needs the E2E-21 calling-convention spec), expose-basic-blocks, all 13 register-allocator sub-passes | weeks. Witnesses come from instrumented dumps (register and frame homes, live sets) checked against L15/L16 semantics. Register allocation is the largest single item |
| semantic | expander, cp0 (twice), cptypes (twice), convert-assignments, expand-foreign, recognize-attachment, unbox-fp-vars!, `$np-expand-primitives` (cpprim), place-overflow-and-trap, insert-trap-check, expand-hand-coded, expose-allocation-pointer, np-generate-code (instruction encoding) | months. cp0 and cptypes are optimizers with effort counters; per-output validation needs a Scheme semantics (E2E-14/15) and primitive contracts (E2E-17). cpprim needs the fixnum-tag representation (E2E-21) and machine-integer semantics |

**Recommended next steps, in order:**

1. Instrument Chez to print raw IR with info fields. This removes the
   `OB-CHEZ-NP-PRINTER` gap. Chez exposes no raw unparser, so this means a
   patched build.
2. `$np-expand-primitives` for `+`. Its output is the fixnum fast path:
   `%logor` with `%log!test 7`, then `%+/ovfl`, with the overflow branch going
   to library `+`. The fast path is exactly what the E2E-20 Islaris theorem
   covers at the byte level.
3. A validator for L16 to code-list against the arm64 encoders. Together with
   5.3, this closes the last mile from L16 blocks to bytes.

**Connection to the ARM theorems.** 5.3 shows that the captured bytes are a
relocation instance of `np-generate-code` output. The E2E-20 Islaris theorem
(`ports/arm/islaris/buri_chez_add.v`) is about those same captured bytes: the
fast path `+0x00..+0x23` reaches the return address with X23 = a + b. The
sail-arm model theorem covers the `ADDS` word at `+0x14`. A full chain needs
four more links:

1. per-pass validation from Lsrc to L16, which is open for 38 passes;
2. an L16-to-instruction-semantics bridge;
3. relocation targets resolved to the library entries' own verified code
   (E2E-24);
4. the isla-trace-to-Coq-model bridge, which E2E-20 lists as open.

## 7. What remains open

* 38 of the 40 traced nanopass passes, the whole front end and the register
  allocator are unvalidated. Only one function was captured. Incremental
  compilation, `compile-file` and boot-image code are not examined.
* No aarch64 Shen-Scheme process exists. The tarm64le process stands in for it
  under the same parameters. This rests on x86_64 sampled agreement only
  (E2E-20).
* The Rocq checkers read printed IR. The printer is trusted
  (`OB-CHEZ-NP-PRINTER`).
* The relocation items are checked for shape only, not for target addresses.
* The release charter's `chez-scheme` pin is still marked "version
  unrecorded". That field belongs to E2E-03. This lane recorded 10.3.0 in
  `OB-CHEZ-COMPILATION`.
