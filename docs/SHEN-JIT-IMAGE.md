# Shen/JIT heap image (OB-JIT-IMAGE)

Status: **code objects lane-checked; the rest scoped into four sub-obligations with measured feasibility verdicts;
the sealing exclusion stated in Rocq as a named premise. Not discharged.** Since r21-image-lane,
`scripts/check-shen-jit.sh` decodes the pinned binary's image with
[`rocq/JitImage.v`](../rocq/JitImage.v) and Rocq proves `image_code_ok` by `vm_compute`: every one of the 955 stage 0
definitions of the 24 files loads (`JitBytecode.build_code`) to exactly the code object its function cell holds in the
image. `code_check_sound` (in `Audit_Jit`, closed) states what that gives. `image_code_ok` and `image_mutants_caught`
are each "Closed under the global context" (since `0595b57`: the reader writes the image's bytes as constructors of the
ordinary inductive `byte` and Rocq joins them, so no primitive integer is involved), and the lane fails unless both
print exactly that. The lane also proves two one-word image
mutants caught, and compares the census Rocq computes on the image with `tests/shen-jit/image-facts.txt`. The proof
mutant `ShenJitImageNoCodeEq` is rejected. Since r22-image-verdict, `OB-JIT-IMAGE-SEALING`'s exclusion is the Rocq
definition `JitImage.JitImageSealing.sealing_exclusion_statement` (in `Audit_Jit`, closed as a definition; a premise,
not proved of any program), and the census Rocq computes on the image also counts the sealing gap (65 unsealed
definitions, their names, 115 sealed sites in 45 definitions), so the 18-versus-24 numbers are lane-pinned Rocq census,
not only Python.

This document relates the image to stage 0's output. It says nothing about which definitions are validated:
counts of the form "N of 955 kernel definitions validated" come from the full-pipeline judge, not from here. The
image result is "955 of 955 stage 0 code objects equal their image function cells' code objects".

## The verdict: five sub-obligations

`OB-JIT-IMAGE` is partial and depends on the five below; it is discharged only when all five are. Each verdict
names its measurement; the commands and log hashes are under Evidence.

| Sub-obligation | Ledger | Precise statement | Verdict | Measured by (command, log sha256; runs [L], [M], [X] under Evidence (r22-image-verdict)) |
|---|---|---|---|---|
| `OB-JIT-IMAGE-CODE` | partial (lane evidence; depends on `-READER`) | For each of the 955 `(defun F Code)` of the 24 `.sbc` files, F's function cell holds a capture-free closure whose code object decodes to `build_code prim_tree 64 Code` | **Done in the lane** (`image_code_ok`, closed under the global context, instance-validation via `code_check_sound`). Stays partial only because it depends on `-READER`, which is open, and the ledger forbids discharging over an open dependency (`tests/ledger.shen`, `discharged-over-open-dependency`) | [L] lane step `image:`: lane log `80e439169544b626f15d69f048907beacab49cd30271d6aec50455ecf74508fd`, `s0/Img.log` `2de4a6f06d5e65efbb2cd32f1ed681ea7bb03c6a6afc90fc0a10e1b2a39bbe4e` (two "Closed under the global context", then `image_facts`) |
| `OB-JIT-IMAGE-INIT` | open | The 7 code objects not reachable from the 955, the 357 closures outside function cells, the 55 bound value cells and the data they reach denote the store initialisation reaches | **Code part (`INIT-CODE`, the 7) feasible, not done; data part (`INIT-DATA`) infeasible now** (below) | [L] Rocq census `image_facts` (`cn_codes_unreached` 7, `cn_clo_other` 357, `cn_clo_other_reached` 352, `cn_values_bound` 55), `s0/image-facts.txt` `04fd3ee3775b9c04ebcf5e67c26107f85d304af76e277edfd95f590137431db8` equal to the pin; [M] `census.out` `36f1fd87...6dcc` |
| `OB-JIT-IMAGE-SEALING` | open (premise stated, not yet a hypothesis of the top theorem) | The top theorem excludes redefinition of the 65 extension names, which the image leaves unsealed behind 115 sealed call sites: `JitImageSealing.sealing_exclusion_statement sealed c0`, no configuration the source run reaches from `c0` evaluates a `defun` of one of `JitImageSealing.ext_names` | **Feasible only as a premise; the premise is now stated** (Rocq definition, closed). The alternative, FunRel surviving redefinition, is false on the binary (test below) | [L] `Audit_Jit.log` `2d61479f7c55b04993647d04e84200deed500458606184067db4cefe0cc6800d` (710 closed, the last two the premise and its name list); Rocq census `sealed_by_file`, `cn_unsealed_defs` 65, `cn_ext_names_ok` true, `cn_ext_sites` 115, `cn_ext_callers` 45 in `s0/image-facts.txt` `04fd3ee3775b9c04ebcf5e67c26107f85d304af76e277edfd95f590137431db8`; [X] census mutant rejected, log `ffff4756...a03`; [M] `sealgap.out` `0e509ac1...77cb`, `redef.out` `46329b98...cb7` |
| `OB-JIT-IMAGE-READER` | open | The reader's bytes are the image's bytes, and `image_load`'s rebasing and raw-field rebuild give the heap JitImage decodes | **Feasible by review plus a Rocq model of `rebase_heap`; not done.** The reader (`--image`) now only copies bytes, each as a `byte` constructor; Rocq joins them into words (`JitImage.words_of_bytes`, closed) | [M] `split.out` `a2703018...6919` (image part `fd8485a5...` equals `build/shen-jit.img`); [L] the reader's output `s0/Img.v` `323383bbcceb100b8df23342dcb7a861d024173ac4bf3f2c885eabc3ad254fdd` parses (`image_code_ok` needs `image_of` to succeed) |
| `OB-JIT-IMAGE-FILE` | partial | The run opens the pinned binary as its image: `SHEN_JIT_IMAGE` unset, `argv[0]` resolves to a file whose last image is `fd8485a5...` | **Feasible only as a stated premise** (a process-model fact, not provable from the image); not yet stated in Rocq | [M] `split.out` `a2703018...6919`, `bin.sha` `e0acd513...` |

### INIT, precisely

Measured by Rocq on the image (lane, `image_facts`) and by `census.py`:
- 2371 code objects. 2364 are reachable from the 955 function cells, nested code included. 7 are not: `thread`, made by
  `shen-jit.initialise` through `eval-kl` of `(defun thread (x) (shen-jit.thread x))`, and 6 `lambda` code objects
  reached from `*property-vector*`.
- 1313 closures: 956 in function cells (the 955 and `thread`), 357 elsewhere, 3 of them in value cells. Of the 357,
  352 run a code object reachable from the 955, so their code is already covered by `image_code_ok`, and 5 run one of
  the 6 unreached lambdas. None of the 357 has captures.
- 1557 symbols, 55 with a bound value cell (the rest hold the unbound immediate 26). The list is in `census.out`
  (`*property-vector*`, `*macros*`, `shen.*special*`, the stream globals, the six port globals stage 1 sets, ...).

Sub-obligation `INIT-CODE` (the 7 code objects): **feasible**, by capturing the forms initialisation passes to
`eval-kl` and judging them with the full pipeline like any other source. It is not done: no capture of those forms
exists, and the pipeline accepts too few definitions for it to matter yet.
Sub-obligation `INIT-DATA` (the 55 values, the property vector, dictionaries, streams, and the 357 closures as
values): **infeasible now.** Either stage 1 must be proved an instance of the main theorem, which needs the
initialisation functions validated (the source judge accepts 148 of 955 at 0.6), or Rocq must decode that data and
relate it to the KLambda store the initialisation calls reach, which needs a source-level run of initialisation that
no model has. The decoder could print the data; nothing yet says what it should equal.

### The initial-store facts share's HT and HP need

HT and HP are the premises of share's `check_share_sound`. They, `ht_not_com`, `thaw_defun_refused`, `hd_tl_fixed` and
`hd_tl_defun_refused` are on branch `p2/r1-share-ht`, not yet on `p2/int`.

Measured by Rocq in the lane (`name_facts`: sealed bit, function cell, `Match`) and by the binary (`redef.shen`, test):

| Name | Sealed bit in the image | Function cell | Stage 0 code `Match` | `defun` in the binary |
|---|---|---|---|---|
| `thaw` | 1 | closure | yes (sys.sbc's thaw) | refused: "defun of a fixed name" |
| `hd` | 0 | unbound | no stage 0 definition | refused: "defun of a fixed name" |
| `tl` | 0 | unbound | no stage 0 definition | refused: "defun of a fixed name" |

- **HT (D defines thaw as the kernel does):** the image side holds and is now lane evidence. thaw's cell holds the
  code stage 0 made from the kernel's `(defun thaw (V) (V))`, and the binary refuses to redefine it, as the model's
  `thaw_defun_refused` does. The source side is still **infeasible on this back end**: that code is a 0-ary
  `tail-call-value`, Comp has no rule for it, and `ht_not_com` shows no store meeting HT has `Com`. That stays
  `OB-JIT-SHARE-THAW` until an emit family relates dynamic apply.
- **HP (D holds hd and tl as the primitives):** the store side holds in the image. Neither has a function, so calls
  go to the primitive, and the binary refuses `defun` of either. **HP's sealed side does not hold as stated.** D_wf
  puts hd and tl in `sealed`, but the image's sealed bit is 0 for both. The image protects them as fixed names, not
  as sealed ones. The pinned sealed list is the 890 names with the bit set, and it does not contain hd or tl. So the
  premise must be restated with fixed names (`hd_tl_fixed`, `hd_tl_defun_refused`), or the sealed parameter must be
  read as "sealed or fixed". That is a decision for share's owner, recorded under `OB-JIT-SHARE-THAW`.

## Inputs (bound)

| What | Value |
|---|---|
| Binary | `/lps/p6/sj/build/shen-jit`, sha256 `e0acd5132a9d876e7618bf1f400706abd82330d18458d209ee064d81d3c10c8d`, 5440856 bytes, ELF riscv64 (`file`), the pinned build of docs/SHEN-JIT.md |
| Runtime part | bytes 0 to 4657759, sha256 `13afde42c3f42de360c3aa7a8ad62ddafed5f281457fd8a34dbd994b3a3f71c4`, equal to `build/runtime` |
| Image part | the last 783096 bytes, sha256 `fd8485a556e7461352dc61860253c4013073c7adb0004b4e3cefc52c3f0bc18f`, equal to `build/shen-jit.img` |
| Stage 0 | `LC_ALL=C sha256sum *.forms *.sbc | sha256sum` = `ec9b387204471bfce36162019601b89493eb29abc4e42e8b8424d0ab903ab736` (the pin) |
| Rocq | 9.3.0, opam switch `lps`, in `buri-lps`. r22-image-verdict runs: the tree `aa1a7e5` on `p2/r22-image-verdict`, based on `p2/int` `fe461f4` (r1-image ran on `2e45d67`, r21-image-lane on `f42d6c4`). The lane's `Coq` to `Stdlib` rename is applied |

docs/SHEN-JIT.md says the image is "about 765 KB of its 1 MB on arm64". At 0.6 it is 783096 of the 5440856 bytes of
a riscv64 binary. The 4.6 MB runtime carries debug information.

## What the image is

`Makefile`: `build/runtime --stage1 build/stage0 build/shen-jit.img`, then `cat runtime shen-jit.img > shen-jit`.
The `stage1` function in `src/runtime/main.c` does four things, in order:

1. Loads the 24 `.sbc` files with `load_stage0_sealed`, in this order: `toplevel` to `lower` (18 files), then the 6
   extension files. Only definitions that start before the 19th file are sealed (`SEALED_FILES = 18`).
2. Runs `sj_init_host` and sets `*language*`, `*implementation*`, `*release*`, `*port*`, `*porters*` and `*os*`.
3. Runs `shen.initialise`, `shen.x.features.initialise` with `[shen/shen-jit]`,
   `shen.x.programmable-pattern-matching.initialise`, `shen.x.namespaces.initialise` and `shen-jit.initialise`.
4. Dumps the heap with `image_dump`.

The image format is `src/runtime/image.c`, version 2:
- a 13-word header;
- the heap after one collection, with each pointer stored as its byte offset from the heap base and raw native fields
  stored as 0;
- the cell array (2 words per symbol: value, then function);
- the constant array;
- a 2-word trailer, whose `SJHI-END` and length let the runtime find the image at the end of its own file.

Measured header (Rocq `s_hdr`, and the Python census agrees):

| Field | Value |
|---|---|
| magic, version | `SJHI`, 2 |
| build | `5c81999610faf8e6`, which occurs in the runtime part too (`grep -c -a` on its 4657760 bytes: 2) |
| word size | 8 |
| heap words | 87059 |
| cell entries | 3114 (1557 cells) |
| constant entries | 7699 |
| symbols | 1557 |
| primitive count | 121, equal to `JitBytecode.prim_table` without `raise-cond` |
| primitive checksum | 15828751884822036086 (read, not checked: it hashes the C table's names) |

The heap walk, which follows `rebase_heap`, ends exactly at word 87059. It finds these objects:

| Type | Count |
|---|---:|
| pairs | 5623 |
| strings | 2223 |
| byte objects (bytecode) | 2371 |
| symbols | 1557 |
| vectors | 62 |
| closures | 1313 |
| code objects | 2371 |
| streams | 3 |

## The decoder and the relation

[`rocq/JitImage.v`](../rocq/JitImage.v) (moved from `spikes/image-decode/` by r21-image-lane) defines the following, all in Rocq:

- **`parse_image`** checks the header and trailer and walks the heap. A word with tag 111 starts an object of
  `obj_words` words; any other word starts a pair. The walk must end at the heap size. A pointer is read only into an
  object start of the right type.
- **`fn_code`** finds a symbol's cell from its `SYM_CELL` word (low 56 bits) and reads the procedure in that cell's
  function slot. That must be a closure with no captures. `fn_code` then decodes the closure's code object into
  `JitBytecode.code`:
  - the bytecode is unpacked as `bytecode_unpack` does, then decoded with `loader.c`'s operand layout;
  - constants and nested code objects come from the constant array at the code's base;
  - a call's cell operand is read back to the symbol that owns the cell;
  - a sealed call's operand is a constant slot, read back to the symbol whose function cell holds the procedure in that
    slot. A cell or procedure claimed by two symbols decodes to nothing;
  - the entry count above bit 32 of `CODE_ARITY` must agree with the first instruction.
- **`check_def`** compares one definition `(defun F Code)` from the `.sbc` files with the decoded code of F's function
  cell. It gives `Match` when `JitBytecode.build_code prim_tree 64 Code`, the loader model the lane already uses,
  equals that decoded code under a boolean equality proved sound (`code_eqb_true`).
- **`check_def_sound`** states what `Match` means: the form is `(defun F Code)`, `build_code` accepts `Code` as `k`, and
  `fn_code` of F is `k`. Rocq 9.3 prints "Closed under the global context" for it.

The one trusted step is the lane's reader, `tests/shen-jit/stage0_to_rocq.py --image` (`OB-JIT-IMAGE-READER`). It
finds the image from the trailer and writes each of its bytes, in file order, as a constructor of Rocq's ordinary
inductive `byte`; `JitImage.words_of_bytes` joins them into little-endian words in Rocq. The 24 files' trees are not
read again: `Img.v` imports the stage 0 step's own `Buri.s0.S0_<file>` modules. (The r1-image spike used
`spikes/image-decode/image_to_rocq.py`, which split words in Python; that is history, below.)

### Result

```
run.sh /lps/p6/sj OUT   (in buri-lps, under /lps/bin/rocq-slot)
s_total = Some (955, 0)          (* Match, other verdicts *)
```

Each of the 24 files has every definition `Match` and an empty list of other verdicts (`s_tally`). That means every
constant, nested code object, sealed call target and inline field is equal, as well as every instruction. Sealed call
targets are the closures the function cells hold after initialisation. So initialisation redefined none of the 955
functions, and every sealed slot is bound to the current definition.

The relation is not vacuous. `ImgMut.v` changes one image word at a time, and each change turns `print`'s verdict
into `Differ` (writer: 26 Match plus `differ print`):
- the arity word of `print`'s code object, 1 changed to 2;
- `print`'s first bytecode byte, `const` changed to `move`.

Costs: compiling `ImgData.v` (97887 words plus the 955 `.sbc` trees, 4.5 MB of source) took 1084 s and about 1.3 GB.
`ImgSum.v`, the whole relation plus the census, took 100 s. `ImgMut.v` took 46 s.

## Code objects not reached from the 955

2371 code objects: 2364 are reachable from the 955 function cells, nested code included, and 7 are not.

| Code | Held by | Made by |
|---|---|---|
| `thread` (arity 1, 8 bytes of bytecode) | the function cell of `thread` | `shen-jit.initialise`, which calls `eval-kl` on `(defun thread (x) (shen-jit.thread x))` (`src/port/shen-jit.kl`, about line 415), "defined here, once sealing has ended" |
| 5 `lambda` | reached from the value of `*property-vector*`, through pair chains (first referrer followed; the key holding each one was not decoded) | consistent with the lambda-form entries initialisation records with `shen.set-lambda-form-entry`; not checked further |
| 1 `lambda` | constant slot 7698, nested in one of those 5 (the one whose arity word carries an entry) | the same |

Of the 1313 closures, 956 sit in function cells: the 955 and `thread`. The other 357 are held elsewhere, in values
and data built by initialisation, and are part of `OB-JIT-IMAGE-INIT` too.

These 7 were lowered at stage 1 by the image's own sealed lowerer, through `eval-kl`, and not by stage 0. That lowerer is
measured to reproduce stage 0 on 944 of 955 definitions (CENSUS.md, the image run). No stage 0 validation covers these 7.
They belong to `OB-JIT-IMAGE-INIT`. Two routes would close them:
- capture the forms initialisation passes to `eval-kl`, and judge them with the full pipeline like any other source; or
- prove stage 1 an instance of the main theorem.

## Sealing: 18 files in the image, 24 at stage 0

Stage 0 (`src/lowerer/stage0.shen`) seals all 955 defun names before it lowers, so calls into the 6 extension
files are lowered as `call-sealed`. Stage 1 seals only the first 18 files.

Measured in the image, from `SYM_CELL` bit 58 (`objects.c`: `SEALED_BIT = 58`):
- 890 of the 955 names are sealed, exactly the definitions of the first 18 files;
- the 65 definitions of the 6 extension files are not sealed;
- no other symbol is sealed.

Measured twice, both census, not proof:
- by Rocq on the image, in the lane since r22-image-verdict (`image_facts`, pinned in `tests/shen-jit/image-facts.txt`):
  `cn_unsealed_defs` 65 definitions lack the sealed bit; `cn_ext_names_ok` true, so their names, in load order, are
  exactly `JitImage.ext_names_s`, the list the premise below names; `cn_ext_sites` 115 `ICallSealed`/`ITailSealed`
  operands in the decoded code of the 955 function cells (nested code included) name one of them; `cn_ext_callers` 45
  definitions hold at least one. Since `image_code_ok` equates each decoded code with stage 0's, these are stage 0's
  sites too;
- by `sealgap.py` on stage 0 (per caller file, below): 115 `call-sealed`/`tail-call-sealed` sites in 45 definitions
  target those 65 names.

| Caller file | Sites |
|---|---:|
| shen-jit (`shen.x.launcher.main`) | 2 |
| extension-features | 2 |
| extension-launcher | 13 |
| extension-programmable-pattern-matching | 24 |
| extension-namespaces | 22 |
| extension-expand-dynamic | 32 |
| extension-type-annotations | 20 |

No `inline` instruction targets an extension name.

**The gap file by file.** The 18 files `toplevel` to `lower` have every definition sealed both at stage 0 and in the
image (890 names). That is a Rocq census, `sealed_by_file` in `image_facts`, diffed against `tests/shen-jit/image-facts.txt`; it is not a proof. The 6 files below were sealed at stage 0 and are
not sealed in the image. Columns: definitions, sealed in the image (Rocq, lane), stage 0 sealed sites that target the
file's definitions, and their caller files (`census.py`, `gap` lines).

| Stage 0 file | Definitions | Sealed at stage 0 | Sealed in the image | Sealed sites targeting it | From caller files (callers) | Image-run lowerer differences (CENSUS.md) |
|---|---:|---:|---:|---:|---|---:|
| extension-features | 4 | 4 | 0 | 2 | extension-features 2 (1) | 2 |
| extension-launcher | 11 | 11 | 0 | 15 | extension-launcher 13, shen-jit 2 (`shen.x.launcher.main`) (5) | 3 |
| extension-programmable-pattern-matching | 16 | 16 | 0 | 24 | itself 24 (11) | 3 |
| extension-namespaces | 11 | 11 | 0 | 22 | itself 22 (9) | 3 |
| extension-expand-dynamic | 16 | 16 | 0 | 32 | itself 32 (13) | 0 |
| extension-type-annotations | 7 | 7 | 0 | 20 | itself 20 (6) | 0 |
| **total** | **65** | **65** | **0** | **115** | 45 callers | 11 |

So 6 files with 65 definitions make up the 24 minus 18. Each is fully unsealed in the image. All but 2 of the 115 sites
are calls inside the same extension file. The other 2 are `shen.x.launcher.main` (file `shen-jit`, sealed) calling
into extension-launcher.

**Redefinition, tested in the pinned binary** (`spikes/image-decode/redef.shen`, run under qemu: test evidence, not
proof). `shen.x.launcher.eval-command-h` reaches `shen.x.launcher.execute-all`, one of the 65, through a
`tail-call-sealed` site.

| Step | Result |
|---|---|
| `sealed?` of execute-all; of `shen.x.launcher.main` (sealed file) | false; true |
| `(shen.x.launcher.eval-command-h [] [])` before | `[success]` |
| `eval-kl` of `(defun shen.x.launcher.execute-all (X) redefined)` | accepted |
| open call `(shen.x.launcher.execute-all [])` after | `redefined` |
| the sealed caller `(shen.x.launcher.eval-command-h [] [])` after | `[success]`: the closure bound at load |
| `defun` of `shen.x.launcher.main` | refused: "is sealed and cannot be redefined" |
| `defun` of `thaw`, `hd`, `tl` | refused: "defun of a fixed name" |

This confirms the source reading. After a redefinition, the binary's sealed sites call the old definition and its
open calls call the new one. In KLambda's late binding, `eval-command-h` would return `redefined`. So the route
"FunRel survives redefinition" is **false for the binary**, by this test. Only the premise route is feasible. The
model meets it if the theorem's `sealed` set holds the 65 names, so that `jit_rules` refuses their `defun`. The binary
does not refuse, so the premise must be stated as an exclusion on programs, never derived from the image.

**What the gap does and does not change.**
- **The loaded code does not change.** The `.sbc` already carries `call-sealed`, and the relation above matches all
  955, including the 65.
- **Redefinition is what changes.** In the image the 65 names are open, so a program may redefine them, through
  `eval-kl` of a `defun` or the install primitive. Read from the source, and not tested, the 115 sealed sites then
  still call the closure bound at load, while open calls and `shen-jit.sealed?` see the new definition. Shen's late
  binding would call the new one. The source reading:
  - `sj_install` (`loader.c`, about lines 448 to 480) refuses only names whose sealed bit is set. Its
    `bind_sealed(&l, true)` binds only the sealed slots of the code being installed (`l.sealed_slot` is local to that
    load).
  - The `redefine` hook (`jit.c`, about line 304) only undoes the native patches of open calls to that cell
    (`patches_drop`).
  - Nothing rewrites an existing sealed constant slot.
- **The image's own lowerer differs from stage 0's.** It treats these callees as open, with `shen-jit.inlined?`
  guards. That is where the 11 image-run differences of CENSUS.md come from: features 2, launcher 3, namespaces 3,
  programmable-pattern-matching 3.

`OB-JIT-IMAGE-SEALING`, precisely (r22-image-verdict). The exclusion is a Rocq definition at the end of
[`rocq/JitImage.v`](../rocq/JitImage.v):

```coq
Module JitImageSealing.
Definition ext_names : list name := map of_string JitImage.ext_names_s.   (* the 65 *)
Definition sealing_exclusion_statement (sealed : list name) (c0 : config) : Prop :=
 forall rho f ps b k s,
  JitLowerStep.JitLowerStep.Sstar sealed c0 (Cfg (Eval rho (EDefun f ps b)) k s) -> ~ In f ext_names.
End JitImageSealing.
```

It says no configuration the source run (`jit_rules sealed`, the `Sstar` of the top theorems) reaches from `c0` is about
to evaluate a `defun` of one of the 65 names. It is stated over the run, not the program text, so a `defun` built at
run time and passed to `eval-kl` (which the source semantics turns into `Eval [] e`) is excluded too. Both definitions
are in `Audit_Jit` and print "Closed under the global context" (they are definitions, so that says only that they
mention no axiom). Nothing proves the premise of any program, and the image cannot supply it: the binary accepts the
redefinition. `call_preservation_src_statement` is unchanged and does not yet take this premise; adding it as a
hypothesis of the top theorem is what remains for `OB-JIT-IMAGE-SEALING` (ledger: open). Redefinition through
`shen-jit.install` is not covered by this statement: `jit_rules` gives port primitives no meaning (`OB-JIT-PORT-PRIMS`,
decision-gated), so a run calling it is outside the model already.

The name list is transcribed (from the 6 extension `.forms`, by a Python one-liner: orchestration). Rocq checks the
transcription on every lane run: `cn_ext_names_ok` is true only when the list equals, in order, the names of the 955
definitions that lack the image's sealed bit, and the lane fails with `IMAGE_FACTS_CHANGED` otherwise. Run [X] below drops
one name and the census gives `cn_ext_names_ok := false`, so the lane's diff rejects it.

Verdict: **feasible as a premise, now stated; not dischargeable from the image**, because the binary accepts the
redefinition and its 115 sealed sites then disagree with late binding (test above).

### 18 versus 24, reconciled

| Count | Value | Kind and source |
|---|---:|---|
| files stage 0 lowers, all names sealed (`stage0.shen` seals every defun name before lowering) | 24 files, 955 names | `image_files` (Rocq, lane: the 24 files are stage 1's, in order); stage 0 census |
| files stage 1 seals (`main.c`, `SEALED_FILES = 18`) | 18 files, 890 names | Rocq census `sealed_by_file` and `cn_sealed` 890 (lane) |
| the gap | 6 files, 65 names, all unsealed in the image | Rocq census `sealed_by_file` (6 rows `n, 0`) and `cn_unsealed_defs` 65 (lane) |
| sealed sites into the gap | 115 sites in 45 definitions (2 of them in `shen.x.launcher.main`, file `shen-jit`) | Rocq census `cn_ext_sites`, `cn_ext_callers` (lane); `sealgap.py` (per file) |
| code of the 65 | equal to stage 0's | `image_code_ok` (Rocq proof, lane) covers all 955, the 65 included |
| what the gap changes | redefinition of the 65 only | binary test `redef.shen`; excluded by `sealing_exclusion_statement` (premise) |

## Reading the image (`OB-JIT-IMAGE-FILE`, `OB-JIT-IMAGE-READER`)

`run` in `main.c` sets `image = getenv("SHEN_JIT_IMAGE") ? getenv("SHEN_JIT_IMAGE") : executable_file(argv[0], ...)`.
`executable_file` searches `PATH` when `argv[0]` has no `/` and otherwise uses `argv[0]` as given. It doesn't use
`/proc/self/exe`.

`image_load` then reads the last image in that file and checks four things against the runtime:
- the build identifier;
- the word size;
- the primitive count;
- the primitive checksum.

It rebases every pointer and rebuilds the raw fields:
- closure entries become the compile stub;
- code `native` fields become 0;
- the 3 standard streams are reattached and file streams are closed;
- `vm_track_code` and `vm_find_free_consts` run.

So the premise `OB-JIT-IMAGE-FILE` still needs has three parts:
- `SHEN_JIT_IMAGE` is unset;
- the file that `argv[0]` resolves to holds the pinned binary, whose last image is `fd8485a5...`;
- the process model's file system says so.

The split of the binary is measured (Inputs, above). `OB-JIT-IMAGE-READER` covers two things: the reader script, which
only splits bytes into words, and `image_load`'s rebasing and raw-field reconstruction. Neither is modelled. The
decoder reads the stored, unrebased image, and the claim that loading it yields the heap the decoder describes is that
obligation.

## The lane step (`OB-JIT-IMAGE-CODE`, r21-image-lane)

The steps the r1-image scoping listed are done. `scripts/check-shen-jit.sh` now does the following after the stage 0 step:
1. `JitImage` is in the lane's FILES and in `rocq/modules.d/70-jit.list`. `Audit_Jit` adds `code_eqb_true`,
   `check_def_sound`, `tally_sound` and `code_check_sound`, so 527 audited statements.
2. `stage0_to_rocq.py --image BIN Img.v` is the reader. It finds the image from the trailer and writes each byte as a
   constructor `xHH` of `Corelib.Init.Byte.byte`, in chunks of 8000. It reads no `.sbc`: `Img.v` imports the stage 0 step's own `Buri.s0.S0_<file>`
   modules, so the trees the image is compared with are the trees the stage 0 judge read.
3. `Img.v` defines `words := JitImage.words_of_bytes bytes`, and Rocq proves, each by `vm_compute`:
   - `image_files`: the 24 files are stage 1's, in order;
   - `image_code_ok : code_check words fs = true`;
   - `image_mutants_caught`: print's code object with its arity word raised by one, and with bit 1 of its first
     bytecode byte flipped, each no longer `Match`. The word positions are found in Rocq, not given.

   **Assumptions.** `Print Assumptions` on both lemmas prints "Closed under the global context", and the lane fails
   on anything else (`IMAGE_ASSUMPTIONS`). Until `0595b57` the reader wrote 32-bit halves as `Uint63` literals and
   both lemmas assumed Rocq's primitive `int`, `lsr`, `land` and `eqb`. Closed encodings tried before that:
   - Rocq computed the words as an N list and stored it as a constant: stopped after 616 s (VM-compiling a constant
     of about 6 million constructors);
   - the words as N literals in the file: stopped after 140 s;
   - each chunk of 1000 words joined by `Eval vm_compute` into its own N constant: timed out at 900 s.

   The bytes encoding works because a `byte` is one constant constructor (an immediate in the VM), so the 783096
   bytes are about 0.8 million list cells, against about 6 million `positive` constructors for the words as N.
   `byte_n` reads a byte's value from `Byte.to_bits`, an ordinary function. Measured: `Img.v` with the bytes
   compiled in 181 s (stage 0 modules already built), and its `image_facts` equals the pin.
4. `image_facts`, the census Rocq computes on the image, is diffed with `tests/shen-jit/image-facts.txt`. It covers the
   word and definition counts, the code, closure and cell census, the sealing by file, and the thaw, hd and tl facts.
   A change fails the lane (`IMAGE_FACTS_CHANGED`).

Cost: N literals were the 18-minute part. A file of the 97887 words as N literals had not compiled after 140 s and was
stopped. The same words as Uint63 halves compiled in 5 s, but were not closed. The bytes encoding, which is closed,
makes the whole image step (reader, compile of `Img.v`, `image_code_ok`, the mutants and the census) about 3 minutes.

`mut_caught` counts a mutant as caught only when the mutated image still parses and `check_def` on the mutated name
is not `Match`. A mutant that breaks parsing is not counted (before `0595b57` it was).

The proof mutant `ShenJitImageNoCodeEq` (`tests/mutate-shen-jit.py`) makes `check_def` give `Match` without
comparing code, and `check_def_sound` then fails.

Under Coq 8.18 (`make prove`), `JitImage.v` is UNKNOWN: no 8.18 toolchain was available here.

## Evidence (r22-image-verdict)

All runs were in `buri-lps` on 11 November 2026, under Rocq 9.3 (opam switch `lps`), on commit `aa1a7e5` of
`p2/r22-image-verdict` (based on `p2/int` `fe461f4`), copied with `git archive` to `/work/p2-r22-image-verdict`. The
commit after it changes only docs and the ledger. Kinds are kept apart: Rocq proofs (lane), Rocq census
(`image_facts`), Python census, and a binary test. The binary is `e0acd513...` and stage 0 is `ec9b3872...`, both as
pinned (`bin.sha`, `stage0.sha` of [M]).

| Run | Command | Exit | Log sha256 |
|---|---|---|---|
| [L] Lane with image step | `cd /work/p2-r22-image-verdict && SKIP_DIFF=1 JIT_OUT=/tmp/p2-r22-image-verdict-out /lps/bin/rocq-slot bash scripts/check-shen-jit.sh`, 21:19:36Z to 22:06:39Z | LANE_RC=0 | `/tmp/p2-r22-image-verdict-lane.log` `80e439169544b626f15d69f048907beacab49cd30271d6aec50455ecf74508fd` |
| [L] its image step's Rocq log (`image_code_ok`, `image_mutants_caught`: each "Closed under the global context"; then `image_facts`) | inside [L] | 0 | `s0/Img.log` `2de4a6f06d5e65efbb2cd32f1ed681ea7bb03c6a6afc90fc0a10e1b2a39bbe4e`; `s0/Img.v` `323383bbcceb100b8df23342dcb7a861d024173ac4bf3f2c885eabc3ad254fdd` (the reader's output, byte-identical to r21-image-lane's); `s0/image-facts.txt` `04fd3ee3775b9c04ebcf5e67c26107f85d304af76e277edfd95f590137431db8`, byte-equal to `tests/shen-jit/image-facts.txt` |
| [L] its audit | inside [L] | 0 | `Audit_Jit.log` `2d61479f7c55b04993647d04e84200deed500458606184067db4cefe0cc6800d`: 710 lines "Closed under the global context" and nothing else; the last two are `JitImageSealing.ext_names` and `JitImageSealing.sealing_exclusion_statement` |
| [P] Pre-measurement of the new census (to write the pin) | `rocq compile` of this branch's `JitImage.v` and of `s0/Img.v` in `/tmp/p2-r22-image-verdict-pre`, a copy of the r22-int-land lane build of `fe461f4`, under rocq-slot | 0, 0 | `Img.log` `2de4a6f06d5e65efbb2cd32f1ed681ea7bb03c6a6afc90fc0a10e1b2a39bbe4e`, the same bytes as [L]'s |
| [X] Census mutant: `ext_names_s` without its last name | `bash /tmp/p2-r22-image-verdict-mut.sh` (recompiles the mutated `JitImage.v` and `Img.v` in the [P] copy, extracts `image_facts` as the lane does, diffs with the pin) | diff 1: `cn_ext_names_ok := false`, "IMAGE_FACTS_CHANGED (mutant rejected by the lane's diff)" | `/tmp/p2-r22-image-verdict-mut.log` `ffff475658b3898a44358af684e822c3323faeeca8172d72e2eb5d2bdbd8ea03` |
| [M] Measurements (Python census, binary split, redefinition test) | `/lps/bin/rocq-slot bash spikes/image-decode/meas.sh /work/p2-r22-image-verdict /tmp/p2-r22-image-verdict-meas` | 0 (each step 0) | `/tmp/p2-r22-image-verdict-meas.log` `01ac4f10e259857d7568c4e0eac73667eab8716db95114bb51b8f4428af2a2d6` |

[M]'s outputs are byte-identical to r21-image-lane's: `split.out` `a2703018...6919`, `census.out` `36f1fd87...6dcc`,
`sealgap.out` `0e509ac1...77cb`, `fncells.out` `ae8e9264...3364`, `redef.shen` `acc9512f...686d`, `redef.out`
`46329b98...cb7`, `redef.err` empty. The facts were therefore re-measured at the pin, and nothing moved: the
census Rocq computes and `sealgap.py` agree on 65 names, 115 sites and 45 callers.

**Ledger:** `./scripts/check-shen tests/ledger.shen` on the host passed: BURI_SUITE_OK ledger 62.

**Not run, UNKNOWN for this branch:** `make prove` (Coq 8.18; no 8.18 toolchain in `buri-lps`), the differential
(SKIP_DIFF), `gate_tests.sh`, the full mutation suite and `make report`. No proof mutant was added: the two new Rocq
items are definitions, and the census link's mutant is [X].

## Evidence (r21-image-lane)

All runs were in `buri-lps` on 11 November 2026, under Rocq 9.3 (opam switch `lps`). The proof runs are at commit
`0595b57` on `p2/r21-image-lane` (based on `p2/int` `f42d6c4`), copied with `git archive` to
`/work/p2-r21-image-lane`; the later commits change only docs and the ledger. The measurement run is at `2149914`;
`git diff --stat 2149914 0595b57` touches only `rocq/JitImage.v`, `scripts/check-shen-jit.sh`,
`tests/shen-jit/stage0_to_rocq.py` and docs/ledger, none of which `meas.sh` reads (it runs `census.py`,
`sealgap.py`, `fncells.py` and `redef.shen` on the binary and stage 0 outputs). Kinds are kept apart: Rocq proofs (lane), Rocq census (`image_facts`), Python
census, and a binary test.

| Run | Command | Exit | Log sha256 |
|---|---|---|---|
| Lane, with image step (proof and Rocq census), at `0595b57` | `cd /work/p2-r21-image-lane && SKIP_DIFF=1 JIT_OUT=/tmp/p2-r21-image-lane-out /lps/bin/rocq-slot bash scripts/check-shen-jit.sh` | 0, 1545 s | `/tmp/p2-r21-image-lane-lane2.log` `a120de67401662489f1d23474d48833a5e9842e882464372a212e33d5a57078b` |
| the image step's Rocq log (`image_code_ok`, `image_mutants_caught`, each "Closed under the global context"; `image_facts`) | inside the lane run | 0 | `s0/Img.log` `b330dd6e547cd6d2339da07de5423a990be68b877644c3c5d6edd3dedc387571`; `s0/Img.v` `323383bbcceb100b8df23342dcb7a861d024173ac4bf3f2c885eabc3ad254fdd`; `s0/image-facts.txt` `d1017803d8c748e4e764a6aa8c54489dd6e59a65cf53df9d7083f3b0cf600376` (equal to the pin) |
| Proof mutant `ShenJitImageNoCodeEq` (from `tests/mutate-shen-jit.py` at `0595b57`, Stdlib rename), against that lane build | `cd /tmp/p2-r21-image-mut2 && python3 tests/mutate-shen-jit.py && rocq compile -Q /tmp/p2-r21-image-lane-out Buri ShenJitImageNoCodeEq.v` under rocq-slot | 1, rejected: "(in proof check_def_sound): Attempt to save an incomplete proof" | `/tmp/p2-r21-image-mut2/ShenJitImageNoCodeEq.log` `45eb3afdfe79ed6fb33983661205e14e31560a43587c7ce5ba2115e793772847` (same text as the run at `1533b51`) |
| Superseded: lane at `1533b51` (Uint63 halves; instance assumed `int`, `lsr`, `land`, `eqb`) | same command | 0, 1355 s | `/tmp/p2-r21-image-lane-lane.log` `ea4cd53c500132976d847df2ae92565c922df68d3b2852bff0f4be57fa848327`; `s0/Img.log` `cb369c66...3574` |
| Measurements (Python census, binary split, redefinition test) | `bash spikes/image-decode/meas.sh /work/p2-r21-image-lane /tmp/p2-r21-image-meas2`, at commit `2149914` (the script committed): runs `census.py`, `sealgap.py` and `fncells.py`, the split hashes, and `qemu-riscv64 /lps/p6/sj/build/shen-jit script redef.shen` | 0 (each step 0) | `/tmp/p2-r21-image-meas2.log` `671c9ff9873b046d88d87cde89ed68506bd4870ed11fb9362bdf7e708053c2bc`. An earlier run of the same script from the scratchpad gave identical output hashes |

The lane printed:
- "rocq-9: 527 audited statements closed, rocqchk passed";
- "stage0: 148 accepted, 807 rejected, 0 unreadable of 955 definitions, as recorded";
- "image: image_code_ok proved, closed under the global context (...), 2 image mutants caught, census as recorded";
- "differential: NOT RUN".

`Audit_Jit.log` has sha256 `f19d12ce631457a12dbe4993ef7d4bea089ddfb49748035eec9fec161b60d5f7` (527 "Closed under the
global context", unchanged from `1533b51`). Not run: the differential (SKIP_DIFF), `gate_tests.sh`, the full proof
mutation suite, `make report` and the Coq 8.18 `make prove`: UNKNOWN. The 148 is the source
judge's stage 0 count, not a validated count.

Measurement outputs (sha256):
- `split.out` `a2703018141da0842914299260b03247d7cec877e0f23f0799e7c5a855746919`: 5440856 bytes, runtime `13afde42...`,
  image `fd8485a5...`, `SJHI-END`;
- `census.out` `36f1fd87391f5c2bb6e30f0e4b9bf8e88821401c01c185bc76838e9b7bdb6dcc`;
- `sealgap.out` `0e509ac14f9b6c14c78bfde49bce30b741b814a5fb574cad38dc3291d7b877cb`, the same as at r1-image;
- `fncells.out` `ae8e926404034dab5752104aab9e6d18ae604c35d95716d5a2b314942f953364`;
- `redef.shen` `acc9512f2fd0d2150129a6041bb2be17146d43f9e67e1c2dec4f29e86217686d`, `redef.out`
  `46329b981e8d9250ff6b739bcedebcc09552ad26e8f9e8586ee85cb54e6e8cb7`, `redef.err` empty.

The binary is `e0acd513...` and stage 0 is `ec9b3872...`, both as pinned.

**Ledger:** `./scripts/check-shen tests/ledger.shen` on the host passed: BURI_SUITE_OK ledger 62.

**Not run, UNKNOWN for this branch:**
- `make prove` (Coq 8.18, which would compile `JitImage.v`; no 8.18 toolchain here);
- the differential;
- `gate_tests.sh`;
- the full mutation suite (`scripts/proof-mutations`);
- `make report`.

## Evidence of the r1-image spike (history, superseded for the code objects by the lane step)

Everything was run in `buri-lps` on 10 November 2026, from worktree `p2/r1-image`, at commit `e08d73e`, which is based
on `p2/int` `2e45d67`. These are measurements: the Rocq verdicts are computed by Rocq, and the census lines are Python
bookkeeping. Nothing here runs in the lane.

**Run of the committed spike.** Command: `cd /work/p2-r1-image && /lps/bin/rocq-slot bash spikes/image-decode/run.sh
/lps/p6/sj /tmp/p2-r1-image-final`. Exit 0 after 1836 s. It printed `IMAGE_DECODE_OK`, which run.sh prints only
after three checks pass:
- Ax.log says closed;
- `s_total = Some (955, 0)`;
- both mutants give `differ print`.

The log is `/tmp/p2-r1-image-run.log`, sha256 `9f24f9eaee718574ed425d1535ee504185a72fc73718ff9bdf29b1d9651cca2d`.
The run's outputs are byte-identical to the first, exploratory run's.

| Item | sha256 |
|---|---|
| `spikes/image-decode/JitImage.v` (committed) | `e0c2f3ebafc16461a7cbfe5461e55bac0e1240fdfb4e3197d4cc4f02289ef020` |
| the same, as compiled (Stdlib rename) | `a6064daebceac296e28ca7fc6867108d295c6709d9768dbde0e3c1562a9d7014` |
| `image_to_rocq.py` | `1f8caa1c13128fd108470553ff3b6b1f627d18fd543cc10378aedc8c09ae36ab` |
| `ImgRun.v`, `ImgSum.v`, `ImgMut.v` | `b45b1ded...9036`, `c7db10b3...bc09`, `d7f0a0a2...7014` |
| `census.py`, `sealgap.py`, `run.sh` | `d8719f5a...930e`, `eb767564...b2f2`, `1b649ec3...a439` |
| `ImgData.v` (generated) | `6ead9530a6e529a0e298df4d0c76b7ae830c363d8feb8719b1d5db0fd1a4a113` |
| `ImgSum.log` (the 955 tally, header, types, sealing, code objects) | `8e332a8a18451238a159aa789fed610751875d129b48dfb1b9b0370b520a37e2` |
| `ImgMut.log` (two mutants, each `differ print`) | `ef02bcf991317d77f2d69ad602668cc03c36bc0ada80b1019365fa08e5317d84` |
| `Ax.log` (`Print Assumptions check_def_sound`: closed) | `188ff29b8a0705f491438ebf47623e533fe60658944f3f1f58e1f9b5badb1bcf` |
| `census.out` (Python walk: same types, 2371/2364/7, 890 sealed) | `87713698409cbdcf7d63491a94567da77012627c93b8964eb63a5b75b23ee141` |
| `sealgap.out` (115 sites, 45 callers) | `0e509ac14f9b6c14c78bfde49bce30b741b814a5fb574cad38dc3291d7b877cb` |

`fncells.py` was run separately, by hand. It found 956 function cells that hold a procedure, all distinct.

**Lane.** Command: `SKIP_DIFF=1 JIT_OUT=/tmp/p2-r1-image-lane /lps/bin/rocq-slot bash scripts/check-shen-jit.sh`.
It ran on the same tree, whose lane-checked files are unchanged from `p2/int`. Exit 0 after 1063 s:
- "rocq-9: 199 audited statements closed, rocqchk passed";
- "stage0: 111 accepted, 844 rejected, 0 unreadable of 955 definitions, as recorded";
- differential NOT RUN.

The log sha256 is `2e01b8e52d591237ceefc44d37401376f979f032bb40d6e656afdca1ef1d1003`.

**Not run:** `make prove` (Coq 8.18), the differential, `gate_tests.sh` and the mutation suite. They are UNKNOWN for
this branch. The ledger check `./scripts/check-shen tests/ledger.shen` passed on the host (BURI_SUITE_OK ledger 62).
