# Shen/JIT heap image (OB-JIT-IMAGE)

Status: **scoped, partly measured. Not discharged, and nothing here is lane-checked.** The code objects of the
955 stage 0 definitions were decoded from the pinned binary's image by a Rocq decoder and compared with Rocq's loader
model of stage 0. All 955 match. That comparison is a Rocq `vm_compute` **measurement** run from
[`spikes/image-decode/`](../spikes/image-decode/). It is not in `scripts/check-shen-jit.sh`, `make prove` or `Audit_Jit`.
The rest of the image is split into sub-obligations, each with what was measured about it.

This document relates the image to stage 0's output. It says nothing about which definitions are validated:
counts of the form "N of 955 kernel definitions validated" come from the full-pipeline judge, not from here.

## The verdict

| Part | Verdict | Ledger |
|---|---|---|
| Code objects of the 955 stage 0 definitions | **Feasible, and done as a measurement:** 955 of 955 equal `JitBytecode.build_code` of their `.sbc` code. To count as evidence it must move into the lane (below) | `OB-JIT-IMAGE-CODE`, partial |
| 7 code objects made during initialisation | Not related. They were lowered at stage 1 by the image's own lowerer, not by stage 0 | `OB-JIT-IMAGE-INIT`, open |
| Global values, the property vector, dictionaries, streams | Not related. Initialisation built them by running kernel code | `OB-JIT-IMAGE-INIT`, open |
| Sealing: 18 files sealed in the image, 24 at stage 0 | Measured. The code is the same either way. The difference is that 65 names can be redefined in the image | `OB-JIT-IMAGE-SEALING`, open |
| Reading and loading the image | Trusted reader plus `image_load`, not modelled | `OB-JIT-IMAGE-READER`, open |
| Which file the run reads | Measured. No premise has been stated yet | `OB-JIT-IMAGE-FILE`, partial |

`OB-JIT-IMAGE` is now partial and depends on these five. It is discharged only when all five are. Of its two
completion routes, "image bytes decoded in Rocq and related to that store" is reached for the code objects only. Global
state needs either the stage 1 route, which is proving stage 1 an instance of the main theorem, or a Rocq decoder of the
data that initialisation built. The stage 1 route needs validated initialisation code. At 0.6 the source judge accepts
148 of 955 definitions (`tests/shen-jit/stage0-accepted.txt`; 111 at the re-pin, `spikes/pass-split/CENSUS.md`, before `=`
against a symbol constant was admitted), so that route is far off.

## Inputs (bound)

| What | Value |
|---|---|
| Binary | `/lps/p6/sj/build/shen-jit`, sha256 `e0acd5132a9d876e7618bf1f400706abd82330d18458d209ee064d81d3c10c8d`, 5440856 bytes, ELF riscv64 (`file`), the pinned build of docs/SHEN-JIT.md |
| Runtime part | bytes 0 to 4657759, sha256 `13afde42c3f42de360c3aa7a8ad62ddafed5f281457fd8a34dbd994b3a3f71c4`, equal to `build/runtime` |
| Image part | the last 783096 bytes, sha256 `fd8485a556e7461352dc61860253c4013073c7adb0004b4e3cefc52c3f0bc18f`, equal to `build/shen-jit.img` |
| Stage 0 | `LC_ALL=C sha256sum *.forms *.sbc | sha256sum` = `ec9b387204471bfce36162019601b89493eb29abc4e42e8b8424d0ab903ab736` (the pin) |
| Rocq | 9.3.0, opam switch `lps`, in `buri-lps`. The rocq/ dependencies are at this branch's base, `p2/int` `2e45d67`. The lane's `Coq` to `Stdlib` rename is applied |

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

[`spikes/image-decode/JitImage.v`](../spikes/image-decode/JitImage.v) defines the following, all in Rocq:

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

The one trusted step is [`image_to_rocq.py`](../spikes/image-decode/image_to_rocq.py). It finds the image from the
trailer, splits it into little-endian words, and writes the 24 `.sbc` files as the lane's `sx` trees with
`stage0_to_rocq.py`'s own reader.

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

Measured in stage 0, with `sealgap.py`, a census: 115 `call-sealed`/`tail-call-sealed` sites in 45 definitions target
those 65 names.

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

`OB-JIT-IMAGE-SEALING` asks for one of two things:
- the top theorem excludes redefining the 65 names, as a stated premise or exclusion; or
- Rocq shows FunRel survives the redefinition.

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

## Path to discharge `OB-JIT-IMAGE-CODE`

This is feasible with the existing pieces. The work is wiring, not proof:

1. Move `JitImage.v` into `rocq/`, list it in `rocq/modules.d/70-jit.list`, and add `check_def_sound` and
   `code_eqb_true` to `Audit_Jit`.
2. Add a lane step to `scripts/check-shen-jit.sh` that runs the reader and checks `(955, 0)`. The reader would become
   an `--image` mode of `tests/shen-jit/stage0_to_rocq.py`, append-only. Add `ImgMut.v`'s two mutants to
   `tests/mutate-shen-jit.py`.
3. Cut the 18-minute data compile. One option is to emit fewer, larger literals. Another is to have the lane's existing
   per-file `S0_*.v` files import one image module, so the `.sbc` trees are not parsed twice.
4. Record it in the ledger as an `instance-validation`.

Under Coq 8.18 (`make prove`) the spike's files are UNKNOWN: they were compiled only under Rocq 9.3.

## Evidence (this run)

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
