# E2E-22 Chez nanopass captures: provenance

These are inert captured data plus the orchestration scripts that made them.
Findings are in [CHEZ-NANOPASS](../../docs/CHEZ-NANOPASS.md). Hashes are in
`SHA256SUMS`, which `make prove` checks.

| File | What it is |
|---|---|
| `upstream/np-languages.ss` | exact copy of Chez Scheme 10.3.0 `s/np-languages.ss` (tag v10.3.0, commit `adfaf9e6`; identical in `csv10.3.0.tar.gz`, sha256 `d237d987...`). Apache-2.0, see `LICENSES/Chez-Scheme.txt` |
| `tarm64le-buri-arm-add.np` | output of `scripts/np-dump.ss` under the ARM lane's native tarm64le Chez 10.3.0 build (`nix/arm/build-chez-10.3.0-aarch64.sh`; binaries hashed in `ports/arm/README.md`) run by qemu-user 11.1.2 |
| `ta6le-buri-arm-add.np` | the same script under the stage-1 x86_64 build of the same release |
| `scripts/np-dump.ss` | compiles `(define (kl:buri-arm-add V3015 V3016) (+ V3015 V3016))` with `eval` and `($np-tracer #t)`, and replays the untraced front end. It prints with `print-gensym 'pretty/suffix` and `print-graph #t`. Its only printing change is that `info` records show their fields |
| `scripts/run-np-dump.sh` | reruns both captures. Two runs gave byte-identical files |
| `scripts/chez-passes.py` | regenerates `spec/chez-passes.json` from a Chez source tree and the trace. It is a reading aid |

Each `.np` file is made of sections that begin with a line `@@@ NAME` and end
with a line `@@@ end`. The sections are:

* `parameters`;
* `source`;
* the front-end passes, printed with `$uncprep`;
* `expand/optimize-output`;
* `np-trace`, which is the tracer's own `output of PASS:` stream.

The register-allocator sub-passes print a block listing and a dot graph, not
data.

The `.np` files are captures. They are not proofs.
`scripts/package-chez-np.py` packages the files as bytes, and
`scripts/check-chez-np-package.py` checks that packaging byte for byte. Only
the Rocq modules `rocq/ChezNp*.v` decide anything.
