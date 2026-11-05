# Optional Coalton typing experiment

This is an independent tool assessment, outside Búri's implementation and acceptance
path. It does not define Búri semantics, construct Búri certificates, or adapt a
Shen port. Those responsibilities remain in Shen under `AGENTS.md`. Coalton is
not adopted as a dependency, and no global gate loads this experiment.

The tiny arithmetic syntax tree is illustrative standalone Coalton code. Running
it tests three observations: a typed expression computes 42, an ill-typed call
raises Coalton's `TC-ERROR`, and an explicit Common Lisp `check-type` boundary
rejects a string. None is a universal theorem or a compiler-correctness result.

## Reproduce

Install SBCL and ASDF; make the pinned source trees below discoverable with ASDF's
source registry. For example, keep all dependency checkouts and the Coalton
checkout in a dedicated `deps` directory, then run from this directory:

```sh
export CL_SOURCE_REGISTRY="$(pwd)/deps//:"
unset COALTON_ENV
sbcl --script spike.lisp
```

The registry path must point to the directory containing the actual sources.
No dependencies are downloaded by the spike. Use a fresh ASDF cache when changing
Coalton development/release mode; compiler and library must use the same mode.
The recorded run used development mode only, on SBCL 2.2.9.debian, Linux x86-64.
It is not an ARM execution test. Other Lisp implementations and release mode
have not been tested here.

Pinned source dependencies used for the recorded run:

| Repository | Commit |
| --- | --- |
| https://github.com/coalton-lang/coalton | `0b5c10fa14058a9460ee38e69634afa5c5bd10db` |
| https://github.com/s-expressionists/Concrete-Syntax-Tree | `f79dab6b6d14000259449c169b501cc6398b3f54` |
| https://github.com/s-expressionists/Eclector | `1088a7998f0d205da12ff48de7238b1008a31792` |
| https://github.com/robert-strandh/Acclimation | `9339b92e16e6a6784488f8bac82c189ae4bab4aa` |
| https://github.com/Shinmera/float-features | `cd5dab00d2f4a562d65f46b3fc1cecec308e2443` |
| https://github.com/Shinmera/documentation-utils | `fcbd927dee7f311915a27ee557e3db1d4510403c` |
| https://github.com/Shinmera/trivial-indent | `87b35ff9202b107230e35790e93c471cc7880900` |

Additional Common Lisp source packages used in that run (Debian package versions):

| Package | Version |
| --- | --- |
| cl-alexandria | `20211025.gita67c3a6-1` |
| cl-closer-mop | `2:20220227.giteabdf6a-1` |
| cl-named-readtables | `20201221.gitc5689a4-1` |
| cl-trivial-features | `20210228.gitf6e8dd7-2` |
| cl-trivial-garbage | `20211229.gitb3af9c0-1` |
| cl-trivial-gray-streams | `20210117.git2b3823e-1` |

`source-error` and `coalton-asdf` are included in the Coalton source tree.
These pins document the tested environment; this is not a hermetic build lock.

Expected check output (compiler startup messages omitted):

```text
PASS typed IR evaluates to 42
PASS ill-typed expression rejected (TC-ERROR)
PASS explicit Lisp boundary rejects string
NOTE: independent experiment only; no Rocq proof or Buri/Shen integration.
```

See [the assessment](../../docs/COALTON-ASSESSMENT.md) for the trust boundaries
and adoption recommendation.
