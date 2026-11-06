#!/bin/bash
# Route A proofs live apart from coq/, so that a broken rung can't affect route B's gate or its mutants.
here=$(cd "$(dirname "$0")" && pwd)
cp "$here"/coq-a/*.v /work-s7/theories/Examples/emitter_ns/
W=/work-s7 bash "$here/dbuild.sh" "$@"
