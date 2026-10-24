"""Literal capture packaging; all dependency/translation decisions are Rocq's."""
from pathlib import Path
import sys

source, destination = map(Path, sys.argv[1:])
bits = source.read_bytes()
if not bits or any(b not in b'01' for b in bits):
    raise SystemExit('Capture must contain only ASCII 0 and 1 bytes')
destination.write_text('''From Coq Require Import String.
From Buri Require Import Sealed.
Open Scope string_scope.
Definition sealed_text : string := "''' + bits.decode('ascii') + '''".
Theorem sealed_checked : SealedCapture.check sealed_text = true.
Proof. vm_compute. reflexivity. Qed.
Global Opaque sealed_text.
''')
