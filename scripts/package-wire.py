"""Package exact 0/1 capture bytes as a Rocq string; no semantic decoding."""
from pathlib import Path
import sys
source, destination = map(Path, sys.argv[1:])
bits = source.read_bytes()
if not bits or any(b not in b'01' for b in bits):
    raise SystemExit('Capture must contain only ASCII 0 and 1 bytes')
text = bits.decode('ascii')
preamble = '''(* Exact captured bytes. Semantic decoding/validation occurs inside Rocq. *)
From Coq Require Import List String.
From Buri Require Import Wire Resolve NativeValidation.
Import ListNotations.
Open Scope string_scope.
Import Wire.Wire NativeValidation.NativeValidation.
Definition native_capture_text : string := "'''
proofs = '''".
Definition native_capture_ok : bool := count_ok 100 native_capture_text 12.
Theorem native_capture_checked : native_capture_ok = true.
Proof. vm_compute. reflexivity. Qed.
Global Opaque native_capture_text.
Theorem native_capture_sound : exists raw es,
 check_capture 100 native_capture_text = Some (raw,es) /\\
 List.length es = 12 /\\ capture raw = native_capture_text /\\ Forall entry_sound es.
Proof. exact (checked_count_sound 100 native_capture_text 12 native_capture_checked). Qed.
Theorem native_capture_record_coverage : exists raw es ds,
 check_capture 100 native_capture_text = Some (raw,es) /\\
 List.length es = 12 /\\
 raw = Cons (Atom false "buri-native-1") (Cons (list_data ds) Nil) /\\
 Forall2 (fun d e => check_record 100 d = Some e) ds es.
Proof. exact (checked_count_coverage 100 native_capture_text 12 native_capture_checked). Qed.
'''
destination.write_text(preamble + text + proofs)
