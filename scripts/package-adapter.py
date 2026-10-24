"""Package literal capture bytes; Rocq performs all semantic checking."""
from pathlib import Path
import sys
source, destination = map(Path, sys.argv[1:])
bits = source.read_bytes()
if not bits or any(b not in b'01' for b in bits):
    raise SystemExit('Expected literal ASCII bits')
destination.write_text('''From Coq Require Import List String.
From Buri Require Import Wire Native NativeHelpers.
Import ListNotations Native.Native.
Open Scope string_scope.
Definition adapter_text : string := "''' + bits.decode('ascii') + '''".
Definition adapter_decode :=
 match Wire.decode_text adapter_text with
 | Some (Wire.Cons (Wire.Atom false "buri-constructor-native-1") (Wire.Cons tagged Wire.Nil)) =>
   match untag 500 tagged with Some root => match elements root with
     | Some xs => definitions 500 xs | _ => None end
     | _ => None end
 | _ => None end.
Definition adapter_program := Eval vm_compute in
 match adapter_decode with Some ds => ds | None => [] end.
Theorem adapter_exact : adapter_decode = Some adapter_program.
Proof. vm_compute. reflexivity. Qed.
Theorem adapter_names : map fst adapter_program =
 ["kl:buri.kl-bytes";"kl:buri.kl-node";"kl:buri.capture-encoder-kl"].
Proof. vm_compute. reflexivity. Qed.
Global Opaque adapter_text adapter_decode.
''')
