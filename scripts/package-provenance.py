"""Literal capture packaging only; selected-body acceptance is proved in Rocq."""
from pathlib import Path
import sys
kind, source, destination = sys.argv[1:]
if kind not in ('bootstrap', 'observer', 'compiler_pass', 'checked_io', 'order_call', 'observer_forms', 'io_read', 'equality_core', 'equality_seal'):
    raise SystemExit('Unknown packaging profile')
bits = Path(source).read_bytes()
if not bits or any(b not in b'01' for b in bits):
    raise SystemExit('Expected literal ASCII bits')
# Selection is explicit in the theorem input, not semantic Python decoding.
count, names = {'bootstrap': (2, ['kl:buri.native-bytes', 'kl:buri.native-node']),
                'observer': (1, ['kl:buri.install-observed']),
                'compiler_pass': (1, ['kl:_scm.merge-nested-lets']),
                'checked_io': (1, ['kl:buri.checked-write']),
                'order_call': (6, ['kl:_scm.merge-nested-lets','kl:_scm.simple-scheme-expression?','kl:_scm.has-computation?','kl:_scm.fresh-call-variable','kl:_scm.order-call-inputs','kl:_scm.order-call']),
                'observer_forms': (2, ['kl:buri.install-observed','kl:buri.observe-forms']),
                'io_read': (1, ['kl:read-file-as-string']),
                'equality_core': (4, ['kl:buri.eq2-derive','kl:buri.eq2-sym','kl:buri.eq2-trans','kl:buri.eq2-cong']),
                'equality_seal': (4, ['kl:buri.eq2-seal-definition','kl:buri.eq2-seal-program','kl:buri.eq2-seal-request','kl:buri.make-sealed-eq2'])}[kind]
text = '''From Coq Require Import List String.
From Buri Require Import Wire Native.
Import ListNotations Native.Native.
Open Scope string_scope.
Definition CAP_text : string := "BITS".
Definition CAP_nodes :=
 match Wire.decode_text CAP_text with
 | Some (Wire.Cons (Wire.Atom false "buri-constructor-native-1") (Wire.Cons tagged Wire.Nil)) =>
   match untag 500 tagged with Some root => elements root | _ => None end
 | _ => None end.
Definition CAP_decode := match CAP_nodes with
 | Some xs => definitions 500 (firstn COUNT (skipn OFFSET xs)) | None => None end.
Definition CAP_program := Eval vm_compute in
 match CAP_decode with Some ds => ds | None => [] end.
Theorem CAP_exact : CAP_decode = Some CAP_program.
Proof. vm_compute. reflexivity. Qed.
Theorem CAP_names : map fst CAP_program = NAMES.
Proof. vm_compute. reflexivity. Qed.
Global Opaque CAP_text CAP_nodes CAP_decode.
'''
text = text.replace('CAP', kind).replace('BITS', bits.decode('ascii')).replace('COUNT', str(count))
text = text.replace('OFFSET', '3' if kind == 'checked_io' else '0')
text = text.replace('NAMES', '[' + ';'.join('"' + n + '"' for n in names) + ']')
if kind in ('equality_core','equality_seal'):
    complete = ('Theorem '+kind+'_complete : match '+kind+'_nodes with\n'
                ' | Some xs => List.length xs = '+str(count)+' | None => False end.\n'
                'Proof. vm_compute; reflexivity. Qed.\n')
    text = text.replace('Global Opaque', complete+'Global Opaque')
Path(destination).write_text(text)
