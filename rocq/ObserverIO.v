(* Checked data-flow in the actual captured observer entry. This is a
   structural IO-plan proof, not a claim that native reads/writes are truthful. *)
From Coq Require Import List String Arith.
From Buri Require Import Native ObserverInput.
Import ListNotations.
Module ObserverIO.
Import Native.Native.
Open Scope string_scope.
Local Transparent observer_nodes observer_text.
Definition entry := Eval vm_compute in match observer_nodes with
 | Some ds => nth 2 ds Nil | _ => Nil end.
Theorem entry_from_capture : observer_nodes = Some
 (match observer_nodes with Some xs => xs | None => [] end) /\
 match observer_nodes with Some xs => nth 2 xs Nil = entry | None => False end.
Proof. vm_compute; split; reflexivity. Qed.
Local Opaque observer_nodes observer_text.
Definition bindings := match elements entry with
 | Some [_;_;e] => match elements e with Some [_;bs;_] => match elements bs with Some xs=>xs|_=>[] end | _=>[] end
 | _=>[] end.
Definition entry_body := match elements entry with
 | Some [_;_;e] => match elements e with Some [_;_;b]=>b|_=>Nil end | _=>Nil end.
Definition q x := L [Symbol "quote";Symbol x].
Theorem source_read_parse_snapshot :
 nth 3 bindings Nil = L [Symbol "W5973";L [Symbol "kl:read-file-as-string";Symbol "V5967"]] /\
 nth 4 bindings Nil = L [Symbol "W5974";L [Symbol "kl:set";q "buri.observed-source";Symbol "W5973"]] /\
 nth 5 bindings Nil = L [Symbol "W5975";L [Symbol "kl:buri.observe-forms";
   L [Symbol "kl:read-from-string";Symbol "W5973"]]] /\
 match elements entry_body with
 | Some (_::first_write::_) => first_write = L [Symbol "kl:write-to-file";
    L [Symbol "string-append";Symbol "V5968";Text ".source"];Symbol "W5973"]
 | _ => False end.
Proof. vm_compute; repeat split; reflexivity. Qed.
Fixpoint occurrences name v := match v with
 | Symbol s => if String.eqb name s then 1 else 0
 | Pair a b => occurrences name a + occurrences name b | _ => 0 end.
Theorem single_source_read_token : occurrences "kl:read-file-as-string" entry = 1.
Proof. vm_compute; reflexivity. Qed.
Theorem single_source_parse_token : occurrences "kl:read-from-string" entry = 1.
Proof. vm_compute; reflexivity. Qed.
End ObserverIO.
