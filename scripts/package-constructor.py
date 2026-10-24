"""Literal native constructor capture, without semantic transformations."""
from pathlib import Path
import sys

source, destination = map(Path, sys.argv[1:])
bits = source.read_bytes()
if not bits or any(b not in b'01' for b in bits):
    raise SystemExit('Expected literal ASCII bits')
destination.write_text('''From Coq Require Import List String.
From Buri Require Import Wire Native NativeHelpers Sealed.
Import ListNotations Native.Native NativeHelpers.NativeHelpers.
Open Scope string_scope.
Definition constructor_text : string := "''' + bits.decode('ascii') + '''".
Definition constructor_decode :=
 match Wire.decode_text constructor_text with
 | Some (Wire.Cons (Wire.Atom false "buri-constructor-native-1") (Wire.Cons tagged Wire.Nil)) =>
   match untag 500 tagged with Some root => match elements root with
     | Some xs => match definitions 500 xs with Some ds => ds | _ => [] end
     | _ => [] end | _ => [] end
 | _ => [] end.
Definition constructor_program := Eval vm_compute in constructor_decode.
Theorem constructor_exact : constructor_decode = constructor_program.
Proof. vm_compute. reflexivity. Qed.
Global Opaque constructor_text constructor_decode.
Theorem constructor_definitions_complete : List.length constructor_program = 10.
Proof. vm_compute. reflexivity. Qed.
Definition native_def name args body := L [Symbol "define";Pair name args;body].
Definition native_binding name args body := L [name;L [Symbol "lambda";args;body]].
Theorem constructor_definition : forall name args body,
 run 100 constructor_program "kl:buri.sealed-definition" [native_def name args body] =
 Returned (native_binding name args body).
Proof. intros. vm_compute. reflexivity. Qed.
Definition record source name args body := L [source;native_def name args body].
Theorem constructor_targets : forall sa sb sc na nb nc aa ab ac ba bb bc,
 run 100 constructor_program "kl:buri.sealed-targets"
 [L [record sa na aa ba;record sb nb ab bb;record sc nc ac bc]] =
 Returned (L [native_binding na aa ba;native_binding nb ab bb;native_binding nc ac bc]).
Proof. intros. vm_compute. reflexivity. Qed.
Theorem constructor_helpers : run 100 constructor_program "kl:buri.sealed-helpers" [] =
 Returned (lift SealedCapture.helper_template).
Proof. vm_compute. reflexivity. Qed.
Theorem constructor_imports : run 100 constructor_program "kl:buri.sealed-imports" [] =
 Returned (lift SealedCapture.imports).
Proof. vm_compute. reflexivity. Qed.
Definition append_values a b := fold_right Pair b a.
Theorem constructor_program_correct : forall sa sb sc na nb nc aa ab ac ba bb bc,
 run 100 constructor_program "kl:buri.sealed-program"
 [L [record sa na aa ba;record sb nb ab bb;record sc nc ac bc]] =
 Returned (L [Symbol "letrec";
   append_values
    (match elements (lift SealedCapture.helper_template) with Some xs => xs | _ => [] end)
    (L [native_binding na aa ba;native_binding nb ab bb;native_binding nc ac bc]);
   Symbol "kl:buri.wire"]).
Proof. intros. vm_compute. reflexivity. Qed.
Theorem constructor_rejects_missing : run 100 constructor_program "kl:buri.sealed-program" [Nil] =
 Raised (Symbol "buri.sealed-targets") (Text "Sealed encoder requires exactly three observed pairs").
Proof. vm_compute. reflexivity. Qed.
Theorem constructor_rejects_bad_definition :
 run 100 constructor_program "kl:buri.sealed-definition" [Nil] =
 Raised (Symbol "buri.sealed-definition") (Text "Sealed encoder requires a procedure definition").
Proof. vm_compute. reflexivity. Qed.
Theorem constructor_request : forall program,
 run 100 constructor_program "kl:buri.sealed-request" [program] =
 Returned (L [Symbol "eval";L [Symbol "quote";program];
  L [Symbol "environment";L [Symbol "quote";
    Pair (Symbol "only") (Pair (L [Symbol "chezscheme"]) (lift SealedCapture.imports))]]]).
Proof. intros. vm_compute. reflexivity. Qed.
Theorem constructor_executor_shape : exists name,
 lookup constructor_program "kl:buri.sealed-eval" =
 Some (Def [name] (Call "eval" [Call "kl:buri.sealed-request" [Var name]])).
Proof. vm_compute. eexists. reflexivity. Qed.
Theorem constructor_entry_shape : exists name,
 lookup constructor_program "kl:buri.make-sealed-encoder" =
 Some (Def [name] (Call "kl:buri.sealed-eval" [Call "kl:buri.sealed-program" [Var name]])).
Proof. vm_compute. eexists. reflexivity. Qed.
''')
