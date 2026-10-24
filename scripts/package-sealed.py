"""Literal capture packaging; all dependency/translation decisions are Rocq's."""
from pathlib import Path
import sys

source, destination = map(Path, sys.argv[1:])
bits = source.read_bytes()
if not bits or any(b not in b'01' for b in bits):
    raise SystemExit('Capture must contain only ASCII 0 and 1 bytes')
destination.write_text('''From Coq Require Import String List ZArith.
From Buri Require Import Sealed Native NativeRuntime NativeHelpers Wire.
Import ListNotations Native.Native.
Open Scope string_scope.
Definition sealed_text : string := "''' + bits.decode('ascii') + '''".
Theorem sealed_checked : SealedCapture.check sealed_text = true.
Proof. vm_compute. reflexivity. Qed.

Definition sealed_native_decode := match SealedCapture.unpack sealed_text with
 | Some root => match EncoderFrontend.EncoderFrontend.elements root with
   | Some [capsule;_;_] => match EncoderFrontend.EncoderFrontend.elements capsule with
     | Some [_;bindings;_] => match elements (NativeHelpers.lift bindings) with
       | Some xs => NativeHelpers.helper_definitions xs | _ => None end
     | _ => None end | _ => None end | _ => None end.
Definition sealed_native_program := Eval vm_compute in
 match sealed_native_decode with Some ds => ds | _ => [] end.
Theorem sealed_native_exact : sealed_native_decode = Some sealed_native_program.
Proof. vm_compute. reflexivity. Qed.
Global Opaque sealed_text sealed_native_decode.
Theorem sealed_native_complete : List.length sealed_native_program = 10.
Proof. vm_compute. reflexivity. Qed.
Theorem sealed_native_helpers : firstn 7 sealed_native_program = NativeHelpers.helpers.
Proof. vm_compute. reflexivity. Qed.
Definition sealed_start input : NativeRuntime.machine :=
 match lookup sealed_native_program "kl:buri.wire" with
 | Some d => (NativeRuntime.Enter (arguments (params d) [input]) (body d),[])
 | _ => (NativeRuntime.Fault Unsupported,[]) end.
Theorem sealed_native_nil :
 NativeRuntime.execute 200 (lookup sealed_native_program) (sealed_start Nil) = Returned (Text "00").
Proof. vm_compute. reflexivity. Qed.
Theorem sealed_native_integer :
 NativeRuntime.execute 2000 (lookup sealed_native_program) (sealed_start (Integer (-17))) =
 Returned (Text (Wire.capture (Wire.Atom true "-17"))).
Proof. vm_compute. reflexivity. Qed.
Theorem sealed_native_symbol :
 NativeRuntime.execute 3000 (lookup sealed_native_program) (sealed_start (Symbol "alpha")) =
 Returned (Text (Wire.capture (Wire.Atom false "alpha"))).
Proof. vm_compute. reflexivity. Qed.
Theorem sealed_native_pair :
 NativeRuntime.execute 3000 (lookup sealed_native_program) (sealed_start (Pair (Integer 1) Nil)) =
 Returned (Text (Wire.capture (Wire.Cons (Wire.Atom true "1") Wire.Nil))).
Proof. vm_compute. reflexivity. Qed.
Theorem sealed_native_string_error :
 NativeRuntime.execute 200 (lookup sealed_native_program) (sealed_start (Text "no")) =
 Raised (Symbol "buri.wire") (Text "Unsupported wire datum").
Proof. vm_compute. reflexivity. Qed.
Theorem sealed_native_boolean_error : forall b,
 NativeRuntime.execute 200 (lookup sealed_native_program) (sealed_start (Boolean b)) =
 Raised (Symbol "buri.wire") (Text "Unsupported wire datum").
Proof. intros []; vm_compute; reflexivity. Qed.
Theorem sealed_native_concurrent : forall input wa wb wc x y,
 NativeRuntime.concurrent_reaches (lookup sealed_native_program)
  (sealed_start input,wa) ((NativeRuntime.Deliver x,[]),wb) ->
 NativeRuntime.concurrent_reaches (lookup sealed_native_program)
  (sealed_start input,wa) ((NativeRuntime.Deliver y,[]),wc) -> x = y.
Proof. intros; eapply NativeRuntime.concurrent_output_unique; eauto. Qed.
''')
