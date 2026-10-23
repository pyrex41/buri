From Coq Require Import List String.
From Buri Require Import Wire Encoder.
Import ListNotations.
Open Scope string_scope.
Import Encoder.
Example encoder_no_fuel : eval 0 [] (Lit (Text "")) = Exhausted.
Proof. reflexivity. Qed.
Example encoder_lazy_branch : eval 2 [] (If (Lit (Boolean true)) (text "ok") (unary Head dummy)) = Returned (Text "ok").
Proof. reflexivity. Qed.
Example encoder_byte_boundary : eval 100 [Number 128;Number 8] (body Byte) = Returned (Text "00000001").
Proof. vm_compute. reflexivity. Qed.
Example encoder_string_boundary : eval 100 [Text "A";Number 0] (body Str) = Returned (Text "1100000100").
Proof. vm_compute. reflexivity. Qed.
Example encoder_nonbyte_refused : primitive ByteRange (Number 256) (Number 0) = Some (Boolean false).
Proof. reflexivity. Qed.
Example encoder_bad_projection : primitive Head (Text "x") (Number 0) = None.
Proof. reflexivity. Qed.
Example encoder_numeric_atom : eval 100 [Data (Wire.Atom true "1");Number 0] (body Datum) = Returned (Text "0111100011000").
Proof. vm_compute. reflexivity. Qed.
Example encoder_symbol_atom : eval 100 [Data (Wire.Atom false "1");Number 0] (body Datum) = Returned (Text "0101100011000").
Proof. vm_compute. reflexivity. Qed.
Example encoder_invalid_condition : eval 2 [] (If dummy (text "a") (text "b")) = Stuck.
Proof. reflexivity. Qed.
Example encoder_left_to_right_failure :
 eval 3 [] (Op Cat (unary Head dummy) (Call Datum (Lit (Data Wire.Nil)) dummy)) = Stuck.
Proof. reflexivity. Qed.
