(* Adversarial examples complement the generic proofs; they do not discharge
   implementation preservation for a Shen port. *)
From Coq Require Import List String ZArith.
From Buri Require Import NativeArithmetic Wire Resolve Normalize NativeValidation.
Import ListNotations.
Import Wire.Wire Resolve.Resolve NativeValidation.NativeValidation.
Open Scope string_scope.

Example nil_roundtrip : decode_text "00" = Some Nil.
Proof. reflexivity. Qed.
Example truncated_prefix : decode [false] = None.
Proof. reflexivity. Qed.
Example trailing_data : decode [false;false;true] = None.
Proof. reflexivity. Qed.
Example invalid_text_digit : decode_text "002" = None.
Proof. reflexivity. Qed.
Example incomplete_octet : decode [false;true;false;true;true] = None.
Proof. reflexivity. Qed.
Example atom_tags_distinct : capture (Atom true "1") <> capture (Atom false "1").
Proof. discriminate. Qed.
Example malformed_integer : integer "12x" = None.
Proof. vm_compute; reflexivity. Qed.
Example empty_integer : integer "" = None.
Proof. reflexivity. Qed.
Example incomplete_negative : integer "-" = None.
Proof. reflexivity. Qed.
Example negative_integer : integer "-17" = Some (-17)%Z.
Proof. vm_compute; reflexivity. Qed.
Example large_integer : integer "9223372036854775808" = Some 9223372036854775808%Z.
Proof. vm_compute; reflexivity. Qed.
Example duplicate_inputs : unique_names ["x";"x"] = false.
Proof. vm_compute; reflexivity. Qed.
Example unbound_names : agrees [] (Name "x") (Name "x") = false.
Proof. vm_compute; reflexivity. Qed.
Example wrong_operator : agrees ["x";"y"]
 (Plus (Name "x") (Name "y")) (Times (Name "x") (Name "y")) = false.
Proof. vm_compute; reflexivity. Qed.
Example alpha_renaming_and_let : agrees ["x";"y"]
 (Plus (Times (Name "x") (Num 3)) (Name "y"))
 (Let "temporary" (Times (Name "x") (Num 3)) (Plus (Name "temporary") (Name "y"))) = true.
Proof. vm_compute; reflexivity. Qed.
Example wrong_shadow_capture : agrees ["x";"y"]
 (Let "x" (Plus (Name "x") (Num 1)) (Minus (Name "x") (Name "y")))
 (Let "z" (Plus (Name "x") (Num 1)) (Minus (Name "x") (Name "y"))) = false.
Proof. vm_compute; reflexivity. Qed.
Example sequential_shadowing : agrees ["x"]
 (Let "x" (Plus (Name "x") (Num 1)) (Let "x" (Times (Name "x") (Num 2)) (Name "x")))
 (Times (Plus (Name "x") (Num 1)) (Num 2)) = true.
Proof. vm_compute; reflexivity. Qed.
Example source_let_binds_after_rhs : resolve ["x"] (Let "x" (Name "x") (Name "x")) =
 Some (KLet (KVar 0) (KVar 0)).
Proof. vm_compute; reflexivity. Qed.
Example reject_host_code : decode_expr 10 KLambda
 (Cons (Atom false "eval-kl") (Cons (Atom true "1") Nil)) = None.
Proof. vm_compute; reflexivity. Qed.
Example reject_mutation : decode_expr 10 KLambda
 (Cons (Atom false "set") (Cons (Atom false "x") (Cons (Atom true "1") Nil))) = None.
Proof. vm_compute; reflexivity. Qed.
Example insufficient_decode_budget : decode_expr 0 KLambda (Atom true "1") = None.
Proof. reflexivity. Qed.
Example wrong_profile : capture_records (Cons (Atom false "another-profile") (Cons Nil Nil)) = None.
Proof. vm_compute; reflexivity. Qed.

Example symbol_integer_confusion : decode_expr 10 KLambda (Atom false "17") = None.
Proof. vm_compute; reflexivity. Qed.
Example boolean_variable_confusion : decode_expr 10 KLambda (Atom false "true") = None.
Proof. vm_compute; reflexivity. Qed.
Example reserved_scope : decode_scope (Cons (Atom false "true") Nil) = None.
Proof. vm_compute; reflexivity. Qed.
