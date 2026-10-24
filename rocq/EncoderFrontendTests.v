From Coq Require Import List String.
From Buri Require Import Wire Encoder EncoderNames EncoderFrontend.
Import ListNotations.
Open Scope string_scope.
Import Encoder.Encoder EncoderNames.EncoderNames EncoderFrontend.EncoderFrontend.
Definition list_node xs := fold_right Pair Nil xs.
Example frontend_alpha_scope :
 match decode 20 (list_node [Sym "let";Sym "W7";Num 8;Sym "W7"]) with
 | Some e => resolve ["V9"] e | None => None end = Some (Let (Lit (Number 8)) (Var 0)).
Proof. vm_compute. reflexivity. Qed.
Example frontend_shadowing : resolve ["X"] (NBind "X" (NVariable "X") (NVariable "X")) = Some (Let (Var 0) (Var 0)).
Proof. reflexivity. Qed.
Example frontend_unbound : resolve ["X"] (NVariable "Y") = None.
Proof. reflexivity. Qed.
Example frontend_duplicate_parameters : params Byte (list_node [Sym "X";Sym "X"]) = None.
Proof. reflexivity. Qed.
Example frontend_wrong_arity : params Byte (list_node [Sym "X"]) = None.
Proof. reflexivity. Qed.
Example frontend_wrong_name : decode_definition 20 Byte
 (list_node [Sym "defun";Sym "other";list_node [Sym "X";Sym "Y"];TextNode ""]) = None.
Proof. reflexivity. Qed.
Example frontend_unknown_call : decode 20 (list_node [Sym "eval-kl";Sym "X"]) = None.
Proof. reflexivity. Qed.
Example frontend_changed_divisor : decode 20 (list_node [Sym "floor";list_node [Sym "/";Sym "X";Num 3]]) = None.
Proof. reflexivity. Qed.
Example frontend_mixed_range : decode 20 (list_node [Sym "and";
 list_node [Sym ">=";Sym "X";Num 0];list_node [Sym "<";Sym "Y";Num 256]]) = None.
Proof. reflexivity. Qed.
Example frontend_effectful_range : decode 20 (list_node [Sym "and";
 list_node [Sym ">=";list_node [Sym "buri.wire";Sym "X"];Num 0];list_node [Sym "<";Sym "X";Num 256]]) = None.
Proof. reflexivity. Qed.
Definition raw_list xs := fold_right Wire.Cons Wire.Nil xs.
Example frontend_text_tag : untag 20 (raw_list [Wire.Atom false "text";
 raw_list [Wire.Atom true "48"]]) = Some (TextNode "0").
Proof. vm_compute. reflexivity. Qed.
Example frontend_symbol_tag : untag 20 (raw_list [Wire.Atom false "sym";Wire.Atom false "0"]) = Some (Sym "0").
Proof. reflexivity. Qed.
Example frontend_nonbyte : byte_string (raw_list [Wire.Atom true "256"]) = None.
Proof. vm_compute. reflexivity. Qed.
Example frontend_extra_definition : check_program 20 (list_node [Nil;Nil;Nil;Nil]) = None.
Proof. reflexivity. Qed.
Example frontend_no_fuel : untag 0 (raw_list [Wire.Atom false "nil"]) = None.
Proof. reflexivity. Qed.
Example frontend_wrong_profile : capture_program 20 (raw_list [Wire.Atom false "wrong";Wire.Nil]) = None.
Proof. reflexivity. Qed.
