From Coq Require Import List String.
From Buri Require Import Encoder EncoderNames EncoderFrontend ObservedEncoder.
Import ListNotations.
Open Scope string_scope.
Import Encoder.Encoder EncoderNames.EncoderNames EncoderFrontend.EncoderFrontend.
Definition ns xs := fold_right Pair Nil xs.
Definition rd scope n := match ObservedEncoder.decode 30 n with Some e => resolve scope e | None => None end.
Example observed_sequential_scope : rd [] (ns [Sym "let*";
 ns [ns [Sym "_scm.a";Num 8];ns [Sym "_scm.b";Sym "_scm.a"]];Sym "_scm.b"]) =
 Some (Let (Lit (Number 8)) (Let (Var 0) (Var 0))).
Proof. vm_compute; reflexivity. Qed.
Example observed_shadow_scope : rd ["X"] (ns [Sym "let";ns [ns [Sym "X";Sym "X"]];Sym "X"]) = Some (Let (Var 0) (Var 0)).
Proof. vm_compute; reflexivity. Qed.
Example observed_parallel_refused : ObservedEncoder.decode 30 (ns [Sym "let";
 ns [ns [Sym "X";Num 8];ns [Sym "Y";Sym "X"]];Sym "Y"]) = None.
Proof. vm_compute; reflexivity. Qed.
Example observed_wrong_tail_binder : ObservedEncoder.decode 30 (ns [Sym "let";
 ns [ns [Sym "tmp";Sym "X"]];ns [Sym "substring";Sym "tmp";Num 1;ns [Sym "string-length";Sym "OTHER"]]]) = None.
Proof. vm_compute; reflexivity. Qed.
Example observed_wrong_divisor : ObservedEncoder.decode 30 (ns [Sym "kl:floor";ns [Sym "non-rational-/";Sym "X";Num 3]]) = None.
Proof. vm_compute; reflexivity. Qed.
Example observed_arbitrary_assert_refused : ObservedEncoder.decode 30 (ns [Sym "kl:_scm.assert-boolean";Sym "X"]) = None.
Proof. vm_compute; reflexivity. Qed.
Example observed_unbound : rd [] (Sym "_scm.missing") = None.
Proof. reflexivity. Qed.
Example observed_extra_record : ObservedEncoder.check_program 30 (ns [Nil;Nil;Nil;Nil]) = None.
Proof. vm_compute; reflexivity. Qed.
