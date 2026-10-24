From Coq Require Import List String ZArith.
From Buri Require Import Native NativeRuntime.
Import ListNotations Native.Native.
Open Scope string_scope.
Definition no_program : program := fun _ => None.
Definition no_environment : env := fun _ => None.
Definition failure owner := Call "error" [Lit (Symbol owner);Lit (Text "failed")].
Example left_error_first : eval 20 no_program no_environment
 (Call "cons" [failure "left";failure "right"]) = Raised (Symbol "left") (Text "failed").
Proof. reflexivity. Qed.
Example machine_left_error_first : NativeRuntime.execute 50 no_program
 (NativeRuntime.Enter no_environment (Call "cons" [failure "left";failure "right"]),[]) =
 Raised (Symbol "left") (Text "failed").
Proof. reflexivity. Qed.
Example exhaustion_is_distinct : eval 0 no_program no_environment (failure "left") = Exhausted.
Proof. reflexivity. Qed.
Example unknown_is_distinct : eval 10 no_program no_environment (Var "missing") = Unsupported.
Proof. reflexivity. Qed.
Example scheme_zero_is_true : eval 10 no_program no_environment
 (If (Lit (Integer 0)) (Lit (Text "yes")) (Lit (Text "no"))) = Returned (Text "yes").
Proof. reflexivity. Qed.
Example false_short_circuits : eval 10 no_program no_environment
 (And (Lit (Boolean false)) (failure "unreachable")) = Returned (Boolean false).
Proof. reflexivity. Qed.
Example true_short_circuits : eval 10 no_program no_environment
 (Or (Lit (Integer 0)) (failure "unreachable")) = Returned (Integer 0).
Proof. reflexivity. Qed.
Example malformed_parallel_let_rejected : decode 20
 (L [Symbol "let";L [L [Symbol "x";Integer 1];L [Symbol "y";Integer 2]];Symbol "x"]) = None.
Proof. reflexivity. Qed.
Example sequential_shadowing :
 match decode 20 (L [Symbol "let*";
 L [L [Symbol "x";Integer 1];L [Symbol "x";L [Symbol "+";Symbol "x";Integer 1]]];Symbol "x"]) with
 | Some e => eval 20 no_program no_environment e | _ => Unsupported end = Returned (Integer 2).
Proof. reflexivity. Qed.
Example native_boolean_not_a_symbol :
 eval 10 no_program no_environment (Var "false") = Unsupported /\
 eval 10 no_program no_environment (Lit (Boolean false)) = Returned (Boolean false).
Proof. split; reflexivity. Qed.
Example dynamic_evaluation_unavailable : eval 10 no_program no_environment
 (Call "eval" [Lit (Symbol "some-global")]) = Unsupported.
Proof. reflexivity. Qed.
Example fault_cannot_forge_success : NativeRuntime.execute 10 no_program
 (NativeRuntime.Fault (Returned (Integer 1)),[]) = Unsupported.
Proof. reflexivity. Qed.
