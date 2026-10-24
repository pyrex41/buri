(* Transfer the captured Shen constructor's existing evaluator proofs to
   instruction execution. No duplicate hand-written constructor is used. *)
From Coq Require Import List String.
From Buri Require Import Native NativeRuntime NativeSimulation NativeHelpers ConstructorInput Sealed.
Import ListNotations Native.Native NativeRuntime.NativeRuntime NativeSimulation.NativeSimulation NativeHelpers.NativeHelpers.
Open Scope string_scope.
Theorem constructor_machine_program : forall sa sb sc na nb nc aa ab ac ba bb bc,
 exists steps, NativeRuntime.invoke steps constructor_program "kl:buri.sealed-program"
 [L [record sa na aa ba;record sb nb ab bb;record sc nc ac bc]] =
 Returned (L [Symbol "letrec";
   append_values
    (match elements (lift SealedCapture.helper_template) with Some xs => xs | _ => [] end)
    (L [native_binding na aa ba;native_binding nb ab bb;native_binding nc ac bc]);
   Symbol "kl:buri.wire"]).
Proof. intros; eapply run_invoke; apply constructor_program_correct. Qed.
Theorem constructor_machine_request : forall program,
 exists steps, NativeRuntime.invoke steps constructor_program "kl:buri.sealed-request" [program] =
 Returned (L [Symbol "eval";L [Symbol "quote";program];
  L [Symbol "environment";L [Symbol "quote";
    Pair (Symbol "only") (Pair (L [Symbol "chezscheme"]) (lift SealedCapture.imports))]]]).
Proof. intros; eapply run_invoke; apply constructor_request. Qed.
Theorem constructor_machine_rejects_missing : exists steps,
 NativeRuntime.invoke steps constructor_program "kl:buri.sealed-program" [Nil] =
 Raised (Symbol "buri.sealed-targets") (Text "Sealed encoder requires exactly three observed pairs").
Proof. eapply run_result_invoke; [apply constructor_rejects_missing|discriminate]. Qed.
Theorem constructor_machine_rejects_bad_definition : exists steps,
 NativeRuntime.invoke steps constructor_program "kl:buri.sealed-definition" [Nil] =
 Raised (Symbol "buri.sealed-definition") (Text "Sealed encoder requires a procedure definition").
Proof. eapply run_result_invoke; [apply constructor_rejects_bad_definition|discriminate]. Qed.
