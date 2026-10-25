(* Pinned Shen-Scheme read override: discharge path construction/forwarding
   rather than assuming the complete Shen read function is truthful. Chez's
   read-file-as-string and the fixed home-directory lookup remain contracts. *)
From Coq Require Import List String.
From Buri Require Import Native ObserverEffects ObserverPipeline IOReadInput.
Import ListNotations.
Module IOReadCorrect.
Import Native.Native ObserverEffects.ObserverEffects.
Open Scope string_scope.
Definition P := lookup io_read_program.
Definition operation home (read:string->computation) name args : computation :=
 match name,args with
 | "kl:value",[Symbol "*home-directory*"]=>ret (Text home)
 | "read-file-as-string",[Text path]=>read path
 | _,_=>return_result (external name args) end.
Definition rho path := arguments ["V5960"] [Text path].
Definition invoke home read path previous :=
 match P "kl:read-file-as-string" with
 | Some d=>eval_with 4 P (operation home read) (arguments (params d) [Text path]) (body d) previous
 | None=>Out Unsupported previous [] end.
Definition path_expression := Call "string-append" [Call "kl:value" [Lit (Symbol "*home-directory*")];Var "V5960"].
Theorem captured_path_construction : forall home read path previous,
 eval_with 3 P (operation home read) (rho path) path_expression previous =
 Out (Returned (Text (home++path))) previous [].
Proof. reflexivity. Qed.
Theorem captured_read_forwards_exactly : forall home read path previous,
 invoke home read path previous = read (home++path) previous.
Proof.
 intros home read path previous.
 change (eval_with 4 P (operation home read) (rho path)
 (Call "read-file-as-string" [path_expression]) previous = read (home++path) previous).
 rewrite ObserverPipeline.unary_call_step. unfold bind at 1.
 rewrite captured_path_construction. cbn [answer records trace].
 change (let o:=read (home++path) previous in Out (answer o) (records o) (trace o) = read (home++path) previous).
 destruct (read (home++path) previous); reflexivity.
Qed.
Theorem native_read_contract_suffices : forall home read path previous text,
 read (home++path) previous = Out (Returned (Text text)) previous [ReadFile (Text (home++path)) (Text text)] ->
 invoke home read path previous = Out (Returned (Text text)) previous [ReadFile (Text (home++path)) (Text text)].
Proof. intros; rewrite captured_read_forwards_exactly; assumption. Qed.
Theorem native_read_failure_propagates : forall home read path previous failure updated events,
 read (home++path) previous = Out failure updated events ->
 invoke home read path previous = Out failure updated events.
Proof. intros; rewrite captured_read_forwards_exactly; assumption. Qed.
End IOReadCorrect.
