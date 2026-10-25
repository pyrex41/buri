(* Exact captured read-back checking wrapper. A write may lie, be hushed, or
   partially mutate its world. Success is checked against a truthful read. *)
From Coq Require Import List String Bool.
From Buri Require Import Native NativeHelpers ObserverEffects CheckedIOInput.
Import ListNotations.
Module CheckedFileIO.
Import Native.Native ObserverEffects.ObserverEffects.
Open Scope string_scope.
Definition program := (checked_io_program ++ NativeHelpers.helpers)%list.
Definition P := lookup program.
Fixpoint file_lookup path files := match files with
 | Pair (Pair (Text name) (Text contents)) rest =>
   if String.eqb path name then Some contents else file_lookup path rest
 | _ => None end.
Definition writer := string -> string -> value -> (result * value).
Definition operation (write:writer) op vs : computation := fun files =>
 match op,vs with
 | "kl:write-to-file",[Text path;Text requested] =>
   let '(r,updated):=write path requested files in
   Out r updated [WriteFile (Text path) (Text requested) r]
 | "kl:read-file-as-string",[Text path] => match file_lookup path files with
   | Some actual => Out (Returned (Text actual)) files [ReadFile (Text path) (Text actual)]
   | None => Out Unsupported files [ReadFile (Text path) Nil] end
 | _,_ => Out (external op vs) files [] end.
Definition invoke fuel write path text files := match lookup program "kl:buri.checked-write" with
 | Some d => eval_with fuel P (operation write) (arguments (params d) [Text path;Text text]) (body d) files
 | None => Out Unsupported files [] end.
Definition mismatch := Raised (Symbol "buri.checked-write") (Text "Snapshot write verification failed").
Definition expected path requested r updated := match r with
 | Returned _ => match file_lookup path updated with
   | Some actual => Out (if String.eqb actual requested then Returned (Text requested) else mismatch)
     updated [WriteFile (Text path) (Text requested) r;ReadFile (Text path) (Text actual)]
   | None => Out Unsupported updated [WriteFile (Text path) (Text requested) r;ReadFile (Text path) Nil] end
 | _ => Out r updated [WriteFile (Text path) (Text requested) r] end.
Definition initial path text := arguments ["V5984";"V5985"] [Text path;Text text].
Definition write_expr := Call "kl:write-to-file" [Var "V5984";Var "V5985"].
Definition read_expr := Call "kl:read-file-as-string" [Var "V5984"].
Lemma write_stage : forall n write path text previous,
 eval_with (S (S n)) P (operation write) (initial path text) write_expr previous =
 match write path text previous with (r,updated)=>Out r updated [WriteFile (Text path) (Text text) r] end.
Proof. intros; vm_compute; destruct (write path text previous); reflexivity. Qed.
Lemma read_stage : forall n write path text written previous,
 eval_with (S (S n)) P (operation write) (Native.bind (initial path text) "W5986" written) read_expr previous =
 match file_lookup path previous with
 | Some actual=>Out (Returned (Text actual)) previous [ReadFile (Text path) (Text actual)]
 | None=>Out Unsupported previous [ReadFile (Text path) Nil] end.
Proof. intros; destruct (file_lookup path previous) eqn:R; vm_compute in R; vm_compute; rewrite R; reflexivity. Qed.
Lemma let_step : forall n p operation rho name a b previous,
 eval_with (S n) p operation rho (Let name a b) previous =
 let o:=eval_with n p operation rho a previous in
 match answer o with
 | Returned v=>let next:=eval_with n p operation (Native.bind rho name v) b (records o) in
   Out (answer next) (records next) (trace o ++ trace next)
 | _=>o end.
Proof. reflexivity. Qed.
Lemma guard_stage : forall n write path text written actual previous,
 eval_with (S (S (S n))) P (operation write)
 (Native.bind (Native.bind (initial path text) "W5986" written) "W5987" (Text actual))
 (Call "kl:=" [Var "W5987";Var "V5985"]) previous =
 Out (Returned (Boolean (String.eqb actual text))) previous [].
Proof. intros; vm_compute; reflexivity. Qed.
Lemma if_step : forall n p operation rho c a b previous,
 eval_with (S n) p operation rho (If c a b) previous =
 let o:=eval_with n p operation rho c previous in
 match answer o with
 | Returned v=>let next:=eval_with n p operation rho (match v with Boolean false=>b|_=>a end) (records o) in
   Out (answer next) (records next) (trace o ++ trace next)
 | _=>o end.
Proof. reflexivity. Qed.
Theorem captured_checked_write : forall write path requested previous r updated,
 write path requested previous = (r,updated) ->
 invoke 6 write path requested previous = expected path requested r updated.
Proof.
 intros write path requested previous r updated W.
 match goal with |- _ = ?rhs => change (eval_with 6 P (operation write) (initial path requested)
   (Let "W5986" write_expr (Let "W5987" read_expr
      (If (Call "kl:=" [Var "W5987";Var "V5985"]) (Var "V5985")
        (Call "error" [Lit (Symbol "buri.checked-write");Lit (Text "Snapshot write verification failed")])))) previous = rhs) end.
 rewrite let_step,write_stage,W. destruct r; cbn [answer records trace expected]; try reflexivity.
 rewrite let_step,read_stage.
 destruct (file_lookup path updated) as [actual|] eqn:R;
   cbn [answer records trace]; [|reflexivity].
 rewrite if_step,guard_stage. cbn [answer records trace].
 destruct (String.eqb actual requested); reflexivity.
Qed.
Theorem successful_write_is_observed : forall write path text previous v,
 answer (invoke 6 write path text previous) = Returned v ->
 v = Text text /\ file_lookup path (records (invoke 6 write path text previous)) = Some text.
Proof.
 intros write path text previous v H.
 destruct (write path text previous) as [r updated] eqn:W.
 rewrite captured_checked_write with (r:=r) (updated:=updated) in * by exact W.
 destruct r; cbn [expected answer records] in *; try discriminate.
 destruct (file_lookup path updated) as [actual|] eqn:R; try discriminate.
 destruct (String.eqb actual text) eqn:E; try discriminate.
 apply String.eqb_eq in E; subst actual; inversion H; subst; split; auto.
Qed.
Theorem corrupt_write_rejected : forall write path text previous written updated actual,
 write path text previous = (Returned written,updated) -> file_lookup path updated = Some actual ->
 actual <> text -> answer (invoke 6 write path text previous) = mismatch.
Proof.
 intros; rewrite captured_checked_write with (r:=Returned written) (updated:=updated) by assumption.
 cbn [expected]; rewrite H0. assert (String.eqb actual text = false) as E by (apply String.eqb_neq; assumption).
 rewrite E; reflexivity.
Qed.
Theorem failed_write_not_read : forall write path text previous r updated,
 write path text previous = (r,updated) -> failed r ->
 invoke 6 write path text previous = Out r updated [WriteFile (Text path) (Text text) r].
Proof.
 intros; rewrite captured_checked_write with (r:=r) (updated:=updated) by assumption.
 destruct r; try contradiction; reflexivity.
Qed.
End CheckedFileIO.
