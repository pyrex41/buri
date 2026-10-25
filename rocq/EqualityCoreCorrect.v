(* The actual compiled Shen axiom-free congruence derivation implements
   Equality.check [] for all typed certificates, not just ground examples. *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Equality Native NativeHelpers NativeComposition NativeSimulation NativeRuntime EqualityCoreInput.
Import ListNotations.
Module EqualityCoreCorrect.
Import Native.Native NativeComposition.NativeComposition.
Open Scope string_scope.
Definition helpers := filter (fun d=>String.eqb (fst d) "kl:=") NativeHelpers.helpers.
Definition program := (equality_core_program++helpers)%list.
Definition P := lookup program.
Fixpoint term (t:Equality.term) := match t with
 | Equality.Var n=>L [Symbol "var";Integer (Z.of_nat n)]
 | Equality.Const n=>L [Symbol "const";Integer (Z.of_nat n)]
 | Equality.App a b=>L [Symbol "app";term a;term b] end.
Fixpoint certificate (c:Equality.certificate) := match c with
 | Equality.Refl a=>L [Symbol "refl";term a]
 | Equality.Sym p=>L [Symbol "sym";certificate p]
 | Equality.Trans p q=>L [Symbol "trans";certificate p;certificate q]
 | Equality.Cong p q=>L [Symbol "cong";certificate p;certificate q]
 | Equality.Instance n sigma=>L [Symbol "instance";Integer (Z.of_nat n);L (map term sigma)] end.
Definition result_value r := match r with
 | Some (a,b)=>L [Symbol "some";L [term a;term b]] | None=>Symbol "none" end.
Definition flip (r:option (Equality.term*Equality.term)) := match r with Some (a,b)=>Some (b,a)|None=>None end.
Definition join (r s:option (Equality.term*Equality.term)) := match r,s with
 | Some (a,b),Some (c,d)=>if term_eq_dec b c then Some (a,d) else None | _,_=>None end.
Definition congruence (r s:option (Equality.term*Equality.term)) := match r,s with
 | Some (a,b),Some (c,d)=>Some (Equality.App a c,Equality.App b d) | _,_=>None end.
Lemma same_term_iff : forall a b, same (term a) (term b)=true <-> a=b.
Proof.
 induction a; destruct b; cbn [term L fold_right same String.eqb Ascii.eqb Bool.eqb andb];
 try (split; intro H; discriminate).
 - rewrite Bool.andb_true_r,Z.eqb_eq. split; intro H; [f_equal;lia|inversion H;reflexivity].
 - rewrite Bool.andb_true_r,Z.eqb_eq. split; intro H; [f_equal;lia|inversion H;reflexivity].
 - repeat rewrite Bool.andb_true_r. rewrite Bool.andb_true_iff,IHa1,IHa2.
   split; [intros [A B];subst;reflexivity|intro H;inversion H;auto].
Qed.
Lemma same_term_decision : forall a b, same (term a) (term b)=if term_eq_dec a b then true else false.
Proof.
 intros a b; destruct (term_eq_dec a b) as [E|N].
 - apply same_term_iff; exact E.
 - destruct (same (term a) (term b)) eqn:E; [apply same_term_iff in E;contradiction|reflexivity].
Qed.
Ltac start_run := unfold runs; eexists; split; [reflexivity|]; split; [reflexivity|].
Ltac small := unfold executes; exists 20; reflexivity.
Theorem captured_sym : forall r,
 runs P "kl:buri.eq2-sym" [result_value r] (result_value (flip r)).
Proof. intros [[a b]|]; start_run; exists 30; reflexivity. Qed.
Theorem captured_congruence : forall r s,
 runs P "kl:buri.eq2-cong" [result_value r;result_value s] (result_value (congruence r s)).
Proof. intros [[a b]|] [[c d]|]; start_run; exists 40; reflexivity. Qed.
Theorem captured_transitivity : forall r s,
 runs P "kl:buri.eq2-trans" [result_value r;result_value s] (result_value (join r s)).
Proof.
 intros [[a b]|] [[c d]|]; start_run; try (exists 40;reflexivity).
 exists 40.
 change ((if same (term b) (term c) then Returned (result_value (Some (a,d))) else Returned (Symbol "none")) =
 Returned (result_value (join (Some (a,b)) (Some (c,d))))).
 rewrite same_term_decision; unfold join; destruct (term_eq_dec b c); reflexivity.
Qed.
Theorem captured_checker : forall p,
 runs P "kl:buri.eq2-derive" [certificate p] (result_value (check [] p)).
Proof.
 induction p; start_run.
 - small.
 - eapply branch with (flag:=false); [small|].
   eapply branch with (flag:=true); [small|].
   eapply call with (vs:=[result_value (check [] p)]).
   + constructor; [|constructor]. eapply call with (vs:=[certificate p]); [constructor;[small|constructor]|exact IHp].
   + apply captured_sym.
 - do 2 (eapply branch with (flag:=false); [small|]).
   eapply branch with (flag:=true); [small|].
   eapply binding with (x:=result_value (check [] p1)).
   + eapply call with (vs:=[certificate p1]); [constructor;[small|constructor]|exact IHp1].
   + eapply call with (vs:=[result_value (check [] p1);result_value (check [] p2)]).
     * constructor; [small|constructor;[|constructor]].
       eapply call with (vs:=[certificate p2]); [constructor;[small|constructor]|exact IHp2].
     * apply captured_transitivity.
 - do 3 (eapply branch with (flag:=false); [small|]).
   eapply branch with (flag:=true); [small|].
   eapply binding with (x:=result_value (check [] p1)).
   + eapply call with (vs:=[certificate p1]); [constructor;[small|constructor]|exact IHp1].
   + eapply call with (vs:=[result_value (check [] p1);result_value (check [] p2)]).
     * constructor; [small|constructor;[|constructor]].
       eapply call with (vs:=[certificate p2]); [constructor;[small|constructor]|exact IHp2].
     * apply captured_congruence.
 - destruct n; small.
Qed.
Theorem checker_machine : forall p, exists steps,
 NativeRuntime.invoke steps program "kl:buri.eq2-derive" [certificate p] = Returned (result_value (check [] p)).
Proof.
 intro p; destruct (runs_run _ _ _ _ (captured_checker p)) as [fuel E].
 eapply NativeSimulation.run_invoke; exact E.
Qed.
Lemma term_injective : forall a b, term a=term b -> a=b.
Proof. intros; apply same_term_iff; rewrite H; apply same_term_iff; reflexivity. Qed.
Lemma result_injective : forall r a b,
 result_value r=result_value (Some (a,b)) -> r=Some (a,b).
Proof.
 intros [[c d]|] a b H; [|discriminate]. cbn [result_value L fold_right] in H.
 injection H as A B. apply term_injective in A,B; subst; reflexivity.
Qed.
Theorem machine_acceptance_matches_checker : forall steps p a b,
 NativeRuntime.invoke steps program "kl:buri.eq2-derive" [certificate p] = Returned (result_value (Some (a,b))) ->
 check [] p=Some (a,b).
Proof.
 intros steps p a b H; destruct (checker_machine p) as [n C].
 unfold NativeRuntime.invoke in H,C.
 destruct (lookup program "kl:buri.eq2-derive") as [d|] eqn:D; [|discriminate].
 destruct (Nat.eqb _ _) eqn:AR; [|discriminate].
 apply NativeRuntime.execute_trace in H,C.
 assert ((NativeRuntime.Deliver (result_value (check [] p)),([]:list NativeRuntime.frame)) =
 (NativeRuntime.Deliver (result_value (Some (a,b))),([]:list NativeRuntime.frame))) as E.
 { eapply NativeRuntime.terminal_unique; eauto; reflexivity. }
 inversion E. apply result_injective; assumption.
Qed.
Theorem actual_checker_sound : forall (D:Type) (constants:nat->D) (application:D->D->D) steps p a b,
 NativeRuntime.invoke steps program "kl:buri.eq2-derive" [certificate p] = Returned (result_value (Some (a,b))) ->
 forall rho, @denote D constants application rho a=@denote D constants application rho b.
Proof.
 intros D constants application steps p a b H.
 eapply (@check_sound_under_rules D constants application []); [intros x y I;inversion I|].
 eapply machine_acceptance_matches_checker; exact H.
Qed.
Fixpoint references e : list string := match e with
 | Lit _ | Var _=>[] | If c a b=>references c++references a++references b
 | Let _ a b | And a b | Or a b=>references a++references b
 | Call name args=>name::flat_map references args end.
Definition allowed_calls := ["pair?";"eq?";"car";"cdr";"null?";"list";"cons";
 "kl:buri.eq2-derive";"kl:buri.eq2-sym";"kl:buri.eq2-trans";"kl:buri.eq2-cong";"kl:="].
Definition actual_references := Eval vm_compute in flat_map (fun d=>references (body (snd d))) equality_core_program.
Theorem captured_dependency_closure : forallb
 (fun name=>existsb (String.eqb name) allowed_calls) actual_references=true.
Proof. vm_compute;reflexivity. Qed.
End EqualityCoreCorrect.
