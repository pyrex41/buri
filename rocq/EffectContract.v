(* General first-order effect contract: immutable lexical environments,
   arbitrary external operations, explicit outcomes and left-to-right traces. *)
From Coq Require Import List String Arith Lia.
From Buri Require Import Native ObserverEffects.
Import ListNotations.
Module EffectContract.
Import Native.Native ObserverEffects.ObserverEffects.
Open Scope list_scope.
Definition many fuel p op rho := fix go es (k:list value->computation) := match es with
 | []=>k []
 | a::rest=>bind (eval_with fuel p op rho a) (fun v=>go rest (fun vs=>k (v::vs))) end.
Definition apply fuel p op name vs := match p name with
 | Some d=>if Nat.eqb (List.length (params d)) (List.length vs)
 then eval_with fuel p op (arguments (params d) vs) (body d) else return_result Unsupported
 | None=>op name vs end.
Lemma call_step : forall fuel p op rho name es state,
 eval_with (S fuel) p op rho (Call name es) state = many fuel p op rho es (apply fuel p op name) state.
Proof. reflexivity. Qed.
Definition completed o := answer o <> Exhausted.
Lemma bind_result : forall m k state,
 bind m k state = match m state with
 | Out (Returned v) updated events=>let o:=k v updated in Out (answer o) (records o) (events++trace o)
 | o=>o end.
Proof. intros; unfold bind; destruct (m state) as [r st es]; destruct r; reflexivity. Qed.
Definition approximates (a b:computation) := forall state o,
 a state = o -> completed o -> b state = o.
Lemma approximates_refl : forall a, approximates a a.
Proof. unfold approximates; auto. Qed.
Lemma bind_approximates : forall a a' k k',
 approximates a a' -> (forall v, approximates (k v) (k' v)) ->
 approximates (bind a k) (bind a' k').
Proof.
 intros a a' k k' A K state out E C.
 rewrite bind_result in E |- *.
 destruct (a state) as [r st es] eqn:R; destruct r.
 - assert (a' state = Out (Returned v) st es) as R' by
   (apply A; [exact R|unfold completed; discriminate]).
   rewrite R'. destruct (k v st) as [r st' es'] eqn:N.
   cbn [answer records trace] in E.
   assert (completed (Out r st' es')) as CN by (unfold completed in *; subst out; exact C).
   rewrite (K v st _ N CN); exact E.
 - rewrite (A state _ R) by (unfold completed; discriminate); exact E.
 - subst out; contradiction C; reflexivity.
 - rewrite (A state _ R) by (unfold completed; discriminate); exact E.
Qed.
Lemma many_approximates : forall n m p op rho,
 (forall e, approximates (eval_with n p op rho e) (eval_with m p op rho e)) ->
 forall es k k', (forall vs, approximates (k vs) (k' vs)) ->
 approximates (many n p op rho es k) (many m p op rho es k').
Proof.
 intros n m p op rho R es; induction es; intros k k' K; cbn [many].
 - apply K.
 - apply bind_approximates; [apply R|]. intros; apply IHes; intros; apply K.
Qed.
Theorem eval_completed_monotone : forall n p op rho e state o,
 eval_with n p op rho e state = o -> completed o ->
 forall m, n<=m -> eval_with m p op rho e state = o.
Proof.
 intro n; induction n as [|n IH]; intros p op rho e state out E C m LE.
 - subst out; contradiction C; reflexivity.
 - destruct m as [|m]; [lia|].
   assert (R : forall rho e, approximates (eval_with n p op rho e) (eval_with m p op rho e)).
   { intros r e0 st o H N; eapply IH; eauto; lia. }
   assert (S : approximates (eval_with (S n) p op rho e) (eval_with (S m) p op rho e)).
   { destruct e; cbn [eval_with].
     - apply approximates_refl.
     - apply approximates_refl.
     - apply bind_approximates; [apply R|]. intro v; destruct v; try apply R; destruct b; apply R.
     - apply bind_approximates; [apply R|]. intro v; apply R.
     - apply bind_approximates; [apply R|]. intro v; destruct v; try apply R;
       destruct b; [apply R|apply approximates_refl].
     - apply bind_approximates; [apply R|]. intro v; destruct v; try apply approximates_refl;
       destruct b; [apply approximates_refl|apply R].
     - fold (many n p op rho args (apply n p op s)).
       fold (many m p op rho args (apply m p op s)).
       apply many_approximates; [apply R|]. intro vs; unfold apply.
       destruct (p s) as [d|]; [destruct (Nat.eqb _ _)|]; try apply approximates_refl; apply R. }
   exact (S state out E C).
Qed.
Fixpoint variables e : list string := match e with
 | Lit _=>[] | Var s=>[s]
 | If c a b=>variables c ++ variables a ++ variables b
 | Let _ a b | And a b | Or a b=>variables a ++ variables b
 | Call _ es=>flat_map variables es end.
Definition compatible e (rho sigma:env) := forall name,
 In name (variables e) -> rho name = sigma name.
Lemma bind_congruent : forall m m' k k',
 (forall st, m st=m' st) -> (forall v st, k v st=k' v st) ->
 forall st, bind m k st=bind m' k' st.
Proof.
 intros m m' k k' M K st; unfold bind; rewrite M.
 destruct (m' st) as [r updated events]; destruct r; try reflexivity.
 cbn [answer records trace]; rewrite K; reflexivity.
Qed.
Lemma many_congruent : forall fuel p op rho sigma es,
 (forall e, In e es -> forall st, eval_with fuel p op rho e st=eval_with fuel p op sigma e st) ->
 forall k st, many fuel p op rho es k st=many fuel p op sigma es k st.
Proof.
 intros fuel p op rho sigma es; induction es; intros H k st; [reflexivity|].
 cbn [many]; apply bind_congruent.
 - apply H; left; reflexivity.
 - intros; apply IHes; intros; apply H; right; assumption.
Qed.
Theorem environment_congruence : forall fuel p op rho sigma e,
 compatible e rho sigma -> forall st, eval_with fuel p op rho e st=eval_with fuel p op sigma e st.
Proof.
 induction fuel as [|fuel IH]; intros p op rho sigma e H st; [reflexivity|].
 destruct e; cbn [eval_with].
 - reflexivity.
 - rewrite (H s); [reflexivity|left;reflexivity].
 - assert (C1:compatible e1 rho sigma) by (intros x X; apply H; cbn [variables]; apply in_or_app; auto).
   assert (C2:compatible e2 rho sigma) by
     (intros x X; apply H; cbn [variables]; apply in_or_app; right; apply in_or_app; auto).
   assert (C3:compatible e3 rho sigma) by
     (intros x X; apply H; cbn [variables]; apply in_or_app; right; apply in_or_app; auto).
   apply bind_congruent; [apply IH; exact C1|].
   intros v state; destruct v; try exact (IH p op rho sigma e2 C2 state).
   destruct b; [exact (IH p op rho sigma e2 C2 state)|exact (IH p op rho sigma e3 C3 state)].
 - assert (C1:compatible e1 rho sigma) by (intros x X; apply H; cbn [variables]; apply in_or_app; auto).
   assert (C2:compatible e2 rho sigma) by (intros x X; apply H; cbn [variables]; apply in_or_app; auto).
   apply bind_congruent; [apply IH;exact C1|].
   intros v state; apply IH; intros x X; unfold Native.bind.
   destruct (String.eqb x s); [reflexivity|apply C2; exact X].
 - assert (C1:compatible e1 rho sigma) by (intros x X; apply H; cbn [variables]; apply in_or_app; auto).
   assert (C2:compatible e2 rho sigma) by (intros x X; apply H; cbn [variables]; apply in_or_app; auto).
   apply bind_congruent; [apply IH;exact C1|].
   intros v state; destruct v; try exact (IH p op rho sigma e2 C2 state).
   destruct b; [exact (IH p op rho sigma e2 C2 state)|reflexivity].
 - assert (C1:compatible e1 rho sigma) by (intros x X; apply H; cbn [variables]; apply in_or_app; auto).
   assert (C2:compatible e2 rho sigma) by (intros x X; apply H; cbn [variables]; apply in_or_app; auto).
   apply bind_congruent; [apply IH;exact C1|].
   intros v state; destruct v; try reflexivity.
   destruct b; [reflexivity|exact (IH p op rho sigma e2 C2 state)].
 - fold (many fuel p op rho args (apply fuel p op s)).
   fold (many fuel p op sigma args (apply fuel p op s)).
   apply many_congruent; intros e E state; apply IH; intros x X; apply H.
   cbn [variables]. apply in_flat_map; exists e; auto.
Qed.
Theorem fresh_binding_preserves_effects : forall fuel p op rho e name v st,
 ~ In name (variables e) ->
 eval_with fuel p op (Native.bind rho name v) e st = eval_with fuel p op rho e st.
Proof.
 intros; apply environment_congruence; intros x X; unfold Native.bind.
 destruct (String.eqb x name) eqn:E; [|reflexivity].
 apply String.eqb_eq in E; subst; contradiction.
Qed.
End EffectContract.
