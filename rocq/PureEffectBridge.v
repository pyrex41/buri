(* Exact erasure of the effect evaluator to the existing pure evaluator. *)
From Coq Require Import List String Arith Lia.
From Buri Require Import Native NativeSimulation ObserverEffects EffectContract CallRefinement.
Import ListNotations.
Module PureEffectBridge.
Import Native.Native ObserverEffects.ObserverEffects.
Module E := EffectContract.EffectContract.
Module N := NativeSimulation.NativeSimulation.
Definition operation name vs := return_result (external name vs).
Lemma pure_bind : forall r k st,
 bind (return_result r) k st = match r with Returned v=>k v st|_=>Out r st [] end.
Proof.
 intros; destruct r; try reflexivity.
 change (bind (ret v) k st = k v st); apply CallRefinement.bind_return.
Qed.
Local Opaque bind.
Lemma many_erases : forall fuel p rho,
 (forall e st, eval_with fuel p operation rho e st = Out (Native.eval fuel p rho e) st []) ->
 forall es k st, E.many fuel p operation rho es k st =
 match N.many fuel p rho es with Values vs=>k vs st|ArgumentFailure r=>Out r st [] end.
Proof.
 intros fuel p rho IH es; induction es as [|a es IHas]; intros k st; [reflexivity|].
 cbn [E.many N.many]. rewrite E.bind_result,IH.
 destruct (Native.eval fuel p rho a) eqn:A; try reflexivity.
 cbn [answer records trace]. rewrite IHas.
 destruct (N.many fuel p rho es); [destruct (k (v::vs) st)|]; reflexivity.
Qed.
Theorem pure_erasure : forall fuel p rho e st,
 eval_with fuel p operation rho e st = Out (Native.eval fuel p rho e) st [].
Proof.
 induction fuel as [|fuel IH]; intros p rho e st; [reflexivity|].
 destruct e; cbn [eval_with Native.eval]; try reflexivity.
 - destruct (rho s); reflexivity.
 - rewrite E.bind_result,IH. destruct (Native.eval fuel p rho e1); try reflexivity.
   cbn [answer records trace]. destruct v; try (rewrite IH; reflexivity).
   destruct b; rewrite IH; reflexivity.
 - rewrite E.bind_result,IH. destruct (Native.eval fuel p rho e1); try reflexivity.
   cbn [answer records trace]. rewrite IH; reflexivity.
 - rewrite E.bind_result,IH. destruct (Native.eval fuel p rho e1); try reflexivity.
   cbn [answer records trace]. destruct v; try (rewrite IH; reflexivity).
   destruct b; [rewrite IH;reflexivity|reflexivity].
 - rewrite E.bind_result,IH. destruct (Native.eval fuel p rho e1); try reflexivity.
   cbn [answer records trace]. destruct v; try reflexivity.
   destruct b; [reflexivity|rewrite IH;reflexivity].
 - match goal with |- _ = ?rhs => change (E.many fuel p operation rho args (E.apply fuel p operation s) st = rhs) end.
   fold (N.many fuel p rho args).
   rewrite many_erases by (intros;apply IH).
   destruct (N.many fuel p rho args); [|reflexivity].
   unfold E.apply; destruct (p s); [destruct (Nat.eqb _ _)|]; try reflexivity.
   apply IH.
Qed.
Theorem result_monotone : forall n p rho e r,
 Native.eval n p rho e = r -> r <> Exhausted -> forall m, n<=m -> Native.eval m p rho e = r.
Proof.
 intros n p rho e r H N m LE.
 assert (eval_with n p operation rho e Nil = Out r Nil []) as E by (rewrite pure_erasure,H;reflexivity).
 pose proof (E.eval_completed_monotone n p operation rho e Nil (Out r Nil []) E N m LE) as M.
 rewrite pure_erasure in M; inversion M; reflexivity.
Qed.
End PureEffectBridge.
