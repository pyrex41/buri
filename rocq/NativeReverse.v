(* Reverse result correspondence for the existing first-order instruction
   machine. Machine fuel and evaluator depth are existentially related. *)
From Coq Require Import List String Arith Lia.
From Buri Require Import Native NativeRuntime NativeSimulation PureEffectBridge.
Import ListNotations.
Module NativeReverse.
Import Native.Native NativeRuntime.NativeRuntime.
Module N := NativeSimulation.NativeSimulation.
Open Scope list_scope.
Definition apply_result fuel p name vs := match p name with
 | Some d=>if Nat.eqb (List.length (params d)) (List.length vs)
 then eval fuel p (arguments (params d) vs) (body d) else Unsupported
 | None=>external name vs end.
Fixpoint finish fuel p k r := match r with
 | Returned v=>match k with
   | []=>Returned v
   | Choose rho a b::k=>finish fuel p k (eval fuel p rho (match v with Boolean false=>b|_=>a end))
   | Bind rho name body::k=>finish fuel p k (eval fuel p (bind rho name v) body)
   | Conjoin rho b::k=>finish fuel p k (match v with Boolean false=>Returned v|_=>eval fuel p rho b end)
   | Disjoin rho b::k=>finish fuel p k (match v with Boolean false=>eval fuel p rho b|_=>Returned v end)
   | Arguments rho name rest acc::k=>match N.many fuel p rho rest with
     | Values vs=>finish fuel p k (apply_result fuel p name (rev (v::acc)++vs))
     | ArgumentFailure r=>r end
   end
 | _=>r end.
Definition meaning fuel p m := match m with
 | (Enter rho e,k)=>finish fuel p k (eval fuel p rho e)
 | (Deliver v,k)=>finish fuel p k (Returned v)
 | (Fault (Returned _),_)=>Unsupported
 | (Fault r,_)=>r end.
Lemma finish_exhausted : forall fuel p k, finish fuel p k Exhausted=Exhausted.
Proof. destruct k; reflexivity. Qed.
Lemma many_monotone : forall es n m p rho r,
 n<=m -> N.many n p rho es=r -> r<>ArgumentFailure Exhausted -> N.many m p rho es=r.
Proof.
 induction es as [|a es IH]; intros n m p rho r LE E C; [exact E|].
 cbn [N.many] in E |- *. destruct (eval n p rho a) eqn:A.
 - rewrite (PureEffectBridge.result_monotone _ _ _ _ _ A) by (discriminate || exact LE).
   destruct (N.many n p rho es) eqn:B; inversion E; subst.
   + rewrite (IH _ _ _ _ _ LE B) by discriminate; reflexivity.
   + rewrite (IH _ _ _ _ _ LE B) by exact C; reflexivity.
 - rewrite (PureEffectBridge.result_monotone _ _ _ _ _ A) by (discriminate || exact LE); exact E.
 - contradiction C; exact (eq_sym E).
 - rewrite (PureEffectBridge.result_monotone _ _ _ _ _ A) by (discriminate || exact LE); exact E.
Qed.
Lemma apply_monotone : forall n m p name vs r,
 n<=m -> apply_result n p name vs=r -> r<>Exhausted -> apply_result m p name vs=r.
Proof.
 intros; unfold apply_result in *; destruct (p name); [destruct (Nat.eqb _ _)|]; try assumption.
 eapply PureEffectBridge.result_monotone; eauto.
Qed.
Lemma finish_input_complete : forall fuel p k r out,
 finish fuel p k r=out -> out<>Exhausted -> r<>Exhausted.
Proof. intros; intro E; subst r; rewrite finish_exhausted in H; congruence. Qed.
Theorem finish_monotone : forall k n m p r out,
 n<=m -> finish n p k r=out -> out<>Exhausted -> finish m p k r=out.
Proof.
 induction k as [|f k IH]; intros n m p r out LE E C; destruct r; try exact E.
 destruct f; cbn [finish] in E |- *.
 - remember (eval n p rho (match v with Boolean false=>b|_=>a end)) as r eqn:R.
   assert (r<>Exhausted) as NR by (eapply finish_input_complete; eauto).
   rewrite (PureEffectBridge.result_monotone _ _ _ _ _ (eq_sym R) NR m LE).
   eapply IH; eauto.
 - remember (eval n p (bind rho name v) body0) as r eqn:R.
   assert (r<>Exhausted) as NR by (eapply finish_input_complete; eauto).
   rewrite (PureEffectBridge.result_monotone _ _ _ _ _ (eq_sym R) NR m LE).
   eapply IH; eauto.
 - destruct v; try (remember (eval n p rho b) as r eqn:R;
     assert (r<>Exhausted) as NR by (eapply finish_input_complete; eauto);
     rewrite (PureEffectBridge.result_monotone _ _ _ _ _ (eq_sym R) NR m LE); eapply IH; eauto).
   destruct b0; [|eapply IH; eauto].
   remember (eval n p rho b) as r eqn:R.
   assert (r<>Exhausted) as NR by (eapply finish_input_complete; eauto).
   rewrite (PureEffectBridge.result_monotone _ _ _ _ _ (eq_sym R) NR m LE); eapply IH; eauto.
 - destruct v; try (eapply IH; eauto).
   destruct b0; [eapply IH; eauto|].
   remember (eval n p rho b) as r eqn:R.
   assert (r<>Exhausted) as NR by (eapply finish_input_complete; eauto).
   rewrite (PureEffectBridge.result_monotone _ _ _ _ _ (eq_sym R) NR m LE); eapply IH; eauto.
 - destruct (N.many n p rho remaining) eqn:A.
   + rewrite (many_monotone remaining n m p rho _ LE A) by discriminate.
     remember (apply_result n p name (rev (v::reversed)++vs)) as r eqn:R.
     assert (r<>Exhausted) as NR by (eapply finish_input_complete; eauto).
     rewrite (apply_monotone _ _ _ _ _ _ LE (eq_sym R) NR); eapply IH; eauto.
   + rewrite (many_monotone remaining n m p rho _ LE A) by congruence; exact E.
Qed.
Lemma apply_meaning : forall fuel p name vs k,
 meaning fuel p (NativeRuntime.apply p name vs k) = finish fuel p k (apply_result fuel p name vs).
Proof.
 intros fuel p name vs k; destruct k as [|f k];
 unfold NativeRuntime.apply,apply_result; destruct (p name); try (destruct (Nat.eqb _ _)); try reflexivity;
 destruct (external name vs); reflexivity.
Qed.
Lemma enter_step_meaning : forall fuel p rho e k next,
 step p (Enter rho e,k)=Some next ->
 meaning fuel p next=finish fuel p k (eval (S fuel) p rho e).
Proof.
 intros fuel p rho e k next E; destruct e.
 all: try (cbn [step] in E; inversion E; subst; clear E; cbn [meaning eval finish]; try reflexivity).
 - destruct (rho s); try reflexivity; destruct k; reflexivity.
 - destruct (eval fuel p rho e1).
   + destruct v; try reflexivity; destruct b; reflexivity.
   + destruct k; reflexivity.
   + destruct k; reflexivity.
   + destruct k; reflexivity.
 - destruct (eval fuel p rho e1); try reflexivity; destruct k; reflexivity.
 - destruct (eval fuel p rho e1).
   + destruct v; try reflexivity; destruct b; reflexivity.
   + destruct k; reflexivity.
   + destruct k; reflexivity.
   + destruct k; reflexivity.
 - destruct (eval fuel p rho e1).
   + destruct v; try reflexivity; destruct b; reflexivity.
   + destruct k; reflexivity.
   + destruct k; reflexivity.
   + destruct k; reflexivity.
 - destruct args as [|a args]; inversion H0; subst; clear H0.
   + apply apply_meaning.
   + cbn [meaning finish].
     change (finish fuel p (Arguments rho s args []::k) (eval fuel p rho a) =
     finish fuel p k (match N.many fuel p rho (a::args) with
       | Values vs=>apply_result fuel p s vs|ArgumentFailure r=>r end)).
     cbn [N.many]. destruct (eval fuel p rho a); cbn [finish];
     try (destruct k; reflexivity).
     destruct (N.many fuel p rho args) eqn:M; [reflexivity|].
     destruct r; try (destruct k;reflexivity).
     exfalso; eapply N.many_no_returned_failure; exact M.
Qed.
Lemma arguments_step_meaning : forall fuel p rho name remaining acc k v,
 meaning fuel p (Deliver v,Arguments rho name remaining acc::k) =
 meaning fuel p (match remaining with
 | []=>NativeRuntime.apply p name (rev (v::acc)) k
 | a::rest=>(Enter rho a,Arguments rho name rest (v::acc)::k) end).
Proof.
 intros; destruct remaining as [|a rest].
 - rewrite apply_meaning. cbn [meaning finish N.many]. rewrite app_nil_r; reflexivity.
 - cbn [meaning finish N.many]. destruct (eval fuel p rho a); try reflexivity.
   destruct (N.many fuel p rho rest); try reflexivity.
   replace (rev (v0::v::acc)++vs) with (rev (v::acc)++v0::vs).
   + reflexivity.
   + cbn [rev]; repeat rewrite <-app_assoc; reflexivity.
Qed.
Lemma deliver_step_meaning : forall fuel p v k next,
 step p (Deliver v,k)=Some next -> meaning fuel p (Deliver v,k)=meaning fuel p next.
Proof.
 intros fuel p v k next E; destruct k as [|f k]; [discriminate|].
 destruct f; try (cbn [step] in E; inversion E; subst; clear E; reflexivity).
 - destruct v; try (inversion E; reflexivity); destruct b0; inversion E; reflexivity.
 - destruct v; try (inversion E; reflexivity); destruct b0; inversion E; reflexivity.
 - cbn [step] in E; inversion E; subst; clear E; destruct remaining as [|a rest]; inversion H0; subst; apply arguments_step_meaning.
Qed.
Theorem step_backward_complete : forall n p start next r,
 step p start=Some next -> meaning n p next=r -> r<>Exhausted ->
 exists m, meaning m p start=r.
Proof.
 intros n p [c k] next r S E C; destruct c.
 - exists (Datatypes.S n). unfold meaning.
   eapply finish_monotone with (n:=n); [lia| |exact C].
   rewrite <- (enter_step_meaning n p rho e k next S); exact E.
 - exists n; rewrite (deliver_step_meaning n p v k next S); exact E.
 - discriminate.
Qed.
Lemma enter_has_step : forall p rho e k, exists next, step p (Enter rho e,k)=Some next.
Proof. intros; destruct e; try (eexists;reflexivity); destruct args; eexists;reflexivity. Qed.
Lemma deliver_has_step : forall p v f k, exists next, step p (Deliver v,f::k)=Some next.
Proof. intros; destruct f; try (eexists;reflexivity); destruct remaining; eexists;reflexivity. Qed.
Theorem execution_has_evaluator_meaning : forall steps p start r,
 execute steps p start=r -> r<>Exhausted -> exists fuel, meaning fuel p start=r.
Proof.
 induction steps as [|steps IH]; intros p [c k] r E C.
 - destruct c as [rho e|v|bad].
   + cbn [execute] in E; subst; contradiction C; reflexivity.
   + destruct k; cbn [execute] in E.
     * subst; exists 0; reflexivity.
     * subst; contradiction C; reflexivity.
   + destruct bad; cbn [execute] in E; subst; try (exists 0;reflexivity); contradiction C;reflexivity.
 - destruct c as [rho e|v|bad].
   + destruct (enter_has_step p rho e k) as [next S]. cbn [execute] in E; rewrite S in E.
     destruct (IH p next r E C) as [fuel M]; eapply step_backward_complete; eauto.
   + destruct k as [|f k]; [cbn [execute] in E;subst;exists 0;reflexivity|].
     destruct (deliver_has_step p v f k) as [next S]. cbn [execute] in E; rewrite S in E.
     destruct (IH p next r E C) as [fuel M]; eapply step_backward_complete; eauto.
   + destruct bad; cbn [execute] in E; subst; try (exists 0;reflexivity); contradiction C;reflexivity.
Qed.
Theorem machine_result_has_evaluation : forall steps p rho e r,
 execute steps p (Enter rho e,[])=r -> r<>Exhausted ->
 exists fuel, eval fuel p rho e=r.
Proof.
 intros; destruct (execution_has_evaluator_meaning _ _ _ _ H H0) as [fuel E].
 exists fuel. unfold meaning in E. destruct (eval fuel p rho e); exact E.
Qed.
Theorem evaluator_machine_equivalence : forall p rho e r,
 r<>Exhausted ->
 ((exists fuel, eval fuel p rho e=r) <-> (exists steps, execute steps p (Enter rho e,[])=r)).
Proof.
 intros; split; intros [n E].
 - eapply N.eval_result_execute; eauto.
 - eapply machine_result_has_evaluation; eauto.
Qed.
Definition eval_diverges p rho e := forall fuel, eval fuel p rho e=Exhausted.
Definition machine_diverges p rho e := forall steps, execute steps p (Enter rho e,[])=Exhausted.
Theorem divergence_equivalence : forall p rho e,
 eval_diverges p rho e <-> machine_diverges p rho e.
Proof.
 intros p rho e; unfold eval_diverges,machine_diverges; split; intros D n.
 - destruct (execute n p (Enter rho e,[])) eqn:E; try reflexivity;
   exfalso; destruct (machine_result_has_evaluation n p rho e _ E ltac:(discriminate)) as [fuel F];
   rewrite D in F; discriminate.
 - destruct (eval n p rho e) eqn:E; try reflexivity;
   exfalso; destruct (N.eval_result_execute n p rho e _ E ltac:(discriminate)) as [steps F];
   rewrite D in F; discriminate.
Qed.
End NativeReverse.
