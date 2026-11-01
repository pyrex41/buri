(* E2E-06: well-formed-state preservation. Every location reachable from the
   control, the continuation, the global value namespace and the heap itself is
   allocated. Each step, and each IO step for every environment response,
   preserves this invariant; consequently well-formed runs never reach the
   dangling-location Wrong states. *)
From Coq Require Import List ZArith NArith String Bool Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics.
Import ListNotations.
Module KLWellFormed.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics.

Definition frame_ok (n : nat) (f : frame) : Prop := match f with
 | KLet _ _ rho | KIf _ _ rho | KAnd _ rho | KOr _ rho | KCond _ _ rho
 | KTrap _ rho | KHead _ rho => eok n rho
 | KAndR | KOrR => True
 | KArgs fv done _ rho => vok n fv /\ lok n done /\ eok n rho
 | KCallArgs _ done _ rho => lok n done /\ eok n rho
 | KApply args => lok n args end.
Definition control_ok (n : nat) (c : control) : Prop := match c with
 | Eval rho _ => eok n rho | Ret v => vok n v | _ => True end.
Definition wf (c : config) : Prop :=
 control_ok (List.length (heap (mem c))) (ctl c) /\
 Forall (frame_ok (List.length (heap (mem c)))) (kont c) /\ store_ok (mem c).
Definition move_ok (m : move) : Prop := match m with
 | MTau c => wf c | MIO _ kk => forall r, wf (kk r) | _ => True end.
(* Profiles must not plant locations in fresh vectors. *)
Definition profile_ok (P : profile) := vok 0 (absvector_fill P).

Lemma frame_mono : forall n m f, n <= m -> frame_ok n f -> frame_ok m f.
Proof.
 intros n m f L H; destruct f; cbn in *;
 repeat match goal with H : _ /\ _ |- _ => destruct H end;
 repeat split; eauto using eok_mono, lok_mono, vok_mono.
Qed.
Lemma frames_mono : forall n m k, n <= m -> Forall (frame_ok n) k -> Forall (frame_ok m) k.
Proof. intros; eapply Forall_impl; [|eassumption]; intros; eapply frame_mono; eauto. Qed.
Lemma control_mono : forall n m c, n <= m -> control_ok n c -> control_ok m c.
Proof. intros n m c L H; destruct c; cbn in *; eauto using eok_mono, vok_mono. Qed.

Lemma lok_app : forall n a b, lok n a -> lok n b -> lok n (a ++ b).
Proof. intros; apply Forall_app; auto. Qed.
Lemma lok_rev : forall n a, lok n a -> lok n (rev a).
Proof. intros; apply Forall_rev; auto. Qed.
Lemma lok_firstn : forall n k a, lok n a -> lok n (firstn k a).
Proof. unfold lok; intros n k; induction k; destruct a; cbn; intros H; try constructor; inversion H; auto. Qed.
Lemma lok_skipn : forall n k a, lok n a -> lok n (skipn k a).
Proof. unfold lok; intros n k; induction k; destruct a; cbn; intros H; auto; inversion H; auto. Qed.
Lemma eok_combine : forall n ps vs, lok n vs -> eok n (combine ps vs).
Proof.
 unfold lok, eok; intros n ps; induction ps; destruct vs; cbn; intros H; try constructor; inversion H; subst; auto.
Qed.
Lemma lok_repeat : forall n v k, vok n v -> lok n (repeat v k).
Proof. unfold lok; intros n v k H; induction k; cbn; constructor; auto. Qed.
Lemma lok_replace : forall n i x l, vok n x -> lok n l -> lok n (replace_nth i x l).
Proof.
 unfold lok; intros n i; induction i; intros x l X L; destruct l; cbn; auto; inversion L; subst; constructor; auto.
Qed.
Lemma forall_replace : forall A (Q : A -> Prop) i x l, Q x -> Forall Q l -> Forall Q (replace_nth i x l).
Proof.
 intros A Q i; induction i; intros x l X L; destruct l; cbn; auto; inversion L; subst; constructor; auto.
Qed.
Lemma lok_nth : forall n l i v, lok n l -> nth_error l i = Some v -> vok n v.
Proof. intros n l i v H E; apply nth_error_In in E; eapply Forall_forall in H; eauto. Qed.

Lemma push_ok : forall P f k c s, control_ok (List.length (heap s)) c ->
 frame_ok (List.length (heap s)) f -> Forall (frame_ok (List.length (heap s))) k -> store_ok s ->
 wf (push P f k c s).
Proof.
 intros; unfold push, wf; destruct (stack_limit P); [destruct (Nat.leb _ _)|]; cbn;
 (split; [assumption || exact I|split; [assumption || (constructor; assumption)|assumption]]).
Qed.

Lemma continue_ok : forall P rest k c s, control_ok (List.length (heap s)) c ->
 lok (List.length (heap s)) rest -> Forall (frame_ok (List.length (heap s))) k -> store_ok s ->
 wf (continue_with P rest k c s).
Proof.
 intros; unfold continue_with; destruct rest.
 - unfold wf; cbn; split; [assumption|split; assumption].
 - apply push_ok; auto.
Qed.

Definition pout_ok (s : store) (o : pout) : Prop := match o with
 | ORet v s' => store_ok s' /\ vok (List.length (heap s')) v /\ List.length (heap s) <= List.length (heap s')
 | _ => True end.
Definition presult_ok (s : store) (r : presult) : Prop := match r with
 | PDone o => pout_ok s o | PIO _ kk => forall resp, pout_ok s (kk resp) end.

Lemma pout_config_ok : forall P o rest k s, store_ok s -> pout_ok s o ->
 lok (List.length (heap s)) rest -> Forall (frame_ok (List.length (heap s))) k ->
 wf (pout_config P o rest k s).
Proof.
 intros P o rest k s S O R K; destruct o; cbn in *.
 - destruct O as [S' [V L]]. apply continue_ok; auto.
   + eapply lok_mono; eauto.
   + eapply frames_mono; eauto.
 - unfold wf; cbn; split; [exact I|split; assumption].
 - apply continue_ok; cbn; auto; constructor.
 - unfold wf; cbn; split; [exact I|split; assumption].
 - unfold wf; cbn; split; [exact I|split; assumption].
Qed.

Ltac args_ok := repeat match goal with
 | H : lok _ (_ :: _) |- _ => inversion H; subst; clear H
 | H : Forall (vok _) (_ :: _) |- _ => inversion H; subst; clear H
 | H : vok _ (VCons _ _) |- _ => destruct H end.
Ltac split_all := repeat match goal with
 | |- context [match ?x with _ => _ end] => destruct x eqn:?
 | |- context [if ?b then _ else _] => destruct b eqn:? end.
Ltac rule_tac := intros; split_all; cbn in *; args_ok; cbn in *; repeat split; auto.

Lemma rule_ok : forall P p args s, profile_ok P -> store_ok s -> lok (List.length (heap s)) args ->
 presult_ok s (prim_rule P p args s).
Proof.
 intros P p args s PO S A. destruct S as [H G].
 destruct p; cbn [prim_rule].
 all: try (unfold rule_intern, rule_pos, rule_tlstr, rule_cn, rule_str, rule_stringp,
   rule_n_to_string, rule_string_to_n, rule_value, rule_simple_error, rule_error_to_string,
   rule_cons, rule_hd, rule_tl, rule_consp, rule_equal, rule_eval_kl, rule_absvectorp,
   rule_arith, rule_div, rule_cmp, rule_numberp, ret, throw, dom;
   rule_tac; unfold store_ok; auto; eapply lookup_ok; eauto; fail).
 - (* set *) unfold rule_set, ret, dom; rule_tac; unfold store_ok, eok in *; cbn; auto.
 - (* absvector *) unfold rule_absvector, ret, dom; rule_tac; unfold store_ok, eok in *; cbn;
   rewrite ?app_length; cbn.
   + apply Forall_app; split.
     * eapply Forall_impl; [|exact H]; intros a Ha; cbn in Ha; eapply lok_mono; [|exact Ha]; lia.
     * constructor; [|constructor]. apply lok_repeat. eapply vok_mono; [|exact PO]; lia.
   + eapply Forall_impl; [|exact G]; intros a Ha; cbn in Ha; eapply vok_mono; [|exact Ha]; lia.
   + lia.
   + lia.
 - (* address-> *) unfold rule_address_set, ret, dom; rule_tac; unfold store_ok, eok in *; cbn;
   rewrite ?replace_nth_length; auto.
   apply forall_replace; auto. apply lok_replace; auto. eapply Forall_forall in H; eauto.
   eapply nth_error_In; eauto.
 - (* <-address *) unfold rule_address_get, ret, dom; rule_tac; unfold store_ok; auto.
   eapply lok_nth; [|eassumption]. eapply Forall_forall in H; eauto. eapply nth_error_In; eauto.
 - unfold rule_write_byte, ret, dom, io_fail; rule_tac; intro resp; rule_tac; unfold store_ok; auto.
 - unfold rule_read_byte, ret, dom, io_fail; rule_tac; intro resp; rule_tac; unfold store_ok; auto.
 - unfold rule_open, ret, dom, io_fail; rule_tac; intro resp; rule_tac; unfold store_ok; auto.
 - unfold rule_close, ret, dom, io_fail; rule_tac; intro resp; rule_tac; unfold store_ok; auto.
 - unfold rule_get_time, ret, dom, io_fail; rule_tac; intro resp; rule_tac; unfold store_ok; auto.
Qed.

Section Moves.
Variable P : profile.
Hypothesis PO : profile_ok P.

Lemma prim_move_ok : forall p args rest k s, store_ok s -> lok (List.length (heap s)) args ->
 lok (List.length (heap s)) rest -> Forall (frame_ok (List.length (heap s))) k ->
 move_ok (prim_move P p args rest k s).
Proof.
 intros p args rest k s S A R K; unfold prim_move.
 pose proof (rule_ok P p args s PO S A) as G.
 destruct (prim_rule P p args s); cbn in *; [|intro r]; apply pout_config_ok; auto.
Qed.

Lemma wf_simple : forall c k s, control_ok (List.length (heap s)) c ->
 Forall (frame_ok (List.length (heap s))) k -> store_ok s -> wf (Cfg c k s).
Proof. intros; unfold wf; cbn; auto. Qed.

Lemma call_named_ok : forall g args k s, store_ok s -> lok (List.length (heap s)) args ->
 Forall (frame_ok (List.length (heap s))) k -> move_ok (call_named P g args k s).
Proof.
 intros g args k s S A K; unfold call_named.
 destruct (lookup g (gfuns s)) as [[p|ps b]|].
 - destruct (Nat.ltb (List.length args) (prim_arity p)); cbn.
   + apply wf_simple; auto. cbn; apply fold_lok; exact A.
   + apply prim_move_ok; auto using lok_firstn, lok_skipn.
 - destruct (Nat.ltb (List.length args) (List.length ps)); cbn.
   + apply wf_simple; auto. cbn; apply fold_lok; exact A.
   + apply continue_ok; auto using lok_skipn. cbn. apply eok_combine, lok_firstn; exact A.
 - apply wf_simple; cbn; auto.
Qed.

Lemma apply_value_ok : forall f args k s, store_ok s -> vok (List.length (heap s)) f ->
 lok (List.length (heap s)) args -> Forall (frame_ok (List.length (heap s))) k ->
 move_ok (apply_value P f args k s).
Proof.
 intros f args k s S F A K; unfold apply_value.
 destruct f; destruct args as [|a rest]; cbn in *; try (apply wf_simple; cbn; auto; fail).
 - apply continue_ok; auto.
   + cbn. apply fold_eok in F. inversion A; subst. constructor; auto.
   + inversion A; auto.
 - apply wf_simple; cbn; auto. apply fold_eok; exact F.
 - apply call_named_ok; auto. apply lok_app; [apply fold_lok; exact F|exact A].
 - apply call_named_ok; auto. apply lok_app; [apply fold_lok; exact F|exact A].
Qed.

Lemma eval_move_ok : forall rho e k s, store_ok s -> eok (List.length (heap s)) rho ->
 Forall (frame_ok (List.length (heap s))) k -> move_ok (eval_move P rho e k s).
Proof.
 intros rho e k s S R K; destruct e; cbn; try (apply push_ok; cbn; auto; fail);
 try (apply wf_simple; cbn; auto; fail).
 - apply wf_simple; cbn; auto. destruct (lookup x rho) eqn:E; cbn; auto. eapply lookup_ok; eauto.
 - apply wf_simple; cbn; auto. apply fold_eok; exact R.
 - destruct clauses as [|[c b] rest]; cbn; [apply wf_simple; cbn; auto|apply push_ok; cbn; auto].
 - apply wf_simple; cbn; auto. apply fold_eok; exact R.
 - destruct (nodupb params); cbn; apply wf_simple; cbn; auto.
 - destruct args as [|a rest]; [apply call_named_ok; auto; constructor|apply push_ok; cbn; auto].
   split; auto; constructor.
Qed.

Lemma ret_move_ok : forall v f k s, store_ok s -> vok (List.length (heap s)) v ->
 frame_ok (List.length (heap s)) f -> Forall (frame_ok (List.length (heap s))) k ->
 move_ok (ret_move P v f k s).
Proof.
 intros v f k s S V F K; destruct f; cbn in *;
 repeat match goal with H : _ /\ _ |- _ => destruct H end.
 - apply wf_simple; cbn; auto. constructor; auto.
 - apply wf_simple; auto. destruct v; cbn; auto. match goal with bb : bool |- _ => destruct bb end; cbn; auto.
 - destruct v; cbn; try (apply wf_simple; cbn; auto; fail). match goal with bb : bool |- _ => destruct bb end; cbn;
   [apply push_ok; cbn; auto|apply wf_simple; cbn; auto].
 - apply wf_simple; auto. destruct v; cbn; auto.
 - destruct v; cbn; try (apply wf_simple; cbn; auto; fail). match goal with bb : bool |- _ => destruct bb end; cbn;
   [apply wf_simple; cbn; auto|apply push_ok; cbn; auto].
 - apply wf_simple; auto. destruct v; cbn; auto.
 - apply wf_simple; auto. destruct v; cbn; auto. match goal with bb : bool |- _ => destruct bb end; cbn; auto.
 - apply wf_simple; cbn; auto.
 - destruct args as [|a rest]; [apply apply_value_ok; auto; constructor|].
   apply wf_simple; cbn; auto. constructor; cbn; auto. repeat split; auto. constructor.
 - destruct rest as [|a rest].
   + apply apply_value_ok; auto. apply lok_app; [apply lok_rev; auto|constructor; auto; constructor].
   + apply wf_simple; cbn; auto. constructor; cbn; auto. repeat split; auto. constructor; auto.
 - destruct rest as [|a rest].
   + apply call_named_ok; auto. apply lok_app; [apply lok_rev; auto|constructor; auto; constructor].
   + apply wf_simple; cbn; auto. constructor; cbn; auto. repeat split; auto. constructor; auto.
 - apply apply_value_ok; auto.
Qed.

Lemma throw_move_ok : forall x f k s, store_ok s -> frame_ok (List.length (heap s)) f ->
 Forall (frame_ok (List.length (heap s))) k -> move_ok (throw_move x f k s).
Proof.
 intros x f k s S F K; destruct f; cbn in *; try (apply wf_simple; cbn; auto; fail).
 apply wf_simple; cbn; auto. constructor; cbn; auto. constructor; cbn; auto.
Qed.

(* Well-formed-state preservation for internal steps and for every response. *)
Theorem next_preserves_wf : forall c, wf c -> move_ok (next P c).
Proof.
 intros [ctl k s] [C [K S]]; cbn in *; unfold next; cbn.
 destruct ctl; cbn in *; auto.
 - apply eval_move_ok; auto.
 - destruct k as [|f k]; cbn; auto. inversion K; subst. apply ret_move_ok; auto.
 - destruct k as [|f k]; cbn; auto. inversion K; subst. apply throw_move_ok; auto.
 - destruct ev; exact I.
Qed.

Theorem step_preserves_wf : forall c l c', wf c -> step P c l c' -> wf c'.
Proof.
 intros c l c' W S; pose proof (next_preserves_wf c W) as M.
 inversion S; subst; rewrite H in M; cbn in M; auto.
Qed.
End Moves.
End KLWellFormed.
