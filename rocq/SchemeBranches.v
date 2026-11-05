(* E2E-15: the actual captured Shen-Scheme binding, conditional and equality
   emitters (compiler-branches capture: yields-boolean?, force-boolean,
   emit-symbol, emit-let, emit-if, emit-cond, emit-cond-clauses,
   emit-equality-check from pinned src/compiler.shen, read inside the exact
   upstream package header), linked with the captured merge-nested-lets and
   the captured Shen kernel element?.

   Recursive calls of compile-expression, the order-call call made by
   emit-equality-check and every remaining uncaptured compiler function are
   ARBITRARY stateful operations: every theorem holds for all of them. The
   results are exact denotations: for every input, every completed outcome
   (value, raised error, unsupported), final state and compile-time trace of a
   captured emitter equals a stated sequencing of its sub-compilations. *)
From Coq Require Import List String ZArith Bool Ascii Arith Lia.
From Buri Require Import Native ObserverEffects EffectContract EffectBigStep
  CallRefinement OrderCallInput OrderCallPass CompilerBranchesInput KernelElementInput.
Import ListNotations.
Module SchemeBranches.
Import Native.Native ObserverEffects.ObserverEffects EffectContract.EffectContract EffectBigStep.EffectBigStep.
Module Pass := OrderCallPass.OrderCallPass.
Open Scope string_scope.

(* ---------- exact denotations of first-order effectful code ---------- *)
Section Denote.
Variable p : program.
Variable op : string -> list value -> computation.

Definition denotes rho e (m:computation) := forall st out, ev p op rho e st out <-> completed out /\ m st = out.
Definition denotes_app f vs (m:computation) := forall st out, evapp p op f vs st out <-> completed out /\ m st = out.
Definition same_comp (m m':computation) := forall st, m st = m' st.

Lemma completed_after : forall e o, completed (after e o) <-> completed o.
Proof. intros e [r s t]; unfold completed, after; cbn; tauto. Qed.
Lemma bind_after : forall m k st v s1 e1, m st = Out (Returned v) s1 e1 -> bind m k st = after e1 (k v s1).
Proof. intros m k st v s1 e1 E. unfold bind. rewrite E. cbn. destruct (k v s1); reflexivity. Qed.
Lemma bind_stop : forall m k st, stops (m st) -> bind m k st = m st.
Proof.
 intros m k st S. unfold bind. destruct (m st) as [[v| | |] s e]; try reflexivity.
 exfalso; apply (S v); reflexivity.
Qed.

Lemma denotes_ext : forall rho e m m', same_comp m m' -> denotes rho e m -> denotes rho e m'.
Proof. intros rho e m m' E D st out. rewrite (D st out), E. tauto. Qed.
Lemma denotes_app_ext : forall f vs m m', same_comp m m' -> denotes_app f vs m -> denotes_app f vs m'.
Proof. intros f vs m m' E D st out. rewrite (D st out), E. tauto. Qed.

(* The shared shape of every sequencing rule. *)
Lemma conv_seq : forall (A : outcome -> Prop) m (B : value -> value -> outcome -> Prop) k st out,
 (forall o, A o <-> completed o /\ m st = o) ->
 (forall v s1 o, B v s1 o <-> completed o /\ k v s1 = o) ->
 (((exists v s1 e1 o2, A (Out (Returned v) s1 e1) /\ B v s1 o2 /\ out = after e1 o2) \/ (A out /\ stops out)) <->
  completed out /\ bind m k st = out).
Proof.
 intros A m B k st out HA HB. split.
 - intros [[v [s1 [e1 [o2 [X [Y E]]]]]]|[X S]].
   + apply HA in X. apply HB in Y. destruct X as [_ X]. destruct Y as [C Y]. subst out o2.
     split; [apply completed_after; exact C|]. apply bind_after; exact X.
   + apply HA in X. destruct X as [C X]. split; [exact C|]. rewrite bind_stop; [exact X|]. rewrite X; exact S.
 - intros [C E]. destruct (m st) as [r s1 e1] eqn:M. destruct r as [v| | |].
   + left. exists v, s1, e1, (k v s1). split; [apply HA; split; [apply returned_completed|reflexivity]|].
     rewrite (bind_after m k st v s1 e1 M) in E. subst out.
     split; [apply HB; split; [apply completed_after in C; exact C|reflexivity]|reflexivity].
   + right. rewrite bind_stop in E by (rewrite M; intros v; discriminate). rewrite M in E. subst out.
     split; [apply HA; split; [exact C|reflexivity]|intros v; discriminate].
   + right. rewrite bind_stop in E by (rewrite M; intros v; discriminate). rewrite M in E. subst out.
     split; [apply HA; split; [exact C|reflexivity]|intros v; discriminate].
   + right. rewrite bind_stop in E by (rewrite M; intros v; discriminate). rewrite M in E. subst out.
     split; [apply HA; split; [exact C|reflexivity]|intros v; discriminate].
Qed.

Lemma denotes_lit : forall rho v, denotes rho (Lit v) (ret v).
Proof. intros rho v st out. rewrite ev_lit. split; [intro E; subst; split; [apply returned_completed|reflexivity]|intros [_ E]; symmetry; exact E]. Qed.
Lemma denotes_yields : forall rho e v, yields p op rho e v -> denotes rho e (ret v).
Proof.
 intros rho e v Y st out. split.
 - intro H. pose proof (yields_ev p op rho e v st out Y H). subst. split; [apply returned_completed|reflexivity].
 - intros [_ E]. subst. apply Y.
Qed.
Lemma denotes_let : forall rho s a b ma mb, denotes rho a ma -> (forall v, denotes (Native.bind rho s v) b (mb v)) ->
 denotes rho (Let s a b) (bind ma mb).
Proof.
 intros rho s a b ma mb A B st out. rewrite ev_let.
 apply (conv_seq (ev p op rho a st) ma (fun v s1 o => ev p op (Native.bind rho s v) b s1 o) mb st out).
 - intro o; apply A.
 - intros v s1 o; apply B.
Qed.
Lemma denotes_if : forall rho c a b mc mb, denotes rho c mc ->
 (forall v, denotes rho (match v with Boolean false => b | _ => a end) (mb v)) -> denotes rho (If c a b) (bind mc mb).
Proof.
 intros rho c a b mc mb C B st out. rewrite ev_if.
 apply (conv_seq (ev p op rho c st) mc (fun v s1 o => ev p op rho (match v with Boolean false => b | _ => a end) s1 o) mb st out).
 - intro o; apply C.
 - intros v s1 o; apply B.
Qed.
Lemma denotes_if_yields : forall rho c a b cv m, yields p op rho c cv ->
 denotes rho (match cv with Boolean false => b | _ => a end) m -> denotes rho (If c a b) m.
Proof. intros rho c a b cv m C B st out. rewrite (ev_if_yields p op rho c a b cv st out C). apply B. Qed.

(* Arguments are evaluated left to right, then the callee is applied. *)
Fixpoint seq_args (ms : list computation) (k : list value -> computation) : computation :=
 match ms with [] => k [] | m :: ms => bind m (fun v => seq_args ms (fun vs => k (v :: vs))) end.
Lemma denotes_args : forall rho es ms, Forall2 (denotes rho) es ms ->
 forall K k, (forall vs, monotone (fun n => K n vs)) ->
 (forall vs st out, conv (fun n => K n vs) st out <-> completed out /\ k vs st = out) ->
 forall st out, evs p op rho es K st out <-> completed out /\ seq_args ms k st = out.
Proof.
 intros rho es ms F; induction F as [|e m es ms D F IH]; intros K k MK HK st out.
 - rewrite evs_nil. apply HK.
 - rewrite (evs_cons p op rho e es K st out MK). cbn [seq_args].
   apply (conv_seq (ev p op rho e st) m (fun v s1 o => evs p op rho es (fun n vs => K n (v :: vs)) s1 o)
     (fun v => seq_args ms (fun vs => k (v :: vs))) st out).
   + intro o; apply D.
   + intros v s1 o. apply (IH (fun n vs => K n (v :: vs)) (fun vs => k (v :: vs))); [intro; apply MK|].
     intros vs; apply HK.
Qed.
Lemma denotes_call : forall rho f es ms k, Forall2 (denotes rho) es ms -> (forall vs, denotes_app f vs (k vs)) ->
 denotes rho (Call f es) (seq_args ms k).
Proof.
 intros rho f es ms k F A st out. rewrite ev_call.
 apply (denotes_args rho es ms F (fun n => apply n p op f) k (fun vs => apply_monotone _ _ _ _)).
 intros vs s o. apply A.
Qed.
Lemma denotes_call_pure : forall rho f es vs m, Forall2 (yields p op rho) es vs -> denotes_app f vs m ->
 denotes rho (Call f es) m.
Proof. intros rho f es vs m F A st out. rewrite (ev_call_yields p op rho f es vs st out F). apply A. Qed.
Lemma yields_or_bool : forall rho a b x y, yields p op rho a (Boolean x) -> yields p op rho b (Boolean y) ->
 yields p op rho (Or a b) (Boolean (x || y)).
Proof.
 intros rho a b [|] y A B.
 - apply (yields_or_true p op rho a b (Boolean true) A). discriminate.
 - apply (yields_or_false p op rho a b _ A B).
Qed.
Lemma yields_and_bool : forall rho a b x y, yields p op rho a (Boolean x) -> yields p op rho b (Boolean y) ->
 yields p op rho (And a b) (Boolean (x && y)).
Proof.
 intros rho a b [|] y A B.
 - apply (yields_and_true p op rho a b (Boolean true) _ A); [discriminate|exact B].
 - apply (yields_and_false p op rho a b A).
Qed.
Lemma denotes_app_op : forall f vs, p f = None -> denotes_app f vs (op f vs).
Proof. intros f vs D st out. rewrite (evapp_op p op f vs st out D). tauto. Qed.
Lemma denotes_app_def : forall f vs d m, p f = Some d -> List.length (params d) = List.length vs ->
 denotes (arguments (params d) vs) (body d) m -> denotes_app f vs m.
Proof. intros f vs d m D L B st out. rewrite (evapp_def p op f vs d st out D L). apply B. Qed.
Lemma bind_ret_l : forall v k, same_comp (bind (ret v) k) (k v).
Proof. intros v k st. unfold bind, ret, return_result. cbn. destruct (k v st); reflexivity. Qed.
Lemma bind_ext : forall m m' k k', same_comp m m' -> (forall v, same_comp (k v) (k' v)) -> same_comp (bind m k) (bind m' k').
Proof. intros m m' k k' M K st. unfold bind. rewrite M. destruct (m' st) as [[v| | |] s e]; cbn; try reflexivity. rewrite (K v s). reflexivity. Qed.
Lemma bind_ret_r : forall m, same_comp (bind m ret) m.
Proof. intros m st. unfold bind, ret, return_result. destruct (m st) as [[v| | |] s e]; cbn; try reflexivity. rewrite app_nil_r; reflexivity. Qed.
Lemma bind_assoc : forall m k h, same_comp (bind (bind m k) h) (bind m (fun v => bind (k v) h)).
Proof.
 intros m k h st. unfold bind. destruct (m st) as [[v| | |] s e]; cbn; try reflexivity.
 destruct (k v s) as [[w| | |] s' e']; cbn; try (rewrite ?app_nil_r; reflexivity).
 destruct (h w s') as [r s'' e'']; cbn. rewrite app_assoc. reflexivity.
Qed.
Lemma same_refl : forall m, same_comp m m.
Proof. intros m st; reflexivity. Qed.
Lemma same_trans : forall a b c, same_comp a b -> same_comp b c -> same_comp a c.
Proof. intros a b c X Y st. rewrite X; apply Y. Qed.
End Denote.

(* ---------- the linked captured world ---------- *)
(* merge-nested-lets is the first definition of the ordering capture. *)
Definition linked := (compiler_branches_program ++ firstn 1 order_call_program ++ kernel_element_program)%list.
Definition link name := if String.eqb name "kl:element?" then "kl:buri.kernel.element?" else name.
Definition P : program := fun name => lookup linked (link name).

(* kl:= from pinned src/primitives.scm: eq? fast path, numbers by numeric =,
   pairs and strings structurally, everything else by identity. Only exact
   integers are modelled numerically; any other number comparison is outside
   the numeric profile (unsupported), never guessed. *)
Fixpoint kleq (a b : value) : option bool := match a with
 | Integer n => match b with Integer m => Some (Z.eqb n m) | Fraction _ _ | Inexact _ => None | _ => Some false end
 | Fraction _ _ | Inexact _ => if numeric b then None else Some false
 | Pair a1 a2 => match b with
   | Pair b1 b2 => match kleq a1 b1 with Some true => kleq a2 b2 | r => r end
   | _ => Some false end
 | Text s => Some (match b with Text t => String.eqb s t | _ => false end)
 | Symbol s => Some (match b with Symbol t => String.eqb s t | _ => false end)
 | Nil => Some (match b with Nil => true | _ => false end)
 | Boolean x => Some (match b with Boolean y => Bool.eqb x y | _ => false end)
 | Character c => Some (match b with Character d => Ascii.eqb c d | _ => false end)
 | Handle n => Some (match b with Handle m => Nat.eqb n m | _ => false end)
 end.

Section World.
Variable cexp : value -> value -> computation.        (* recursive compile-expression *)
Variable ordc : value -> computation.                 (* the order-call call *)
Variable ext : string -> list value -> computation.   (* every other uncaptured compiler function *)
Variables ys1 ys2 : list string.                       (* the static yields-boolean symbol lists *)

(* assert-boolean (src/primitives.scm): identity on booleans, otherwise it
   raises; the raised payload carries the offending value. *)
Definition op name args : computation := fun st =>
 match name, args with
 | "kl:_scm.compile-expression", [x; s] => cexp x s st
 | "kl:_scm.order-call", [c] => ordc c st
 | "kl:global/_scm.*yields-boolean1*", [] => Out (Returned (L (map Symbol ys1))) st []
 | "kl:global/_scm.*yields-boolean2*", [] => Out (Returned (L (map Symbol ys2))) st []
 | "kl:=", [a; b] => match kleq a b with Some r => Out (Returned (Boolean r)) st [] | None => Out Unsupported st [] end
 | "kl:_scm.assert-boolean", [Boolean b] => Out (Returned (Boolean b)) st []
 | "kl:_scm.assert-boolean", [v] => Out (Raised (Symbol "_scm.assert-boolean") v) st []
 | _, _ => if String.prefix "kl:" name then ext name args st else Out (external name args) st [] end.


(* ---------- pure captured helpers ---------- *)
Definition returns f vs v := forall st, evapp P op f vs st (Out (Returned v) st []).
Lemma returns_def : forall f vs d v, P f = Some d -> List.length (params d) = List.length vs ->
 yields P op (arguments (params d) vs) (body d) v -> returns f vs v.
Proof. intros f vs d v D A Y st. apply (evapp_def P op f vs d st _ D A). apply Y. Qed.
Lemma returns_prim : forall f vs v, P f = None -> (forall st, op f vs st = Out (Returned v) st []) -> returns f vs v.
Proof. intros f vs v D O st. apply (evapp_op P op f vs st _ D). split; [apply returned_completed|apply O]. Qed.
Lemma yields_call_returns : forall rho f es vs v, Forall2 (yields P op rho) es vs -> returns f vs v ->
 yields P op rho (Call f es) v.
Proof. intros rho f es vs v F R. exact (yields_returns P op rho f es vs v F R). Qed.
Lemma denotes_app_returns : forall f vs v, returns f vs v -> denotes_app P op f vs (ret v).
Proof.
 intros f vs v R st out. split.
 - intro H. pose proof (evapp_det P op f vs st out _ H (R st)). subst. split; [apply returned_completed|reflexivity].
 - intros [_ E]. subst. apply R.
Qed.

Definition name_is t x := match x with Symbol s => String.eqb s t | _ => false end.
Lemma kleq_symbol : forall x t, kleq x (Symbol t) = Some (name_is t x).
Proof. intros [| | | | | | | | |] t; reflexivity. Qed.
Lemma op_kleq : forall a b r st, kleq a b = Some r -> op "kl:=" [a; b] st = Out (Returned (Boolean r)) st [].
Proof. intros a b r st E. cbv beta iota delta [op]. rewrite E. reflexivity. Qed.

Definition head_is t x := match x with Symbol s => String.eqb t s | _ => false end.
Lemma op_eq_symbol : forall s h st, op "eq?" [Symbol s; h] st = Out (Returned (Boolean (head_is s h))) st [].
Proof. intros s [| | | | | | | | |] st; reflexivity. Qed.
(* (= [fail] V) in emit-equality-check: structural kl:= against (fail). *)
Definition is_fail v := match v with
 | Pair b1 b2 => (match b1 with Symbol t => String.eqb "fail" t | _ => false end) && (match b2 with Nil => true | _ => false end)
 | _ => false end.
Lemma kleq_fail : forall v, kleq (L [Symbol "fail"]) v = Some (is_fail v).
Proof.
 intros [| | | | | | |b1 b2| |]; try reflexivity. cbn [L fold_right kleq is_fail].
 destruct b1; try reflexivity. cbn [kleq]. destruct (String.eqb "fail" s); destruct b2; reflexivity.
Qed.

Ltac decisions := repeat match goal with Q : _ = true |- _ => rewrite Q | Q : _ = false |- _ => rewrite Q end.
Ltac sel := cbv beta iota zeta fix delta [L fold_right map negb andb orb]; decisions;
 cbn [String.eqb Ascii.eqb Bool.eqb]; cbv beta iota zeta fix delta [L fold_right map negb andb orb].
Ltac Y := match goal with
 | |- yields _ _ _ (Lit _) _ => apply yields_lit
 | |- yields _ _ _ (Var _) _ => apply yields_var; reflexivity
 | |- yields _ _ _ (If _ _ _) _ => eapply yields_if; [Y|sel; Y]
 | |- yields _ _ _ (And _ _) _ => eapply yields_and; [Y|sel; Y]
 | |- yields _ _ _ (Or _ _) _ => eapply yields_or; [Y|sel; Y]
 | |- yields _ _ _ (Let _ _ _) _ => eapply yields_let; [Y|Y]
 | |- yields _ _ _ (Call _ _) _ => eapply yields_call_returns; [Yargs|R]
 end
with R := first
 [ match goal with |- returns ?f _ _ => first
     [ match goal with H : returns f _ _ |- _ => apply H end
     | match goal with H : forall _, returns f _ _ |- _ => apply H end
     | match goal with H : forall _ _, returns f _ _ |- _ => apply H end ] end
 | eapply returns_prim; [reflexivity|intro; reflexivity]
 | match goal with |- returns "kl:=" _ _ =>
     eapply returns_prim; [reflexivity|intro; apply op_kleq; first [apply kleq_symbol|apply kleq_fail]] end
 | match goal with |- returns "eq?" _ _ => eapply returns_prim; [reflexivity|intro; apply op_eq_symbol] end
 | eapply returns_def; [reflexivity|reflexivity|cbn [Native.body Native.params]; Y] ]
with Yargs := match goal with
 | |- Forall2 _ [] _ => constructor
 | |- Forall2 _ (_::_) _ => econstructor; [Y|Yargs]
 end.
Ltac body := eapply returns_def; [reflexivity|reflexivity|cbn [Native.body Native.params]].

Definition member x (ys : list string) := existsb (fun t => name_is t x) ys.
(* The captured kernel element? over a list of symbols. *)
Lemma kernel_element_returns : forall x ys,
 returns "kl:buri.kernel.element?" [x; L (map Symbol ys)] (Boolean (member x ys)).
Proof.
 intros x ys; induction ys as [|t ys IH]; [body; Y|].
 unfold member; cbn [map existsb]; fold (member x ys).
 destruct (name_is t x) eqn:Q; cbn [orb]; body; Y.
Qed.
Lemma element_returns : forall x ys, returns "kl:element?" [x; L (map Symbol ys)] (Boolean (member x ys)).
Proof. intros x ys st. exact (kernel_element_returns x ys st). Qed.


(* ---------- exact denotations of the effectful emitters ---------- *)
Ltac D := match goal with
 | |- denotes _ _ _ (Lit _) _ => apply denotes_lit
 | |- denotes _ _ _ (Var _) _ => apply denotes_yields; apply yields_var; reflexivity
 | |- denotes _ _ _ (If _ _ _) _ => eapply denotes_if_yields; [Y|sel; D]
 | |- denotes _ _ _ (Let _ _ _) _ => eapply denotes_let; [D|intro; D]
 | |- denotes _ _ _ (Call _ _) _ => first [eapply denotes_call_pure; [Yargs|DA] | eapply denotes_call; [Ds|intro; DA]]
 end
with Ds := match goal with
 | |- Forall2 _ [] _ => constructor
 | |- Forall2 _ (_::_) _ => econstructor; [D|Ds]
 end
with DA := first
 [ match goal with |- denotes_app _ _ ?f _ _ => first
     [ match goal with H : denotes_app _ _ f _ _ |- _ => apply H end
     | match goal with H : forall _, denotes_app _ _ f _ _ |- _ => apply H end ] end
 | apply denotes_app_op; reflexivity
 | eapply denotes_app_def; [reflexivity|reflexivity|cbn [Native.body Native.params]; D] ].
Ltac start := eapply denotes_app_ext; [|eapply denotes_app_def; [reflexivity|reflexivity|cbn [Native.body Native.params]; D]].
(* Pointwise equality of the derived denotation with a stated sequencing:
   case on every sub-compilation result (value, error, unsupported, exhausted). *)
Ltac finish_with stop := intro; cbv beta iota zeta delta -[app stop]; repeat (match goal with
 | |- context [cexp ?x ?y ?z] => destruct (cexp x y z) as [[| | |] ? ?]
 | |- context [ordc ?x ?z] => destruct (ordc x z) as [[| | |] ? ?]
 | |- context [ext ?x ?y ?z] => destruct (ext x y z) as [[| | |] ? ?]
 end; cbv beta iota zeta delta -[app stop]); cbn [app]; rewrite ?app_nil_r, ?app_assoc; reflexivity.

Definition emit_let_spec x v b s :=
 bind (cexp v s) (fun cv => bind (cexp b (Pair x s)) (fun cb => ret (L [Symbol "let"; L [L [x; cv]]; cb]))).
(* Binding emission: the value is compiled in the outer scope, then the body
   in the scope extended by the bound variable; effects in that order. *)
Theorem emit_let_exact : forall x v b s, denotes_app P op "kl:_scm.emit-let" [x; v; b; s] (emit_let_spec x v b s).
Proof. intros. start. unfold emit_let_spec. finish_with app. Qed.

Definition is_text v := match v with Text _ => true | _ => false end.
Definition is_nil v := match v with Nil => true | _ => false end.
Definition eq_call opn v1 v2 s :=
 bind (cexp v1 s) (fun c1 => bind (cexp v2 s) (fun c2 => ordc (L [Symbol opn; c1; c2]))).
Definition null_call v s := bind (cexp v s) (fun c => ret (L [Symbol "null?"; c])).
(* The exact branch selection of the captured emit-equality-check, given the
   (pure, boolean) answers u1 u2 of the uncaptured unbound-symbol? calls. *)
Definition emit_eq_spec u1 u2 v1 v2 s :=
 if u1 || u2 || is_fail v1 || is_fail v2 then eq_call "eq?" v1 v2 s
 else if numeric v1 || numeric v2 then eq_call "eqv?" v1 v2 s
 else if is_text v1 || is_text v2 then eq_call "equal?" v1 v2 s
 else if is_nil v1 then null_call v2 s
 else if is_nil v2 then null_call v1 s
 else bind (ext "kl:_scm.native-mode" []) (fun m =>
   ext "kl:_scm.emit-static-application-fallback" [m; Symbol "="; L [v1; v2]; s]).
Definition pure_answer f vs v := forall st, ext f vs st = Out (Returned v) st [].
Theorem emit_equality_exact : forall v1 v2 s u1 u2,
 pure_answer "kl:_scm.unbound-symbol?" [v1; s] (Boolean u1) ->
 pure_answer "kl:_scm.unbound-symbol?" [v2; s] (Boolean u2) ->
 denotes_app P op "kl:_scm.emit-equality-check" [v1; v2; s] (emit_eq_spec u1 u2 v1 v2 s).
Proof.
 intros v1 v2 s u1 u2 U1 U2.
 assert (R1 : returns "kl:_scm.unbound-symbol?" [v1; s] (Boolean u1)).
 { apply returns_prim; [reflexivity|]. intro st. exact (U1 st). }
 assert (R2 : returns "kl:_scm.unbound-symbol?" [v2; s] (Boolean u2)).
 { apply returns_prim; [reflexivity|]. intro st. exact (U2 st). }
 clear U1 U2. unfold emit_eq_spec, eq_call, null_call.
 destruct u1; cbn [orb]; [start; finish_with app|].
 destruct u2; cbn [orb]; [start; finish_with app|].
 destruct (is_fail v1) eqn:F1; cbn [orb]; [start; finish_with app|].
 destruct (is_fail v2) eqn:F2; cbn [orb]; [start; finish_with app|].
 destruct (numeric v1) eqn:N1; cbn [orb]; [start; finish_with app|].
 destruct (numeric v2) eqn:N2; cbn [orb]; [start; finish_with app|].
 destruct (is_text v1) eqn:T1; unfold is_text in T1; cbn [orb]; [start; finish_with app|].
 destruct (is_text v2) eqn:T2; unfold is_text in T2; cbn [orb]; [start; finish_with app|].

 destruct v1 as [| | | | | | | | |]; cbn [is_nil]; try discriminate; [start; finish_with app| | | | |];
 (destruct v2 as [| | | | | | | | |]; cbn [is_nil]; try discriminate; start; finish_with app).
Qed.


(* The exact decision of the captured yields-boolean?: literal booleans,
   (let _ _ E), (do _ E) with E boolean-yielding, and two/three-element forms
   whose head is in the corresponding static list. *)
Fixpoint yields_b v := match v with
 | Boolean _ => true
 | Pair h (Pair _ (Pair _ (Pair e Nil))) => head_is "let" h && yields_b e
 | Pair h (Pair _ (Pair e Nil)) => if head_is "do" h then yields_b e else member h ys2
 | Pair h (Pair _ Nil) => member h ys1
 | _ => false end.
Definition force_spec v := if yields_b v then v else L [Symbol "_scm.assert-boolean"; v].

Lemma yields_returns : forall v, returns "kl:_scm.yields-boolean?" [v] (Boolean (yields_b v)).
Proof.
 assert (EL := element_returns). assert (EQ := op_eq_symbol).
 fix IH 1. intro v.
 destruct v as [| | | | | |[|]|h t| |]; try (body; Y).
 destruct (head_is "let" h) eqn:Ql; destruct (head_is "do" h) eqn:Qd;
 (destruct t as [| | | | | | |a t2| |]; [| | | | | | |destruct t2 as [| | | | | | |b t3| |]| |]);
 try (destruct t3 as [| | | | | | |e t4| |]; [| | | | | | |destruct t4| |]);
 cbn [yields_b]; decisions; cbn [andb]; body; Y.
Qed.
Lemma force_returns : forall v, returns "kl:_scm.force-boolean" [v] (force_spec v).
Proof. intro v. assert (YR := yields_returns). unfold force_spec. destruct (yields_b v) eqn:Q; body; Y. Qed.

Definition emit_if_spec t a b s := match t with
 | Boolean true => cexp a s
 | Boolean false => cexp b s
 | _ => bind (cexp (force_spec t) s) (fun ct => bind (cexp a s) (fun ca =>
        bind (cexp b s) (fun cb => ret (L [Symbol "if"; ct; ca; cb])))) end.
(* Conditionals: a literal test compiles only the selected branch (the other
   branch is never compiled); any other test is forced boolean, then the test,
   then-branch and else-branch are compiled in that order. *)
Theorem emit_if_exact : forall t a b s, denotes_app P op "kl:_scm.emit-if" [t; a; b; s] (emit_if_spec t a b s).
Proof.
 intros t a b s. assert (FR := force_returns).
 destruct t as [| | | | | |[|]| | |]; start; unfold emit_if_spec; finish_with force_spec.
Qed.

Fixpoint clauses_spec cs s : computation := match cs with
 | Nil => ret Nil
 | Pair (Pair t (Pair b Nil)) rest => bind (cexp (force_spec t) s) (fun ct => bind (cexp b s) (fun cb =>
     bind (clauses_spec rest s) (fun cr => ret (Pair (L [ct; cb]) cr))))
 | _ => ext "kl:shen.f-error" [Symbol "_scm.emit-cond-clauses"] end.
Theorem emit_cond_clauses_exact : forall cs s,
 denotes_app P op "kl:_scm.emit-cond-clauses" [cs; s] (clauses_spec cs s).
Proof.
 intros cs s. assert (FR := force_returns).
 induction cs as [| | | | | | |c _ rest IH| |]; try (start; cbn [clauses_spec]; finish_with force_spec).
 destruct c as [| | | | | | |t [| | | | | | |b [| | | | | | | | |]| |]| |];
  start; cbn [clauses_spec]; finish_with clauses_spec.
Qed.
Theorem emit_cond_exact : forall cs s, denotes_app P op "kl:_scm.emit-cond" [cs; s]
 (bind (clauses_spec cs s) (fun r => ret (Pair (Symbol "cond") r))).
Proof.
 intros cs s. assert (C := emit_cond_clauses_exact cs s). start.
 intro st. cbv beta iota zeta delta -[app clauses_spec]. destruct (clauses_spec cs s st) as [[| | |] ? ?];
 cbv beta iota zeta delta -[app clauses_spec]; rewrite ?app_nil_r; reflexivity.
Qed.

(* The captured merge-nested-lets (the first definition of the ordering
   capture, linked into this program) on the three shapes that the ordering
   pass returns: a call whose head is not let/let*, a let* form, a one-binding let. *)
Lemma merge_call : forall b1 f args, String.eqb "let*" f = false -> String.eqb "let" f = false ->
 returns "kl:_scm.merge-nested-lets" [L [Symbol "let"; L [b1]; Pair (Symbol f) args]]
  (Pass.merge_spec b1 (Pair (Symbol f) args)).
Proof. intros b1 f args Q1 Q2. unfold Pass.merge_spec; cbn [Pass.symbol_is]; rewrite Q1, Q2. body; Y. Qed.
Lemma merge_star : forall b1 bs b,
 returns "kl:_scm.merge-nested-lets" [L [Symbol "let"; L [b1]; L [Symbol "let*"; bs; b]]]
  (Pass.merge_spec b1 (L [Symbol "let*"; bs; b])).
Proof. intros. unfold Pass.merge_spec. body; Y. Qed.
Lemma merge_let : forall b1 b2 b,
 returns "kl:_scm.merge-nested-lets" [L [Symbol "let"; L [b1]; L [Symbol "let"; L [b2]; b]]]
  (Pass.merge_spec b1 (L [Symbol "let"; L [b2]; b])).
Proof. intros. unfold Pass.merge_spec. body; Y. Qed.
Lemma merge_shaped : forall f b1 o, String.eqb "let*" f = false -> String.eqb "let" f = false ->
 Pass.shaped f o -> returns "kl:_scm.merge-nested-lets" [L [Symbol "let"; L [b1]; o]] (Pass.merge_spec b1 o).
Proof.
 intros f b1 o Q1 Q2 [[args E]|[[bs [b E]]|[b2 [b E]]]]; subst o;
  [apply merge_call; assumption|apply merge_star|apply merge_let].
Qed.
End World.
End SchemeBranches.
