(* Fuel-free completed-outcome reasoning for the first-order effect evaluator.
   `conv F st out` says that some budget completes with exactly `out`. Budgets
   are monotone, so a completed outcome is unique; exhaustion is never a
   completed outcome and is never relabelled as success or divergence. *)
From Coq Require Import List String Arith Lia.
From Buri Require Import Native ObserverEffects EffectContract CallRefinement.
Import ListNotations.
Module EffectBigStep.
Import Native.Native ObserverEffects.ObserverEffects EffectContract.EffectContract.

Definition monotone (F:nat->computation) := forall n m, n<=m -> approximates (F n) (F m).
Definition conv (F:nat->computation) st out := completed out /\ exists n, F n st = out.
Definition stops o := forall v, answer o <> Returned v.
Definition after (es:list event) (o:outcome) := Out (answer o) (records o) (es ++ trace o).

Lemma after_nil : forall o, after [] o = o.
Proof. intros [r s es]; reflexivity. Qed.
Lemma after_app : forall a b o, after a (after b o) = after (a ++ b) o.
Proof. intros a b [r s es]; unfold after; cbn; rewrite app_assoc; reflexivity. Qed.
Lemma returned_completed : forall v s es, completed (Out (Returned v) s es).
Proof. intros; unfold completed; cbn; discriminate. Qed.

Lemma conv_det : forall F st a b, monotone F -> conv F st a -> conv F st b -> a = b.
Proof.
 intros F st a b M [Ca [n A]] [Cb [m B]].
 pose proof (M n (max n m) ltac:(lia) st a A Ca) as X.
 pose proof (M m (max n m) ltac:(lia) st b B Cb) as Y. congruence.
Qed.
Lemma conv_fixed : forall F n st o out, monotone F -> F n st = o -> completed o -> conv F st out -> o = out.
Proof. intros F n st o out M E C H. apply (conv_det F st); auto. split; [exact C|exists n; exact E]. Qed.
Lemma conv_shift : forall F st out, monotone F -> (conv (fun n => F (S n)) st out <-> conv F st out).
Proof.
 intros F st out M; split; intros [C [n E]]; split; auto.
 - exists (S n); exact E.
 - exists n. exact (M n (S n) ltac:(lia) st out E C).
Qed.
Lemma conv_ext : forall F G st out, (forall n st, F n st = G n st) -> (conv F st out <-> conv G st out).
Proof. intros F G st out E; split; intros [C [n H]]; split; auto; exists n; [rewrite <- E|rewrite E]; exact H. Qed.

Lemma conv_bind : forall F G st out, monotone F -> (forall v, monotone (fun n => G n v)) ->
 (conv (fun n => bind (F n) (G n)) st out <->
  (exists v s1 e1 o2, conv F st (Out (Returned v) s1 e1) /\ conv (fun n => G n v) s1 o2 /\ out = after e1 o2) \/
  (conv F st out /\ stops out)).
Proof.
 intros F G st out MF MG; split.
 - intros [C [n E]]. rewrite bind_result in E.
   destruct (F n st) as [r s1 e1] eqn:R. destruct r as [v| | |].
   + left. exists v, s1, e1, (G n v s1). subst out.
     split; [split; [apply returned_completed|exists n; exact R]|].
     split; [|reflexivity]. split; [|exists n; reflexivity]. exact C.
   + right. subst out. split; [split; [exact C|exists n; exact R]|intros v; discriminate].
   + right. subst out. split; [split; [exact C|exists n; exact R]|intros v; discriminate].
   + right. subst out. split; [split; [exact C|exists n; exact R]|intros v; discriminate].
 - intros [[v [s1 [e1 [o2 [[_ [n A]] [[C2 [m B]] E]]]]]]|[[C [n A]] S]].
   + subst out. split; [exact C2|]. exists (max n m). rewrite bind_result.
     rewrite (MF n (max n m) ltac:(lia) st _ A (returned_completed _ _ _)).
     cbv beta iota zeta.
     rewrite (MG v m (max n m) ltac:(lia) s1 o2 B C2). reflexivity.
   + split; [exact C|]. exists n. rewrite bind_result, A.
     destruct out as [r s es]; destruct r; try reflexivity. exfalso; apply (S v); reflexivity.
Qed.

Lemma eval_monotone : forall p op rho e, monotone (fun n => eval_with n p op rho e).
Proof. intros p op rho e n m L st o E C. eapply eval_completed_monotone; eauto. Qed.
Lemma apply_monotone : forall p op f vs, monotone (fun n => apply n p op f vs).
Proof. intros p op f vs n m L. apply CallRefinement.apply_approximates; exact L. Qed.
Lemma many_monotone : forall p op rho es K, (forall vs, monotone (fun n => K n vs)) ->
 monotone (fun n => many n p op rho es (K n)).
Proof.
 intros p op rho es K MK n m L. apply many_approximates.
 - intro e; apply eval_monotone; exact L.
 - intro vs; apply MK; exact L.
Qed.
Lemma const_monotone : forall c, monotone (fun _ => c).
Proof. intros c n m L; apply approximates_refl. Qed.

Lemma bind_inv : forall m k st out, bind m k st = out -> completed out ->
 (exists v s1 e1, m st = Out (Returned v) s1 e1 /\ completed (k v s1) /\ out = after e1 (k v s1)) \/
 (m st = out /\ stops out).
Proof.
 intros m k st out E C. rewrite bind_result in E.
 destruct (m st) as [r s1 e1] eqn:R. destruct r as [v| | |].
 - left. exists v, s1, e1. subst out. split; [reflexivity|]. split; [exact C|reflexivity].
 - right. subst out. split; [reflexivity|intros v; discriminate].
 - right. subst out. split; [reflexivity|intros v; discriminate].
 - right. subst out. split; [reflexivity|intros v; discriminate].
Qed.

Section Semantics.
Variable p : program.
Variable op : string -> list value -> computation.

Definition ev rho e st out := conv (fun n => eval_with n p op rho e) st out.
Definition evs rho es (K:nat -> list value -> computation) st out := conv (fun n => many n p op rho es (K n)) st out.
Definition evapp f vs st out := conv (fun n => apply n p op f vs) st out.
Definition yields rho e v := forall st, ev rho e st (Out (Returned v) st []).

Lemma ev_det : forall rho e st a b, ev rho e st a -> ev rho e st b -> a = b.
Proof. intros; eapply conv_det; eauto; apply eval_monotone. Qed.
Lemma evapp_det : forall f vs st a b, evapp f vs st a -> evapp f vs st b -> a = b.
Proof. intros; eapply conv_det; eauto; apply apply_monotone. Qed.
Lemma ev_completed : forall rho e st out, ev rho e st out -> completed out.
Proof. intros rho e st out [C _]; exact C. Qed.

Lemma ev_lit : forall rho v st out, ev rho (Lit v) st out <-> out = Out (Returned v) st [].
Proof.
 intros rho v st out; unfold ev; rewrite <- conv_shift by apply eval_monotone. split.
 - intros [C [n E]]; exact (eq_sym E).
 - intro E; subst; split; [apply returned_completed|exists 0; reflexivity].
Qed.
Lemma ev_var : forall rho s v st out, rho s = Some v -> (ev rho (Var s) st out <-> out = Out (Returned v) st []).
Proof.
 intros rho s v st out R; unfold ev; rewrite <- conv_shift by apply eval_monotone.
 change (conv (fun _ => match rho s with Some v => ret v | None => return_result Unsupported end) st out <->
   out = Out (Returned v) st []).
 rewrite R. split.
 - intros [C [n E]]; exact (eq_sym E).
 - intro E; subst; split; [apply returned_completed|exists 0; reflexivity].
Qed.
Lemma ev_let : forall rho s a b st out, ev rho (Let s a b) st out <->
 (exists v s1 e1 o2, ev rho a st (Out (Returned v) s1 e1) /\ ev (Native.bind rho s v) b s1 o2 /\ out = after e1 o2) \/
 (ev rho a st out /\ stops out).
Proof.
 intros. unfold ev. rewrite <- conv_shift by apply eval_monotone.
 exact (conv_bind (fun n => eval_with n p op rho a) (fun n v => eval_with n p op (Native.bind rho s v) b) st out
  (eval_monotone _ _ _ _) (fun v => eval_monotone _ _ _ _)).
Qed.
Lemma ev_if : forall rho c a b st out, ev rho (If c a b) st out <->
 (exists v s1 e1 o2, ev rho c st (Out (Returned v) s1 e1) /\
   ev rho (match v with Boolean false => b | _ => a end) s1 o2 /\ out = after e1 o2) \/
 (ev rho c st out /\ stops out).
Proof.
 intros. unfold ev. rewrite <- conv_shift by apply eval_monotone.
 exact (conv_bind (fun n => eval_with n p op rho c)
  (fun n v => eval_with n p op rho (match v with Boolean false => b | _ => a end)) st out
  (eval_monotone _ _ _ _) (fun v => eval_monotone _ _ _ _)).
Qed.
Lemma ev_call : forall rho f es st out, ev rho (Call f es) st out <-> evs rho es (fun n => apply n p op f) st out.
Proof.
 intros. unfold ev, evs. rewrite <- conv_shift by apply eval_monotone. split; intro H; exact H.
Qed.
Lemma evs_nil : forall rho K st out, evs rho [] K st out <-> conv (fun n => K n []) st out.
Proof. intros; split; intro H; exact H. Qed.
Lemma evs_cons : forall rho a es K st out, (forall vs, monotone (fun n => K n vs)) ->
 (evs rho (a::es) K st out <->
  (exists v s1 e1 o2, ev rho a st (Out (Returned v) s1 e1) /\
    evs rho es (fun n vs => K n (v::vs)) s1 o2 /\ out = after e1 o2) \/
  (ev rho a st out /\ stops out)).
Proof.
 intros rho a es K st out MK. unfold evs, ev.
 exact (conv_bind (fun n => eval_with n p op rho a) (fun n v => many n p op rho es (fun vs => K n (v::vs))) st out
  (eval_monotone _ _ _ _) (fun v => many_monotone _ _ _ _ _ (fun vs => MK (v::vs)))).
Qed.
Lemma evapp_def : forall f vs d st out, p f = Some d -> List.length (params d) = List.length vs ->
 (evapp f vs st out <-> ev (arguments (params d) vs) (body d) st out).
Proof.
 intros f vs d st out D A. unfold evapp, ev. apply conv_ext. intros n s.
 unfold apply. rewrite D, A, Nat.eqb_refl. reflexivity.
Qed.
Lemma evapp_op : forall f vs st out, p f = None -> (evapp f vs st out <-> completed out /\ op f vs st = out).
Proof.
 intros f vs st out D. unfold evapp, apply. rewrite D. split.
 - intros [C [n E]]; split; assumption.
 - intros [C E]; split; [exact C|exists 0; exact E].
Qed.

Lemma yields_ev : forall rho e v st out, yields rho e v -> ev rho e st out -> out = Out (Returned v) st [].
Proof. intros rho e v st out Y E; exact (ev_det rho e st out _ E (Y st)). Qed.
Lemma yields_at : forall n rho e v st o, yields rho e v -> eval_with n p op rho e st = o -> completed o ->
 o = Out (Returned v) st [].
Proof. intros n rho e v st o Y E C. exact (conv_fixed _ n st o _ (eval_monotone _ _ _ _) E C (Y st)). Qed.

Lemma evs_yields : forall rho es vs, Forall2 (yields rho) es vs -> forall K, (forall vs, monotone (fun n => K n vs)) ->
 forall st out, evs rho es K st out <-> conv (fun n => K n vs) st out.
Proof.
 intros rho es vs F; induction F as [|e v es vs Y F IH]; intros K MK st out; [apply evs_nil|].
 rewrite (evs_cons rho e es K st out MK). split.
 - intros [[v' [s1 [e1 [o2 [A [B E]]]]]]|[A S]].
   + pose proof (yields_ev _ _ _ _ _ Y A) as X. inversion X; subst.
     rewrite after_nil. apply (IH (fun n vs => K n (v::vs))); [intro; apply MK|exact B].
   + pose proof (yields_ev _ _ _ _ _ Y A) as X. subst out. exfalso; apply (S v); reflexivity.
 - intro H. left. exists v, st, [], out. split; [apply Y|]. split; [|symmetry; apply after_nil].
   apply (IH (fun n vs => K n (v::vs))); [intro; apply MK|exact H].
Qed.
Lemma ev_call_yields : forall rho f es vs st out, Forall2 (yields rho) es vs ->
 (ev rho (Call f es) st out <-> evapp f vs st out).
Proof.
 intros rho f es vs st out F. rewrite ev_call.
 exact (evs_yields rho es vs F (fun n => apply n p op f) (fun vs => apply_monotone _ _ _ _) st out).
Qed.
Lemma yields_lit : forall rho v, yields rho (Lit v) v.
Proof. intros rho v st; apply ev_lit; reflexivity. Qed.
Lemma yields_var : forall rho s v, rho s = Some v -> yields rho (Var s) v.
Proof. intros rho s v R st; apply (ev_var rho s v st _ R); reflexivity. Qed.
Lemma yields_prim : forall rho f es vs v, Forall2 (yields rho) es vs -> p f = None ->
 (forall st, op f vs st = Out (Returned v) st []) -> yields rho (Call f es) v.
Proof.
 intros rho f es vs v F D O st. apply (ev_call_yields rho f es vs st _ F).
 apply evapp_op; [exact D|]. split; [apply returned_completed|apply O].
Qed.
Lemma yields_def : forall rho f es vs d v, Forall2 (yields rho) es vs -> p f = Some d ->
 List.length (params d) = List.length vs -> yields (arguments (params d) vs) (body d) v -> yields rho (Call f es) v.
Proof.
 intros rho f es vs d v F D A Y st. apply (ev_call_yields rho f es vs st _ F).
 apply (evapp_def f vs d st _ D A). apply Y.
Qed.
Lemma yields_if : forall rho c a b cv v, yields rho c cv ->
 yields rho (match cv with Boolean false => b | _ => a end) v -> yields rho (If c a b) v.
Proof.
 intros rho c a b cv v C B st. apply ev_if. left. exists cv, st, [], (Out (Returned v) st []).
 split; [apply C|]. split; [apply B|reflexivity].
Qed.
Lemma yields_let : forall rho s a b av v, yields rho a av -> yields (Native.bind rho s av) b v ->
 yields rho (Let s a b) v.
Proof.
 intros rho s a b av v A B st. apply ev_let. left. exists av, st, [], (Out (Returned v) st []).
 split; [apply A|]. split; [apply B|reflexivity].
Qed.
Lemma ev_and : forall rho a b st out, ev rho (And a b) st out <->
 (exists v s1 e1 o2, ev rho a st (Out (Returned v) s1 e1) /\
   conv (fun n => match v with Boolean false => ret v | _ => eval_with n p op rho b end) s1 o2 /\ out = after e1 o2) \/
 (ev rho a st out /\ stops out).
Proof.
 intros. unfold ev. rewrite <- conv_shift by apply eval_monotone.
 apply (conv_bind (fun n => eval_with n p op rho a)
  (fun n v => match v with Boolean false => ret v | _ => eval_with n p op rho b end) st out (eval_monotone _ _ _ _)).
 intro v; destruct v as [| | | | | |[|]| | |]; try apply eval_monotone; apply const_monotone.
Qed.
Lemma ev_or : forall rho a b st out, ev rho (Or a b) st out <->
 (exists v s1 e1 o2, ev rho a st (Out (Returned v) s1 e1) /\
   conv (fun n => match v with Boolean false => eval_with n p op rho b | _ => ret v end) s1 o2 /\ out = after e1 o2) \/
 (ev rho a st out /\ stops out).
Proof.
 intros. unfold ev. rewrite <- conv_shift by apply eval_monotone.
 apply (conv_bind (fun n => eval_with n p op rho a)
  (fun n v => match v with Boolean false => eval_with n p op rho b | _ => ret v end) st out (eval_monotone _ _ _ _)).
 intro v; destruct v as [| | | | | |[|]| | |]; try apply const_monotone; apply eval_monotone.
Qed.
Lemma conv_ret : forall v st out, conv (fun _ => ret v) st out <-> out = Out (Returned v) st [].
Proof.
 intros; split; [intros [C [n E]]; exact (eq_sym E)|intro E; subst; split; [apply returned_completed|exists 0; reflexivity]].
Qed.
Lemma yields_and_false : forall rho a b, yields rho a (Boolean false) -> yields rho (And a b) (Boolean false).
Proof.
 intros rho a b A st. apply ev_and. left. exists (Boolean false), st, [], (Out (Returned (Boolean false)) st []).
 split; [apply A|]. split; [apply conv_ret; reflexivity|reflexivity].
Qed.
Lemma yields_and_true : forall rho a b av v, yields rho a av -> av <> Boolean false -> yields rho b v ->
 yields rho (And a b) v.
Proof.
 intros rho a b av v A N B st. apply ev_and. left. exists av, st, [], (Out (Returned v) st []).
 split; [apply A|]. split; [|reflexivity].
 destruct av as [| | | | | |[|]| | |]; try apply B; congruence.
Qed.
Lemma yields_or_false : forall rho a b v, yields rho a (Boolean false) -> yields rho b v -> yields rho (Or a b) v.
Proof.
 intros rho a b v A B st. apply ev_or. left. exists (Boolean false), st, [], (Out (Returned v) st []).
 split; [apply A|]. split; [apply B|reflexivity].
Qed.
Lemma yields_or_true : forall rho a b av, yields rho a av -> av <> Boolean false -> yields rho (Or a b) av.
Proof.
 intros rho a b av A N st. apply ev_or. left. exists av, st, [], (Out (Returned av) st []).
 split; [apply A|]. split; [|reflexivity].
 destruct av as [| | | | | |[|]| | |]; try (apply conv_ret; reflexivity); congruence.
Qed.

Lemma yields_and : forall rho a b av v, yields rho a av ->
 yields rho (match av with Boolean false => Lit (Boolean false) | _ => b end) v -> yields rho (And a b) v.
Proof.
 intros rho a b av v A B. destruct av as [| | | | | |[|]| | |];
 try (eapply yields_and_true; [exact A|discriminate|exact B]).
 intro st. pose proof (yields_ev _ _ _ _ _ (yields_lit rho (Boolean false)) (B st)) as E. inversion E; subst.
 apply yields_and_false; exact A.
Qed.
Lemma yields_or : forall rho a b av v, yields rho a av ->
 yields rho (match av with Boolean false => b | _ => Lit av end) v -> yields rho (Or a b) v.
Proof.
 intros rho a b av v A B. destruct av as [| | | | | |[|]| | |];
 try (apply (yields_or_false rho a b v A B));
 (intro st; pose proof (yields_ev _ _ _ _ _ (yields_lit rho _) (B st)) as E; inversion E; subst;
  apply yields_or_true; [exact A|discriminate]).
Qed.
Lemma yields_returns : forall rho f es vs v, Forall2 (yields rho) es vs ->
 (forall st, evapp f vs st (Out (Returned v) st [])) -> yields rho (Call f es) v.
Proof. intros rho f es vs v F R st. apply (ev_call_yields rho f es vs st _ F). apply R. Qed.

(* A pure condition selects a branch without effects. *)
Lemma ev_if_yields : forall rho c a b cv st out, yields rho c cv ->
 (ev rho (If c a b) st out <-> ev rho (match cv with Boolean false => b | _ => a end) st out).
Proof.
 intros rho c a b cv st out C. rewrite ev_if. split.
 - intros [[v [s1 [e1 [o2 [A [B E]]]]]]|[A S]].
   + pose proof (yields_ev _ _ _ _ _ C A) as X. inversion X; subst. rewrite after_nil; exact B.
   + pose proof (yields_ev _ _ _ _ _ C A) as X. subst out. exfalso; apply (S cv); reflexivity.
 - intro B. left. exists cv, st, [], out. split; [apply C|]. split; [exact B|symmetry; apply after_nil].
Qed.
Lemma ev_let_yields : forall rho s a b av st out, yields rho a av ->
 (ev rho (Let s a b) st out <-> ev (Native.bind rho s av) b st out).
Proof.
 intros rho s a b av st out A. rewrite ev_let. split.
 - intros [[v [s1 [e1 [o2 [X [B E]]]]]]|[X S]].
   + pose proof (yields_ev _ _ _ _ _ A X) as Y. inversion Y; subst. rewrite after_nil; exact B.
   + pose proof (yields_ev _ _ _ _ _ A X) as Y. subst out. exfalso; apply (S av); reflexivity.
 - intro B. left. exists av, st, [], out. split; [apply A|]. split; [exact B|symmetry; apply after_nil].
Qed.
(* A call whose arguments are pure except one, evaluated in its position. *)
Lemma ev_call_focus : forall rho f pre a post vpre vpost st out,
 Forall2 (yields rho) pre vpre -> Forall2 (yields rho) post vpost ->
 (ev rho (Call f (pre ++ a :: post)) st out <->
  (exists v s1 e1 o2, ev rho a st (Out (Returned v) s1 e1) /\ evapp f (vpre ++ v :: vpost) s1 o2 /\ out = after e1 o2) \/
  (ev rho a st out /\ stops out)).
Proof.
 intros rho f pre a post vpre vpost st out Pre Post. rewrite ev_call.
 assert (G : forall K, (forall vs, monotone (fun n => K n vs)) -> forall st out,
   evs rho (pre ++ a :: post) K st out <-> evs rho (a :: post) (fun n vs => K n (vpre ++ vs)) st out).
 { clear st out. induction Pre as [|x y xs ys Y Pre IH]; intros K MK st out; [reflexivity|].
   cbn [app]. rewrite (evs_cons rho x (xs ++ a :: post) K st out MK). split.
   - intros [[v [s1 [e1 [o2 [A [B E]]]]]]|[A S]].
     + pose proof (yields_ev _ _ _ _ _ Y A) as X. inversion X; subst. rewrite after_nil.
       exact (proj1 (IH (fun n vs => K n (y::vs)) (fun vs => MK (y::vs)) st o2) B).
     + pose proof (yields_ev _ _ _ _ _ Y A) as X. subst out. exfalso; apply (S y); reflexivity.
   - intro B. left. exists y, st, [], out. split; [apply Y|]. split; [|symmetry; apply after_nil].
     exact (proj2 (IH (fun n vs => K n (y::vs)) (fun vs => MK (y::vs)) st out) B). }
 rewrite (G (fun n => apply n p op f) (fun vs => apply_monotone _ _ _ _) st out).
 rewrite evs_cons by (intro; apply apply_monotone). split.
 - intros [[v [s1 [e1 [o2 [A [B E]]]]]]|[A S]]; [left|right; split; assumption].
   exists v, s1, e1, o2. split; [exact A|]. split; [|exact E].
   exact (proj1 (evs_yields rho post vpost Post (fun n vs => apply n p op f (vpre ++ v :: vs))
    (fun vs => apply_monotone _ _ _ _) s1 o2) B).
 - intros [[v [s1 [e1 [o2 [A [B E]]]]]]|[A S]]; [left|right; split; assumption].
   exists v, s1, e1, o2. split; [exact A|]. split; [|exact E].
   exact (proj2 (evs_yields rho post vpost Post (fun n vs => apply n p op f (vpre ++ v :: vs))
    (fun vs => apply_monotone _ _ _ _) s1 o2) B).
Qed.
End Semantics.
End EffectBigStep.
