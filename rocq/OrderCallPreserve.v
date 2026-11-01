(* Outcome preservation for the actual captured argument-ordering pass.
   Source and target are related through the existing reader `decode` and the
   existing first-order effect evaluator, for ARBITRARY programs, external
   operations (effects, errors, unsupported operations), environments and
   states: every completed outcome -- value, raised error, unsupported --
   together with its final state and full left-to-right event trace is the
   same, and neither side completes when the other does not. *)
From Coq Require Import List String ZArith Bool Arith Lia.
From Buri Require Import Native ObserverEffects EffectContract EffectBigStep DecodeFacts
  OrderCallCorrect OrderCallPass.
Import ListNotations.
Module OrderCallPreserve.
Import Native.Native ObserverEffects.ObserverEffects EffectContract.EffectContract EffectBigStep.EffectBigStep.
Module O := OrderCallCorrect.OrderCallCorrect.
Module D := DecodeFacts.DecodeFacts.
Module Pass := OrderCallPass.OrderCallPass.
Open Scope string_scope.

Definition vars es := flat_map variables es.
Definition atom_syntax e := match e with Lit _ | Var _ => True | _ => False end.
(* Every argument that is a lexical variable reference is bound. *)
Definition bound_args (rho:env) es := forall s, In (Var s) es -> rho s <> None.

Section Semantics.
Variable p : program.
Variable op : string -> list value -> computation.

Lemma atom_yields : forall rho pre, Forall atom_syntax pre -> bound_args rho pre ->
 exists vs, Forall2 (yields p op rho) pre vs.
Proof.
 intros rho pre F; induction F as [|e es A F IH]; intro B; [exists []; constructor|].
 destruct IH as [vs Y]; [intros s I; apply B; right; exact I|].
 destruct e as [v|s| | | | |]; try contradiction.
 - exists (v::vs); constructor; [apply yields_lit|exact Y].
 - destruct (rho s) as [v|] eqn:R; [|exfalso; apply (B s); [left; reflexivity|exact R]].
   exists (v::vs); constructor; [apply yields_var; exact R|exact Y].
Qed.

Lemma yields_fresh : forall rho pre vs name x, Forall2 (yields p op rho) pre vs -> ~ In name (vars pre) ->
 Forall atom_syntax pre -> Forall2 (yields p op (Native.bind rho name x)) pre vs.
Proof.
 intros rho pre vs name x Y; induction Y as [|e v es vs' Ye Y IH]; intros N A; constructor.
 - inversion A as [|? ? Ae _]; subst. destruct e as [w|s| | | | |]; try contradiction.
   + pose proof (yields_ev _ _ _ _ _ _ _ Ye ((proj2 (ev_lit p op rho w Nil _)) eq_refl)) as X.
     inversion X; subst; apply yields_lit.
   + destruct (rho s) as [w|] eqn:R.
     * pose proof (yields_ev _ _ _ _ _ _ _ Ye (proj2 (ev_var p op rho s w Nil _ R) eq_refl)) as X.
       inversion X; subst. apply yields_var. unfold Native.bind.
       destruct (String.eqb s name) eqn:E; [|exact R].
       apply String.eqb_eq in E; subst. exfalso; apply N; left; reflexivity.
     * exfalso. pose proof (Ye Nil) as [C [n H]]. destruct n; [discriminate H|].
       cbn in H. rewrite R in H. discriminate H.
 - apply IH; [intro I; apply N; cbn; apply in_or_app; right; exact I|inversion A; assumption].
Qed.

(* Binding one computed argument to a fresh name before the call. *)
Theorem lift_one : forall rho f pre a post name st out,
 Forall atom_syntax pre -> bound_args rho pre -> ~ In name (vars pre) -> ~ In name (vars post) ->
 (ev p op rho (Call f (pre ++ a :: post)) st out <->
  ev p op rho (Let name a (Call f (pre ++ Var name :: post))) st out).
Proof.
 intros rho f pre a post name st out A B Npre Npost.
 destruct (atom_yields rho pre A B) as [vpre Y].
 rewrite ev_call, (evs_prefix p op rho pre vpre Y (a::post) _ (fun vs => apply_monotone _ _ _ _)).
 rewrite evs_cons by (intro; apply apply_monotone). rewrite ev_let.
 assert (K : forall x s1 o2,
   evs p op rho post (fun n vs => apply n p op f (vpre ++ x :: vs)) s1 o2 <->
   ev p op (Native.bind rho name x) (Call f (pre ++ Var name :: post)) s1 o2).
 { intros x s1 o2.
   rewrite ev_call, (evs_prefix p op _ pre vpre (yields_fresh rho pre vpre name x Y Npre A)
     (Var name :: post) _ (fun vs => apply_monotone _ _ _ _)).
   assert (YV : Forall2 (yields p op (Native.bind rho name x)) [Var name] [x]).
   { constructor; [apply yields_var; unfold Native.bind; rewrite String.eqb_refl; reflexivity|constructor]. }
   change (Var name :: post) with ([Var name] ++ post)%list.
   rewrite (evs_prefix p op _ [Var name] [x] YV post _ (fun vs => apply_monotone _ _ _ _)).
   cbn [app].
   rewrite (evs_congruent p op (Native.bind rho name x) rho post).
   - reflexivity.
   - intros e E n state. apply fresh_binding_preserves_effects.
     intro I; apply Npost; unfold vars; apply in_flat_map; exists e; auto. }
 split; (intros [[x [s1 [e1 [o2 [Ha [Hb E]]]]]]|R]; [left|right; exact R]);
 exists x, s1, e1, o2; (split; [exact Ha|]); (split; [apply K; exact Hb|exact E]).
Qed.
End Semantics.

(* The decoded shape of the ordering transformation: kept arguments stay in
   place; a lifted argument is bound to a name absent from every argument. *)
Inductive DOrd (f:string) : list expr -> list expr -> expr -> Prop :=
| d_done : forall pre, DOrd f pre [] (Call f pre)
| d_keep : forall pre a rest T, DOrd f (pre ++ [a]) rest T -> DOrd f pre (a :: rest) T
| d_lift : forall pre a rest name T, Forall atom_syntax pre -> ~ In name (vars pre) -> ~ In name (vars rest) ->
   DOrd f (pre ++ [Var name]) rest T -> DOrd f pre (a :: rest) (Let name a T).

Theorem dord_preserves : forall p op f pre rest T, DOrd f pre rest T ->
 forall rho st out, bound_args rho (pre ++ rest) ->
 (ev p op rho (Call f (pre ++ rest)) st out <-> ev p op rho T st out).
Proof.
 intros p op f pre rest T D; induction D as [pre|pre a rest T D IH|pre a rest name T A Np Nr D IH];
  intros rho st out B.
 - rewrite app_nil_r; reflexivity.
 - rewrite <- (IH rho st out); [rewrite <- app_assoc; reflexivity|].
   rewrite <- app_assoc; exact B.
 - rewrite (lift_one p op rho f pre a rest name st out A); try assumption.
   + apply ev_let_congr. intros x s o. rewrite <- (IH (Native.bind rho name x) s o).
     * rewrite <- app_assoc; reflexivity.
     * intros t I. unfold Native.bind. destruct (String.eqb t name) eqn:E; [discriminate|].
       apply B. rewrite <- app_assoc in I. cbn in I.
       apply in_app_or in I. apply in_or_app. destruct I as [I|[I|I]].
       -- left; exact I.
       -- inversion I; subst. rewrite String.eqb_refl in E; discriminate.
       -- right; right; exact I.
   + intros t I; apply B; apply in_or_app; left; exact I.
Qed.

Definition never_completes p op rho e st := forall out, ~ ev p op rho e st out.
Corollary dord_noncompletion : forall p op f pre rest T, DOrd f pre rest T ->
 forall rho st, bound_args rho (pre ++ rest) ->
 (never_completes p op rho (Call f (pre ++ rest)) st <-> never_completes p op rho T st).
Proof.
 intros p op f pre rest T D rho st B; unfold never_completes; split; intros N out E; apply (N out);
 apply (dord_preserves p op f pre rest T D rho st out B); exact E.
Qed.

(* ---------- the reader only produces variables that occur in the syntax ---------- *)
Lemma elements_in_occ : forall s t l x, elements t = Some l -> In x l -> O.occurrences s x <= O.occurrences s t.
Proof.
 intros s t; induction t as [| | | | | | |a IHa b IHb| |]; intros l x E I; cbn in E; try discriminate.
 - inversion E; subst; contradiction.
 - destruct (elements b) as [l'|] eqn:Eb; [|discriminate]. inversion E; subst l. cbn [O.occurrences].
   destruct I as [I|I]; [subst; lia|]. specialize (IHb l' x eq_refl I). lia.
Qed.
Lemma dmany_vars : forall d xs es, D.dmany d xs = Some es -> forall s, In s (vars es) ->
 exists x e, In x xs /\ d x = Some e /\ In s (variables e).
Proof.
 intros d xs; induction xs as [|x xs IH]; intros es H s I; cbn in H.
 - inversion H; subst; contradiction.
 - destruct (d x) as [e|] eqn:E; [|discriminate]. destruct (D.dmany d xs) as [es'|] eqn:R; [|discriminate].
   inversion H; subst. unfold vars in I; cbn in I. apply in_app_or in I. destruct I as [I|I].
   + exists x, e. cbn; tauto.
   + destruct (IH es' eq_refl s I) as [y [e' [Iy [Ey Ie]]]]. exists y, e'. cbn; tauto.
Qed.
Lemma dbindings_vars : forall d body xs e, D.dbindings d body xs = Some e -> forall s, In s (variables e) ->
 In s (variables body) \/ exists x n a av, In x xs /\ elements x = Some [Symbol n; av] /\ d av = Some a /\ In s (variables a).
Proof.
 intros d body xs; induction xs as [|x xs IH]; intros e H s I; cbn [D.dbindings] in H.
 - inversion H; subst; left; exact I.
 - destruct (D.dbindings d body xs) as [b|] eqn:R.
   2:{ destruct (elements x) as [l|]; [|discriminate H].
       destruct l as [|y [|av [|z zs]]]; try (cbn in H; discriminate H); destruct y; cbn in H; discriminate H. }
   destruct (elements x) as [l|] eqn:Ex; [|discriminate H].
   destruct l as [|y [|av [|z zs]]]; try (cbn in H; discriminate H); destruct y; try (cbn in H; discriminate H).
   destruct (d av) as [a|] eqn:Ea; [|cbn in H; discriminate H]. cbn in H. inversion H; subst. cbn [variables] in I.
   apply in_app_or in I. destruct I as [I|I].
   + right. exists x, s0, a, av. cbn; tauto.
   + destruct (IH b eq_refl s I) as [J|[y [n [a' [av' [Iy [Ey [Ea' Ia]]]]]]]]; [left; exact J|].
     right. exists y, n, a', av'. cbn; tauto.
Qed.
Lemma dcases_vars : forall d cs e, D.dcases d cs = Some e -> forall s, In s (variables e) ->
 exists c l y e', In c cs /\ elements c = Some l /\ In y l /\ d y = Some e' /\ In s (variables e').
Proof.
 intros d cs; induction cs as [|c cs IH]; intros e H s I; cbn in H; [discriminate|].
 destruct (elements c) as [l|] eqn:Ec; [|discriminate].
 assert (G : forall x b, l = [x;b] -> match d x, d b, D.dcases d cs with
   | Some c, Some b, Some rest => Some (If c b rest) | _,_,_ => None end = Some e ->
   exists c0 l0 y e', In c0 (c::cs) /\ elements c0 = Some l0 /\ In y l0 /\ d y = Some e' /\ In s (variables e')).
 { intros x b L K. subst l. destruct (d x) as [ex|] eqn:E1; [|discriminate]. destruct (d b) as [eb|] eqn:E2; [|discriminate].
   destruct (D.dcases d cs) as [rest|] eqn:R; [|discriminate]. inversion K; subst. cbn [variables] in I.
   apply in_app_or in I; destruct I as [I|I]; [exists c, [x;b], x, ex; cbn; tauto|].
   apply in_app_or in I; destruct I as [I|I]; [exists c, [x;b], b, eb; cbn; tauto|].
   destruct (IH rest eq_refl s I) as [c0 [l0 [y [e' [A B]]]]]. exists c0, l0, y, e'. split; [right; exact A|exact B]. }
 destruct l as [|x [|b [|z zs]]]; try (cbn in H; discriminate H);
  try (destruct x as [| | | | | |[|]| | |]; cbn in H; discriminate H).
 destruct x as [| | | | | |[|]| | |]; try (apply (G _ b eq_refl); exact H).
 destruct cs as [|c' cs']; [|cbn in H; discriminate H].
 exists c, [Boolean true; b], b, e. cbn. cbn; tauto.
Qed.
Lemma and_vars : forall es s,
 In s (variables (match fold_right (fun a tail => Some (match tail with None => a | Some b => And a b end)) None es with
  | Some e => e | None => Lit (Boolean true) end)) -> In s (vars es).
Proof.
 induction es as [|e es IH]; intros s I; [contradiction|]. cbn [fold_right] in I. unfold vars; cbn.
 destruct (fold_right _ None es) as [b|] eqn:R.
 - cbn [variables] in I. apply in_app_or in I. apply in_or_app. destruct I as [I|I]; [left; exact I|right].
   apply IH. exact I.
 - apply in_or_app; left; exact I.
Qed.
Lemma or_vars : forall es s, In s (variables (fold_right Or (Lit (Boolean false)) es)) -> In s (vars es).
Proof.
 induction es as [|e es IH]; intros s I; [contradiction|]. cbn [fold_right variables] in I.
 unfold vars; cbn. apply in_app_or in I. apply in_or_app. destruct I as [I|I]; [left; exact I|right; apply IH; exact I].
Qed.

Ltac crack H := repeat (first
 [ match type of H with context [match ?y with _ => _ end] => is_var y; destruct y end
 | match type of H with context [match elements ?x with _ => _ end] => let E := fresh "El" in destruct (elements x) eqn:E end
 | match type of H with context [match D.dmany ?d ?x with _ => _ end] => let E := fresh "Em" in destruct (D.dmany d x) eqn:E end
 | match type of H with context [match D.dbindings ?d ?b ?x with _ => _ end] => let E := fresh "Eb" in destruct (D.dbindings d b x) eqn:E end
 | match type of H with context [match D.dcases ?d ?x with _ => _ end] => let E := fresh "Ec" in destruct (D.dcases d x) eqn:E end
 | match type of H with context [match decode ?n ?x with _ => _ end] => let E := fresh "Ed" in destruct (decode n x) eqn:E end
 | progress (cbn -[decode D.dmany D.dbindings D.dcases] in H) ]); try discriminate H.

Ltac climb := first
 [ apply le_n
 | match goal with E : elements ?y = Some ?l |- O.occurrences ?s ?x <= _ =>
     eapply Nat.le_trans; [apply (elements_in_occ s y l x E); cbn; tauto|climb] end ].

Lemma tail_occ : forall s h tl x, O.occurrences s x <> 0 -> O.occurrences s x <= O.occurrences s tl ->
 O.occurrences s (Pair h tl) <> 0.
Proof. intros; cbn [O.occurrences]; lia. Qed.

Lemma decode_step_vars : forall n,
 (forall x e, decode n x = Some e -> forall s, In s (variables e) -> O.occurrences s x <> 0) ->
 forall v e, decode (S n) v = Some e -> forall s, In s (variables e) -> O.occurrences s v <> 0.
Proof.
 intros n IH v e H.
 destruct v as [|t| | | | | |h tl| |]; try (cbn in H; inversion H; subst; intros ? I; contradiction).
 - cbn in H. inversion H; subst. intros s I. cbn in I. destruct I as [I|[]]; subst. cbn. rewrite String.eqb_refl. lia.
 - destruct h as [|k| | | | | | | |];
    try (cbn [decode elements] in H; destruct (elements tl); [destruct l|]; discriminate H).
   destruct (in_dec string_dec k D.keywords) as [K|K].
   2:{ rewrite D.decode_default in H by exact K. intros s I.
       destruct (elements tl) as [xs|] eqn:Et; [|discriminate].
       destruct (D.dmany (decode n) xs) as [es|] eqn:Em; [|discriminate]. inversion H; subst.
       destruct (dmany_vars _ _ _ Em s I) as [x [e' [Ix [Ex Ie]]]].
       apply (tail_occ s _ tl x (IH _ _ Ex s Ie)). exact (elements_in_occ s tl xs x Et Ix). }
   cbn [D.keywords In] in K.
   destruct K as [K|[K|[K|[K|[K|[K|[K|[]]]]]]]]; subst k;
    cbn [decode elements] in H; destruct (elements tl) as [xs|] eqn:Et; try discriminate H; D.inline; crack H;
   intros sx I;
   (* generic arguments read through dmany *)
   try (inversion H; subst; cbn [variables] in I;
        destruct (dmany_vars _ _ _ Em sx I) as [x [e' [Ix [Ex Ie]]]];
        apply (tail_occ sx _ tl x (IH _ _ Ex sx Ie)); exact (elements_in_occ sx tl _ x Et Ix)).
   all: try (inversion H; subst; cbn [variables] in I; contradiction).
   (* if and let *)
   all: try (inversion H; subst; cbn [variables] in I;
        repeat (apply in_app_or in I; destruct I as [I|I]);
        match goal with E : decode _ ?x = Some ?e', I : In ?sx (variables ?e') |- _ =>
          apply (tail_occ sx _ tl x (IH _ _ E sx I)); climb end).
   (* and / or *)
   all: try (inversion H; subst; first [apply and_vars in I|apply or_vars in I];
        destruct (dmany_vars _ _ _ Em sx I) as [x [e' [Ix [Ex Ie]]]];
        apply (tail_occ sx _ tl x (IH _ _ Ex sx Ie)); exact (elements_in_occ sx tl _ x Et Ix)).
   (* cond *)
   all: try (destruct (dcases_vars _ _ _ H sx I) as [c [l [y [e' [Ic [Ec [Iy [Ey Ie]]]]]]]];
        apply (tail_occ sx _ tl y (IH _ _ Ey sx Ie));
        eapply Nat.le_trans; [exact (elements_in_occ sx c l y Ec Iy)|exact (elements_in_occ sx tl _ c Et Ic)]).
   (* let* *)
   all: try (destruct (dbindings_vars _ _ _ _ H sx I) as [J|[x [nm [a [av [Ix [Ex [Ea Ia]]]]]]]];
        [match goal with E : decode _ ?b = Some ?body, J : In ?sx (variables ?body) |- _ =>
           apply (tail_occ sx _ tl b (IH _ _ E sx J)); climb end
        |apply (tail_occ sx _ tl av (IH _ _ Ea sx Ia));
         eapply Nat.le_trans; [exact (elements_in_occ sx x _ av Ex ltac:(cbn; tauto))|];
         eapply Nat.le_trans; [exact (elements_in_occ sx _ _ x ltac:(eassumption) Ix)|climb]]).
   (* let*: the binding chain is read by the inline loop of decode *)
   assert (Hb : D.dbindings (decode n) e0 l = Some e).
   { clear - H. revert e H. induction l as [|x l IHl]; intros e H; [exact H|].
     cbn [D.dbindings]. cbn -[decode] in H.
     destruct (elements x) as [k|]; [|discriminate H].
     destruct k as [|y [|a [|z zs]]]; try (cbn in H; discriminate H); destruct y; try (cbn in H; discriminate H).
     match type of H with match ?t with Some _ => _ | None => _ end = _ =>
       destruct t as [o|] eqn:R; [|discriminate H] end.
     rewrite (IHl o eq_refl). exact H. }
   destruct (dbindings_vars _ _ _ _ Hb sx I) as [J|[x [nm [a [av [Ix [Ex [Ea Ia]]]]]]]].
   + apply (tail_occ sx _ tl v0 (IH _ _ Ed sx J)). exact (elements_in_occ sx tl _ v0 Et ltac:(cbn; tauto)).
   + apply (tail_occ sx _ tl av (IH _ _ Ea sx Ia)).
     eapply Nat.le_trans; [exact (elements_in_occ sx x _ av Ex ltac:(cbn; tauto))|].
     eapply Nat.le_trans; [exact (elements_in_occ sx v l x El Ix)|].
     exact (elements_in_occ sx tl _ v Et ltac:(cbn; tauto)).
Qed.

Theorem decode_vars : forall n v e, decode n v = Some e -> forall s, In s (variables e) -> O.occurrences s v <> 0.
Proof.
 induction n as [|n IH]; intros v e H; [discriminate H|]. exact (decode_step_vars n IH v e H).
Qed.

(* ---------- from every successful captured run to a decoded target ---------- *)
Local Open Scope list_scope.
(* Closure construction is outside the first-order evaluator: a lambda form is
   "simple" for the pass but would be read as an ordinary call. *)
Definition no_lambda y := match y with Pair h _ => Pass.symbol_is "lambda" h = false | _ => True end.
Definition covers u (ys : list value) := forall name, O.occurrences name u = 0 -> Forall (fun y => O.occurrences name y = 0) ys.
Definition prefix_ok (r' xs : list value) := Forall (fun y => Pass.simple y = true) r' \/ Pass.has_comp xs = false.

Lemma decode_let1 : forall n v x b,
 decode (S n) (L [Symbol "let"; L [L [Symbol v; x]]; b]) =
 match decode n b with Some B => match decode n x with Some A => Some (Let v A B) | None => None end | None => None end.
Proof. reflexivity. Qed.
Lemma decode_star : forall n bs b,
 decode (S n) (L [Symbol "let*"; bs; b]) =
 match elements bs with
 | Some ys => match decode n b with Some B => D.dbindings (decode n) B ys | None => None end
 | None => None end.
Proof.
 intros n bs b. cbn [decode elements L fold_right].
 destruct (elements bs) as [ys|]; [|reflexivity]. destruct (decode n b) as [B|]; [|reflexivity].
 induction ys as [|y ys IH]; [reflexivity|]. cbn [D.dbindings]. rewrite <- IH.
 cbn -[decode]. destruct (elements y) as [[|z [|a [|w ws]]]|]; try reflexivity; destruct z; reflexivity.
Qed.

Lemma dmany_app : forall d xs ys a b, D.dmany d xs = Some a -> D.dmany d ys = Some b -> D.dmany d (xs ++ ys) = Some (a ++ b).
Proof.
 intros d xs; induction xs as [|x xs IH]; intros ys a b A B; cbn in A.
 - inversion A; subst; exact B.
 - destruct (d x) as [e|] eqn:E; [|discriminate]. destruct (D.dmany d xs) as [a'|] eqn:R; [|discriminate].
   inversion A; subst. cbn. rewrite E, (IH ys a' b eq_refl B). reflexivity.
Qed.
Lemma dmany_cons : forall d x xs es, D.dmany d (x :: xs) = Some es ->
 exists e es', d x = Some e /\ D.dmany d xs = Some es' /\ es = e :: es'.
Proof.
 intros d x xs es H; cbn in H. destruct (d x) as [e|]; [|discriminate]. destruct (D.dmany d xs) as [es'|]; [|discriminate].
 inversion H; subst; eauto.
Qed.
Lemma dmany_forall : forall d (P : value -> Prop) (Q : expr -> Prop) xs es, D.dmany d xs = Some es -> Forall P xs ->
 (forall y e, P y -> d y = Some e -> Q e) -> Forall Q es.
Proof.
 intros d P Q xs; induction xs as [|x xs IH]; intros es H F K; cbn in H.
 - inversion H; constructor.
 - destruct (d x) as [e|] eqn:E; [|discriminate]. destruct (D.dmany d xs) as [es'|] eqn:R; [|discriminate].
   inversion H; subst. inversion F; subst. constructor; [eapply K; eauto|eapply IH; eauto].
Qed.
Lemma fresh_list : forall n name ys es, D.dmany (decode n) ys = Some es -> Forall (fun y => O.occurrences name y = 0) ys ->
 ~ In name (vars es).
Proof.
 intros n name ys es H F I. unfold vars in I. apply in_flat_map in I. destruct I as [e [Ie Iv]].
 assert (G : Forall (fun e => ~ In name (variables e)) es).
 { eapply dmany_forall; [exact H|exact F|]. intros y e' O D' J. exact (decode_vars n y e' D' name J O). }
 rewrite Forall_forall in G. exact (G e Ie Iv).
Qed.
Lemma simple_atom : forall n y e, Pass.simple y = true -> no_lambda y -> decode n y = Some e -> atom_syntax e.
Proof.
 intros [|n] y e S N H; [discriminate H|].
 destruct y as [| | | | | | |h t| |];
  try (lazymatch type of H with decode _ (Pair _ _) = _ => fail | _ => idtac end;
       cbn in H; inversion H; subst; exact I).
 cbn [Pass.simple no_lambda] in S, N. rewrite N in S. rewrite Bool.orb_false_r in S.
 destruct h as [|s| | | | | | | |]; try (cbn in S; discriminate S). cbn [Pass.symbol_is] in S.
 destruct (String.eqb "quote" s) eqn:Q; [|cbn in S; discriminate S]. apply String.eqb_eq in Q; subst s.
 destruct t as [| | | | | | |x [| | | | | | | | |]| |]; try (cbn in S; discriminate S).
 cbn in H. inversion H; subst. exact I.
Qed.
Lemma covers_args : forall f args, covers (L (Symbol f :: args)) args.
Proof.
 intros f args name O. apply Forall_forall. intros y I.
 pose proof (elements_in_occ name (L (Symbol f :: args)) (Symbol f :: args) y (ObserverEffects.elements_list _) (or_intror I)).
 lia.
Qed.
Lemma has_comp_cons : forall x xs, Pass.has_comp (x :: xs) = negb (Pass.simple x) || Pass.has_comp xs.
Proof. reflexivity. Qed.

Definition target_shape f N o T :=
 (exists args, o = Pair (Symbol f) args /\ decode (S N) o = Some T) \/
 (exists bs b, o = L [Symbol "let*"; bs; b]) \/ (exists b2 b, o = L [Symbol "let"; L [b2]; b]).

Lemma merge_decode : forall f N name x a o T, String.eqb "let*" f = false -> String.eqb "let" f = false ->
 decode (S N) x = Some a -> decode (S (S N)) o = Some T -> target_shape f N o T ->
 decode (S (S N)) (Pass.merge_spec (L [Symbol name; x]) o) = Some (Let name a T) /\
 target_shape f N (Pass.merge_spec (L [Symbol name; x]) o) (Let name a T).
Proof.
 intros f N name x a o T Q1 Q2 X O [[args [E D1]]|[[bs [b E]]|[b2 [b E]]]]; subst o.
 - assert (M : Pass.merge_spec (L [Symbol name; x]) (Pair (Symbol f) args) =
     L [Symbol "let"; L [L [Symbol name; x]]; Pair (Symbol f) args])
     by (unfold Pass.merge_spec; cbn [Pass.symbol_is]; rewrite Q1, Q2; reflexivity).
   rewrite M, decode_let1, D1, X. split; [reflexivity|].
   right; right. exists (L [Symbol name; x]), (Pair (Symbol f) args). reflexivity.
 - change (Pass.merge_spec (L [Symbol name; x]) (L [Symbol "let*"; bs; b])) with
     (L [Symbol "let*"; Pair (L [Symbol name; x]) bs; b]).
   rewrite decode_star in O |- *. cbn [elements].
   destruct (elements bs) as [ys|]; [|discriminate O]. destruct (decode (S N) b) as [B|]; [|discriminate O].
   cbn [D.dbindings L fold_right elements]. rewrite O, X. split; [reflexivity|].
   right; left. exists (Pair (L [Symbol name; x]) bs), b. reflexivity.
 - change (Pass.merge_spec (L [Symbol name; x]) (L [Symbol "let"; L [b2]; b])) with
     (L [Symbol "let*"; L [L [Symbol name; x]; b2]; b]).
   rewrite decode_star. cbn [elements L fold_right].
   remember (S N) as M eqn:HM. cbn [decode elements L fold_right] in O.
   destruct (elements b2) as [[|y [|av [|z zs]]]|] eqn:E2; try (cbn in O; discriminate O);
    destruct y; try (cbn in O; discriminate O).
   destruct (decode M b) as [B|] eqn:EB; [|cbn in O; discriminate O].
   destruct (decode M av) as [A2|] eqn:EA; [|cbn in O; discriminate O].
   cbn in O. inversion O; subst T. cbn [D.dbindings L fold_right elements]. rewrite E2, EA, X.
   split; [reflexivity|]. right; left. exists (L [L [Symbol name; x]; b2]), b. reflexivity.
Qed.

Theorem ord_decode : forall f N, ~ In f D.keywords ->
 forall xs r u o, Pass.Ord xs r u o -> forall r' pre rest, r = (r' ++ [Symbol f])%list ->
 D.dmany (decode N) (rev r') = Some pre -> D.dmany (decode N) xs = Some rest ->
 covers u (rev r' ++ xs) -> prefix_ok r' xs -> Forall no_lambda (rev r' ++ xs) ->
 exists T, DOrd f pre rest T /\ decode (S (S N)) o = Some T /\ target_shape f N o T.
Proof.
 intros f N K.
 assert (Q1 : String.eqb "let*" f = false) by (apply String.eqb_neq; intro E; apply K; subst; cbn; tauto).
 assert (Q2 : String.eqb "let" f = false) by (apply String.eqb_neq; intro E; apply K; subst; cbn; tauto).
 intros xs r u o Ord; induction Ord as [r u|x xs r u o Kp Ord IH|x xs r u name o Kp Occ Ord IH];
  intros r' pre rest Er Pre Rest Cov Ok NL.
 - cbn in Rest. inversion Rest; subst rest r. rewrite rev_app_distr. cbn [rev app].
   assert (DC : decode (S N) (L (Symbol f :: rev r')) = Some (Call f pre)) by (rewrite D.decode_call, Pre by exact K; reflexivity).
   exists (Call f pre). split; [constructor|]. split; [apply D.decode_succ; exact DC|].
   left. exists (L (rev r')). split; [reflexivity|exact DC].
 - destruct (dmany_cons _ _ _ _ Rest) as [a [rest' [Ea [Rest' E]]]]. subst rest.
   destruct (IH (x :: r') (pre ++ [a])%list rest') as [T [D1 [D2 D3]]].
   + try subst r; reflexivity.
   + cbn [rev]. apply dmany_app; [exact Pre|cbn; rewrite Ea; reflexivity].
   + exact Rest'.
   + cbn [rev]. rewrite <- app_assoc. exact Cov.
   + unfold Pass.keep in Kp. destruct (Pass.simple x) eqn:Sx.
     * destruct Ok as [F|F]; [left; constructor; assumption|right].
       rewrite has_comp_cons in F. destruct (Pass.has_comp xs); [rewrite orb_true_r in F; discriminate|reflexivity].
     * right. cbn in Kp. destruct (Pass.has_comp xs); [discriminate|reflexivity].
   + cbn [rev]. rewrite <- app_assoc. exact NL.
   + exists T. split; [apply d_keep; exact D1|]. split; assumption.
 - destruct (dmany_cons _ _ _ _ Rest) as [a [rest' [Ea [Rest' E]]]]. subst rest.
   destruct N as [|N']; [discriminate Ea|].
   unfold Pass.keep in Kp. destruct (Pass.simple x) eqn:Sx; [discriminate|].
   destruct (Pass.has_comp xs) eqn:HC; [|discriminate].
   assert (FS : Forall (fun y => Pass.simple y = true) r').
   { destruct Ok as [F|F]; [exact F|]. rewrite has_comp_cons, Sx in F. discriminate F. }
   pose proof (Cov name Occ) as CovN. rewrite Forall_app in CovN. destruct CovN as [CovR CovX].
   inversion CovX as [|? ? OccX CovXs]; subst.
   rewrite Forall_app in NL. destruct NL as [NLR NLX]. inversion NLX as [|? ? NLx NLxs]; subst.
   destruct (IH (Symbol name :: r') (pre ++ [Var name])%list rest') as [T [D1 [D2 D3]]].
   + try subst r; reflexivity.
   + cbn [rev]. apply dmany_app; [exact Pre|reflexivity].
   + exact Rest'.
   + intros nm O'. cbn [O.occurrences] in O'.
     destruct (String.eqb nm name) eqn:EN; [lia|].
     cbn [rev]. rewrite <- app_assoc. apply Forall_app. split.
     * pose proof (Cov nm ltac:(lia)) as C. rewrite Forall_app in C. exact (proj1 C).
     * constructor; [cbn; rewrite EN; reflexivity|].
       pose proof (Cov nm ltac:(lia)) as C. rewrite Forall_app in C. destruct C as [_ C2]. inversion C2; assumption.
   + left. cbn [rev]. constructor; [reflexivity|exact FS].
   + cbn [rev]. rewrite <- app_assoc. apply Forall_app. split; [exact NLR|]. constructor; [exact I|exact NLxs].
   + exists (Let name a T). split.
     * apply d_lift; [|exact (fresh_list _ name _ _ Pre CovR)|exact (fresh_list _ name _ _ Rest' CovXs)|exact D1].
       apply (dmany_forall _ (fun y => Pass.simple y = true /\ no_lambda y) atom_syntax _ _ Pre).
       { apply Forall_forall. intros y Iy. rewrite Forall_forall in FS, NLR.
         split; [apply FS; apply in_rev in Iy; exact Iy|apply NLR; exact Iy]. }
       intros y e [Sy Ny] Dy. exact (simple_atom _ y e Sy Ny Dy).
     * apply (merge_decode f (S N') name x a o T Q1 Q2); [apply D.decode_succ; exact Ea|exact D2|exact D3].
Qed.

(* ---------- end-to-end: actual pass execution preserves outcomes ---------- *)
(* Admission: the input call has an application head (not a special-form
   keyword), is read by `decode`, and has no closure-construction argument.
   For every generator and every successful pass run, the produced syntax is
   read at a budget one larger and, for ANY program, external operations,
   environment binding the variable arguments, and state, has exactly the
   same completed outcomes (value/error/unsupported, final state, trace). *)
Theorem order_call_preserves : forall gen N f args es st0 c st0' tr0,
 ~ In f D.keywords -> decode (S N) (L (Symbol f :: args)) = Some (Call f es) -> Forall no_lambda args ->
 evapp Pass.P (Pass.op gen) "kl:_scm.order-call" [L (Symbol f :: args)] st0 (Out (Returned c) st0' tr0) ->
 exists target, decode (S (S N)) c = Some target /\
  forall p op rho st out, bound_args rho es ->
   (ev p op rho (Call f es) st out <-> ev p op rho target st out).
Proof.
 intros gen N f args es st0 c st0' tr0 K D NL H.
 assert (Q1 : String.eqb "let*" f = false) by (apply String.eqb_neq; intro E; apply K; subst; cbn; tauto).
 assert (Q2 : String.eqb "let" f = false) by (apply String.eqb_neq; intro E; apply K; subst; cbn; tauto).
 destruct (Pass.order_call_success gen f args st0 c st0' tr0 Q1 Q2 H) as [Ord _].
 rewrite D.decode_call in D by exact K.
 destruct (D.dmany (decode N) args) as [es'|] eqn:A; [|discriminate D]. inversion D; subst es'. clear D.
 inversion Ord as [|x xs r u o Kp Ord'|x xs r u name o Kp Occ Ord']; subst.
 - destruct (ord_decode f N K args [Symbol f] (L (Symbol f :: args)) c Ord' [] [] es eq_refl eq_refl A
     (covers_args f args) (or_introl (Forall_nil _)) NL) as [T [DT [DC _]]].
   exists T. split; [exact DC|]. intros p op rho st out B.
   exact (dord_preserves p op f [] es T DT rho st out B).
 - unfold Pass.keep in Kp. cbn in Kp. discriminate Kp.
Qed.

Corollary order_call_noncompletion : forall gen N f args es st0 c st0' tr0,
 ~ In f D.keywords -> decode (S N) (L (Symbol f :: args)) = Some (Call f es) -> Forall no_lambda args ->
 evapp Pass.P (Pass.op gen) "kl:_scm.order-call" [L (Symbol f :: args)] st0 (Out (Returned c) st0' tr0) ->
 exists target, decode (S (S N)) c = Some target /\
  forall p op rho st, bound_args rho es ->
   (never_completes p op rho (Call f es) st <-> never_completes p op rho target st).
Proof.
 intros gen N f args es st0 c st0' tr0 K D NL H.
 destruct (order_call_preserves gen N f args es st0 c st0' tr0 K D NL H) as [T [DT E]].
 exists T. split; [exact DT|]. intros p op rho st B; unfold never_completes.
 split; intros Nc out X; apply (Nc out); apply (E p op rho st out B); exact X.
Qed.
End OrderCallPreserve.
