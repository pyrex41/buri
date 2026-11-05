(* Fuel-free partial semantics for a captured Native program, used to reason
   about the actual EQ-1 kernel. Calls into the program go through a fuelled
   oracle built from the same decoded bodies; primitives keep Native.external.
   Theorem [eval_oracle]: every value the actual Native evaluator returns is the
   value this semantics returns. No program-specific claim is made here. *)
From Coq Require Import List String Arith Lia.
From Buri Require Import Native NativeSimulation.
Import ListNotations.
Module EqualityInductionOracle.
Import Native.Native.
Section Oracle.
Variable ds : list (string * definition).
(* A literal name table, so concrete calls reduce without unfolding bodies. *)
Variable defined : string -> bool.
Hypothesis defined_lookup : forall s, defined s = match lookup ds s with Some _ => true | None => false end.
Definition step (rec : string -> list value -> option value) : env -> expr -> option value :=
 fix sem rho e := match e with
 | Lit v => Some v
 | Var s => rho s
 | If c a b => match sem rho c with
   | Some (Boolean false) => sem rho b | Some _ => sem rho a | None => None end
 | Let s a b => match sem rho a with Some v => sem (bind rho s v) b | None => None end
 | And a b => match sem rho a with
   | Some (Boolean false) => Some (Boolean false) | Some _ => sem rho b | None => None end
 | Or a b => match sem rho a with
   | Some (Boolean false) => sem rho b | Some v => Some v | None => None end
 | Call s es =>
   match (fix many es := match es with
     | [] => Some []
     | e::es => match sem rho e,many es with Some v,Some vs => Some (v::vs) | _,_ => None end end) es with
   | Some vs => if defined s then rec s vs
     else match external s vs with Returned v => Some v | _ => None end
   | None => None end
 end.
Fixpoint oracle (k : nat) (s : string) (vs : list value) : option value := match k with
 | O => None
 | S k => match lookup ds s with
   | Some d => if Nat.eqb (List.length (params d)) (List.length vs)
     then step (oracle k) (arguments (params d) vs) (body d) else None
   | None => None end end.
Definition below (r1 r2 : string -> list value -> option value) :=
 forall s vs v, r1 s vs = Some v -> r2 s vs = Some v.
(* Structural induction with a hypothesis for every call argument. *)
Definition expr_rect' (P : expr -> Prop)
 (lit : forall v, P (Lit v)) (var : forall s, P (Var s))
 (cond : forall c a b, P c -> P a -> P b -> P (If c a b))
 (lett : forall s a b, P a -> P b -> P (Let s a b))
 (conj : forall a b, P a -> P b -> P (And a b))
 (disj : forall a b, P a -> P b -> P (Or a b))
 (call : forall s es, (forall e, In e es -> P e) -> P (Call s es)) : forall e, P e :=
 fix F e := match e with
 | Lit v => lit v | Var s => var s
 | If c a b => cond c a b (F c) (F a) (F b)
 | Let s a b => lett s a b (F a) (F b)
 | And a b => conj a b (F a) (F b)
 | Or a b => disj a b (F a) (F b)
 | Call s es => call s es ((fix G es : forall e, In e es -> P e := match es with
   | [] => fun e (H : In e []) => match H with end
   | x::xs => fun e H => match H with
     | or_introl E => match E in _ = y return P y with eq_refl => F x end
     | or_intror H => G xs e H end end) es) end.
Lemma step_mono : forall r1 r2, below r1 r2 ->
 forall e rho v, step r1 rho e = Some v -> step r2 rho e = Some v.
Proof.
 intros r1 r2 B e; induction e using expr_rect'; intros rho w H0; cbn [step] in *; try exact H0.
 - destruct (step r1 rho e1) as [x|] eqn:E; [|discriminate]. rewrite (IHe1 _ _ E).
   destruct x; try (apply IHe3 + apply IHe2; exact H0). destruct b; [apply IHe2|apply IHe3]; exact H0.
 - destruct (step r1 rho e1) eqn:E; [|discriminate]. rewrite (IHe1 _ _ E). apply IHe2; exact H0.
 - destruct (step r1 rho e1) as [x|] eqn:E; [|discriminate]. rewrite (IHe1 _ _ E).
   destruct x; try (apply IHe2; exact H0). destruct b; [apply IHe2; exact H0|exact H0].
 - destruct (step r1 rho e1) as [x|] eqn:E; [|discriminate]. rewrite (IHe1 _ _ E).
   destruct x; try exact H0. destruct b; [exact H0|apply IHe2; exact H0].
 - match type of H0 with match ?m with _ => _ end = _ => destruct m as [vs|] eqn:M; [|discriminate] end.
   assert (A : forall xs ws, (forall e, In e xs -> In e es) ->
     (fix many es := match es with
     | [] => Some []
     | e::es => match step r1 rho e,many es with Some v,Some vs => Some (v::vs) | _,_ => None end end) xs = Some ws ->
     (fix many es := match es with
     | [] => Some []
     | e::es => match step r2 rho e,many es with Some v,Some vs => Some (v::vs) | _,_ => None end end) xs = Some ws).
   { induction xs as [|a xs IHa]; intros ws S W; [exact W|].
     destruct (step r1 rho a) eqn:E; [|discriminate].
     destruct ((fix many es := match es with
       | [] => Some []
       | e::es => match step r1 rho e,many es with Some v,Some vs => Some (v::vs) | _,_ => None end end) xs) eqn:R;
       [|discriminate].
     rewrite (H a (S a (or_introl eq_refl)) _ _ E).
     rewrite (IHa _ (fun e I => S e (or_intror I)) eq_refl); exact W. }
   rewrite (A es vs (fun e I => I) M). destruct (defined s); [apply B; exact H0|exact H0].
Qed.
Lemma oracle_succ : forall k, below (oracle k) (oracle (S k)).
Proof.
 induction k as [|k IH]; intros s vs v H; [discriminate|].
 cbn [oracle] in H |- *. destruct (lookup ds s); [|discriminate].
 destruct (Nat.eqb _ _); [|discriminate]. eapply step_mono; [exact IH|exact H].
Qed.
Lemma oracle_mono : forall k m, k <= m -> below (oracle k) (oracle m).
Proof.
 intros k m L; induction L; intros s vs v H; [exact H|].
 apply oracle_succ; apply IHL; exact H.
Qed.
Lemma many_oracle : forall r n rho es vs,
 (forall e v, eval n (lookup ds) rho e = Returned v -> step r rho e = Some v) ->
 NativeSimulation.many n (lookup ds) rho es = Values vs ->
 (fix many es := match es with
   | [] => Some []
   | e::es => match step r rho e,many es with Some v,Some vs => Some (v::vs) | _,_ => None end end) es = Some vs.
Proof.
 intros r n rho es; induction es as [|e es IH]; intros vs H M; cbn [NativeSimulation.many] in M.
 - inversion M; reflexivity.
 - destruct (eval n (lookup ds) rho e) eqn:E; try discriminate.
   destruct (NativeSimulation.many n (lookup ds) rho es) eqn:R; try discriminate.
   inversion M; subst. rewrite (H _ _ E), (IH _ H eq_refl). reflexivity.
Qed.
Theorem eval_oracle : forall n rho e v,
 eval n (lookup ds) rho e = Returned v -> step (oracle n) rho e = Some v.
Proof.
 induction n as [|n IH]; intros rho e v H; [discriminate|].
 assert (U : forall rho e v, eval n (lookup ds) rho e = Returned v -> step (oracle (S n)) rho e = Some v).
 { intros; eapply step_mono; [apply oracle_succ|apply IH; assumption]. }
 destruct e; cbn [eval] in H; cbn [step].
 - inversion H; reflexivity.
 - destruct (rho s); [inversion H; reflexivity|discriminate].
 - destruct (eval n (lookup ds) rho e1) as [[]| | |] eqn:E; try discriminate;
   rewrite (U _ _ _ E); try (apply U; exact H). destruct b; apply U; exact H.
 - destruct (eval n (lookup ds) rho e1) eqn:E; try discriminate.
   rewrite (U _ _ _ E). apply U; exact H.
 - destruct (eval n (lookup ds) rho e1) as [[]| | |] eqn:E; try discriminate;
   rewrite (U _ _ _ E); try (apply U; exact H). destruct b; [apply U; exact H|inversion H; reflexivity].
 - destruct (eval n (lookup ds) rho e1) as [[]| | |] eqn:E; try discriminate;
   rewrite (U _ _ _ E); try (inversion H; reflexivity). destruct b; [inversion H; reflexivity|apply U; exact H].
 - fold (NativeSimulation.many n (lookup ds) rho args) in H.
   destruct (NativeSimulation.many n (lookup ds) rho args) as [vs|r] eqn:M.
   + rewrite (many_oracle (oracle (S n)) n rho args vs (U rho) M).
     rewrite defined_lookup. destruct (lookup ds s) as [d|] eqn:D.
     * destruct (Nat.eqb _ _) eqn:Q; [|discriminate].
       cbn [oracle]. rewrite D, Q. apply IH; exact H.
     * destruct (external s vs); try discriminate; inversion H; reflexivity.
   + destruct r; try discriminate. exfalso; eapply NativeSimulation.many_no_returned_failure; exact M.
Qed.
End Oracle.
Lemma defined_names : forall ds s,
 existsb (String.eqb s) (map fst ds) = match lookup ds s with Some _ => true | None => false end.
Proof.
 induction ds as [|[n d] ds IH]; intro s; [reflexivity|]. cbn [map fst existsb lookup].
 destruct (String.eqb s n); [reflexivity|apply IH].
Qed.
Lemma oracle_unfold : forall ds defined k s vs d, lookup ds s = Some d ->
 oracle ds defined (S k) s vs = if Nat.eqb (List.length (params d)) (List.length vs)
   then step defined (oracle ds defined k) (arguments (params d) vs) (body d) else None.
Proof. intros; cbn [oracle]; rewrite H; reflexivity. Qed.
(* Inversion of one successful evaluation step, for symbolic execution. *)
Section Inversion.
Variable defined : string -> bool.
Variable rec : string -> list value -> option value.
Lemma inv_lit : forall rho w v, step defined rec rho (Lit w) = Some v -> v = w.
Proof. intros; cbn in H; congruence. Qed.
Lemma inv_var : forall rho s v, step defined rec rho (Var s) = Some v -> rho s = Some v.
Proof. intros; exact H. Qed.
Lemma inv_if : forall rho c a b v, step defined rec rho (If c a b) = Some v -> exists x,
 step defined rec rho c = Some x /\ step defined rec rho (match x with Boolean false => b | _ => a end) = Some v.
Proof.
 intros rho c a b v H; cbn [step] in H; fold (step defined rec) in H.
 destruct (step defined rec rho c) as [x|]; [|discriminate]. exists x; split; [reflexivity|].
 destruct x; try exact H. destruct b0; exact H.
Qed.
Lemma inv_let : forall rho s a b v, step defined rec rho (Let s a b) = Some v -> exists x,
 step defined rec rho a = Some x /\ step defined rec (bind rho s x) b = Some v.
Proof.
 intros rho s a b v H; cbn [step] in H; fold (step defined rec) in H.
 destruct (step defined rec rho a) as [x|]; [|discriminate]. exists x; split; [reflexivity|exact H].
Qed.
Lemma inv_and : forall rho a b v, step defined rec rho (And a b) = Some v -> exists x,
 step defined rec rho a = Some x /\
 match x with Boolean false => v = Boolean false | _ => step defined rec rho b = Some v end.
Proof.
 intros rho a b v H; cbn [step] in H; fold (step defined rec) in H.
 destruct (step defined rec rho a) as [x|]; [|discriminate]. exists x; split; [reflexivity|].
 destruct x; try exact H. destruct b0; [exact H|congruence].
Qed.
Lemma inv_or : forall rho a b v, step defined rec rho (Or a b) = Some v -> exists x,
 step defined rec rho a = Some x /\
 match x with Boolean false => step defined rec rho b = Some v | _ => v = x end.
Proof.
 intros rho a b v H; cbn [step] in H; fold (step defined rec) in H.
 destruct (step defined rec rho a) as [x|]; [|discriminate]. exists x; split; [reflexivity|].
 destruct x; try congruence. destruct b0; [congruence|exact H].
Qed.
Lemma inv_call : forall rho s es v, step defined rec rho (Call s es) = Some v -> exists vs,
 Forall2 (fun e w => step defined rec rho e = Some w) es vs /\
 (if defined s then rec s vs else match external s vs with Returned w => Some w | _ => None end) = Some v.
Proof.
 intros rho s es v H; cbn [step] in H; fold (step defined rec) in H.
 match type of H with match ?m with _ => _ end = _ => destruct m as [vs|] eqn:M; [|discriminate] end.
 exists vs; split; [|exact H]. clear H. revert vs M; induction es as [|e es IH]; intros vs M.
 - inversion M; constructor.
 - destruct (step defined rec rho e) eqn:E; [|discriminate].
   match type of M with match ?m with _ => _ end = _ => destruct m as [ws|] eqn:W; [|discriminate] end.
   inversion M; subst. constructor; [exact E|apply IH; reflexivity].
Qed.
Lemma forall2_cons : forall (P : expr -> value -> Prop) e es ws, Forall2 P (e::es) ws ->
 exists w ws', ws = w::ws' /\ P e w /\ Forall2 P es ws'.
Proof. intros; inversion H; subst; eauto. Qed.
Lemma forall2_nil : forall (P : expr -> value -> Prop) ws, Forall2 P [] ws -> ws = [].
Proof. intros; inversion H; reflexivity. Qed.
End Inversion.
End EqualityInductionOracle.
