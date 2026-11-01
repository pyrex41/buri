(* Fuel-independent facts about the existing Scheme syntax reader `decode`:
   the default (application) branch for every non-keyword head symbol, and
   monotonicity in the reader budget. No new syntax meaning is introduced. *)
From Coq Require Import List String Ascii Bool Arith Lia.
From Buri Require Import Native ObserverEffects.
Import ListNotations.
Module DecodeFacts.
Import Native.Native.
Open Scope string_scope.

Fixpoint dmany (d : value -> option expr) xs := match xs with
 | [] => Some []
 | x::xs => match d x, dmany d xs with Some e, Some es => Some (e::es) | _,_ => None end end.
Fixpoint dbindings (d : value -> option expr) body xs := match xs with
 | [] => Some body
 | x::xs => match elements x, dbindings d body xs with
   | Some [Symbol s;a], Some b => match d a with Some a => Some (Let s a b) | _ => None end
   | _,_ => None end end.
Fixpoint dcases (d : value -> option expr) cs := match cs with
 | [] => None
 | c::cs => match elements c with
   | Some [Boolean true;b] => match cs with [] => d b | _ => None end
   | Some [c;b] => match d c, d b, dcases d cs with
     | Some c, Some b, Some rest => Some (If c b rest) | _,_,_ => None end
   | _ => None end end.

(* The Scheme special-form heads recognised by `decode`. *)
Definition keywords := ["quote";"if";"let";"let*";"cond";"and";"or"].

Ltac split_string :=
  repeat match goal with
  | |- context [match ?s with EmptyString => _ | String _ _ => _ end] => is_var s; destruct s
  | |- context [match ?a with Ascii _ _ _ _ _ _ _ _ => _ end] => is_var a; destruct a
  | |- context [match ?b with true => _ | false => _ end] => is_var b; destruct b
  end.

Lemma many_inline : forall n xs,
 (fix many xs := match xs with
    | [] => Some [] | x::xs => match decode n x,many xs with Some e,Some es => Some (e::es) | _,_ => None end end) xs
 = dmany (decode n) xs.
Proof. intros n xs; induction xs as [|x xs IH]; [reflexivity|]. cbn [dmany]. rewrite <- IH. reflexivity. Qed.

(* Every list whose head is a non-keyword symbol is read as an application. *)
Theorem decode_default : forall n s t, ~ In s keywords ->
 decode (S n) (Pair (Symbol s) t) =
 match elements t with
 | Some xs => match dmany (decode n) xs with Some es => Some (Call s es) | None => None end
 | None => None end.
Proof.
 intros n s t K. cbn [decode elements].
 destruct (elements t) as [xs|]; [|reflexivity].
 rewrite <- many_inline. generalize (decode n) as d. intro d.
 split_string.
 all: try reflexivity.
 all: exfalso; apply K; cbn; tauto.
Qed.

Theorem decode_call : forall n f xs, ~ In f keywords ->
 decode (S n) (L (Symbol f :: xs)) =
 match dmany (decode n) xs with Some es => Some (Call f es) | None => None end.
Proof.
 intros n f xs K. change (L (Symbol f :: xs)) with (Pair (Symbol f) (L xs)).
 rewrite decode_default by exact K. rewrite ObserverEffects.elements_list. reflexivity.
Qed.

Ltac bad := match goal with H : _ = Some _ |- _ => cbn -[decode dmany dbindings dcases] in H; discriminate H end.

(* Simultaneous case analysis of H and the goal, transporting reader results
   from the smaller budget (in H) to the larger one (in the goal). *)
Ltac transport H M MM MB MC :=
  repeat (first
   [ match type of H with context [match ?y with _ => _ end] => is_var y; destruct y end
   | match type of H with context [match elements ?x with _ => _ end] => destruct (elements x) eqn:? end
   | match type of H with context [match dmany ?d ?x with _ => _ end] =>
       let E := fresh "E" in destruct (dmany d x) eqn:E; [try rewrite (MM _ _ E) in *|] end
   | match type of H with context [match dbindings ?d ?b ?x with _ => _ end] =>
       let E := fresh "E" in destruct (dbindings d b x) eqn:E; [try rewrite (MB _ _ _ E) in *|] end
   | match type of H with context [match dcases ?d ?x with _ => _ end] =>
       let E := fresh "E" in destruct (dcases d x) eqn:E; [try rewrite (MC _ _ E) in *|] end
   | match type of H with context [match decode ?n ?x with _ => _ end] =>
       let E := fresh "E" in destruct (decode n x) eqn:E; [try rewrite (M _ _ E) in *|] end
   | progress (cbn -[decode dmany dbindings dcases] in H) ]);
  try (cbn -[decode dmany dbindings dcases] in H; discriminate H); try exact H.

Section Mono.
Variables d d' : value -> option expr.
Hypothesis M : forall x e, d x = Some e -> d' x = Some e.
Lemma dmany_mono : forall xs es, dmany d xs = Some es -> dmany d' xs = Some es.
Proof.
 induction xs as [|x xs IH]; intros es H; [exact H|]. cbn [dmany] in H |- *.
 destruct (d x) eqn:E; [|bad]. destruct (dmany d xs) as [o|] eqn:R; [|bad].
 rewrite (M _ _ E), (IH o eq_refl). exact H.
Qed.
Lemma dbindings_mono : forall body xs e, dbindings d body xs = Some e -> dbindings d' body xs = Some e.
Proof.
 intro body; induction xs as [|x xs IH]; intros e H; [exact H|]. cbn [dbindings] in H |- *.
 destruct (dbindings d body xs) as [o|] eqn:R.
 - rewrite (IH o eq_refl). destruct (elements x) as [l|]; [|bad].
   destruct l as [|y [|a [|z zs]]]; try bad; try (destruct y; bad).
   destruct y; try bad. destruct (d a) eqn:E; [|bad]. rewrite (M _ _ E). exact H.
 - destruct (elements x) as [l|]; [|bad]. destruct l as [|y [|a [|z zs]]]; try bad; destruct y; bad.
Qed.
Lemma dcases_mono : forall cs e, dcases d cs = Some e -> dcases d' cs = Some e.
Proof.
 induction cs as [|c cs IH]; intros e H; [exact H|]. cbn [dcases] in H |- *.
 destruct (elements c) as [l|]; [|bad].
 destruct l as [|x [|b [|z zs]]]; try bad; try (destruct x as [| ? | ? | ? | ? ? | ? | [|] | ? ? | ? | ?]; bad).
 assert (G : match d x, d b, dcases d cs with
   | Some c, Some b, Some rest => Some (If c b rest) | _,_,_ => None end = Some e ->
   match d' x, d' b, dcases d' cs with
   | Some c, Some b, Some rest => Some (If c b rest) | _,_,_ => None end = Some e).
 { intro K. destruct (d x) eqn:E1; [|discriminate K]. destruct (d b) eqn:E2; [|discriminate K].
   destruct (dcases d cs) as [o|] eqn:R; [|discriminate K].
   rewrite (M _ _ E1), (M _ _ E2), (IH o eq_refl). exact K. }
 destruct x; try (apply G; exact H).
 destruct b0; [|apply G; exact H].
 destruct cs; [apply M; exact H|discriminate H].
Qed.
End Mono.

Lemma bindings_inline : forall n body xs,
 (fix bindings xs := match xs with
   | [] => Some body
   | x::xs => match elements x,bindings xs with
     | Some [Symbol s;a],Some b => match decode n a with Some a => Some (Let s a b) | _ => None end
     | _,_ => None end end) xs = dbindings (decode n) body xs.
Proof. intros n body xs; induction xs as [|x xs IH]; [reflexivity|]. cbn [dbindings]. rewrite <- IH. reflexivity. Qed.
Lemma cases_inline : forall n cs,
 (fix cases cs := match cs with
   | [] => None
   | c::cs => match elements c with
     | Some [Boolean true;b] => match cs with [] => decode n b | _ => None end
     | Some [c;b] => match decode n c,decode n b,cases cs with
       | Some c,Some b,Some rest => Some (If c b rest) | _,_,_ => None end
     | _ => None end end) cs = dcases (decode n) cs.
Proof. intros n cs; induction cs as [|c cs IH]; [reflexivity|]. cbn [dcases]. rewrite <- IH. reflexivity. Qed.

Ltac inline := repeat (rewrite many_inline in * || rewrite bindings_inline in * || rewrite cases_inline in *).

Lemma decode_step_mono : forall n m, (forall x e, decode n x = Some e -> decode m x = Some e) ->
 forall v e, decode (S n) v = Some e -> decode (S m) v = Some e.
Proof.
 intros n m IH v e H.
 pose proof (dmany_mono _ _ IH) as MM.
 pose proof (dbindings_mono _ _ IH) as MB.
 pose proof (dcases_mono _ _ IH) as MC.
 destruct v as [| s | | | | | | h t | |]; try exact H.
 destruct h as [| s | | | | | | | |];
  try (cbn [decode elements] in H |- *; destruct (elements t) as [l|]; [destruct l|]; exact H).
 destruct (in_dec string_dec s keywords) as [K|K].
 2:{ rewrite decode_default in H |- * by exact K.
     destruct (elements t) as [xs|]; [|discriminate H].
     destruct (dmany (decode n) xs) eqn:E; [|discriminate H]. rewrite (MM _ _ E). exact H. }
 cbn [keywords In] in K.
 destruct K as [K|[K|[K|[K|[K|[K|[K|[]]]]]]]]; subst s;
  cbn [decode elements] in H |- *; destruct (elements t) as [xs|]; try discriminate H; inline;
  transport H IH MM MB MC.
 - (* let*: the binding chain after the body has been decoded *)
   repeat match goal with Hq : elements _ = Some l |- _ => clear Hq end.
   revert e H. induction l as [|x l IHl]; intros e H; [exact H|].
   cbn -[decode] in H |- *.
   destruct (elements x) as [k|]; [|discriminate H].
   destruct k as [|y [|a [|z zs]]]; try (cbn -[decode] in H; discriminate H);
    destruct y; try (cbn -[decode] in H; discriminate H).
   match type of H with match ?t with Some _ => _ | None => _ end = _ =>
     destruct t as [o|] eqn:R; [|discriminate H] end.
   rewrite (IHl o eq_refl).
   destruct (decode n a) eqn:Ea; [|discriminate H]. rewrite (IH _ _ Ea). exact H.
 - exact (MC _ _ H).
Qed.

Theorem decode_succ : forall n v e, decode n v = Some e -> decode (S n) v = Some e.
Proof.
 induction n as [|n IH]; intros v e H; [discriminate H|].
 exact (decode_step_mono n (S n) IH v e H).
Qed.

Theorem decode_monotone : forall n m v e, n <= m -> decode n v = Some e -> decode m v = Some e.
Proof. intros n m v e L H; induction L; [exact H|apply decode_succ; exact IHL]. Qed.

Lemma dmany_monotone : forall n m xs es, n <= m -> dmany (decode n) xs = Some es -> dmany (decode m) xs = Some es.
Proof. intros; eapply dmany_mono; [|eassumption]. intros; eapply decode_monotone; eassumption. Qed.
End DecodeFacts.
