(* E2E-06 tail positions. The continuation grows only at `push`; tail
   positions (if/cond branches, let bodies, type bodies, closure bodies and the
   bodies of saturated named calls) are entered with the caller's continuation.
   trap-error bodies and the second operand of and/or are not tail positions in
   the agreed profile: their frames remain. A tail-recursive loop therefore
   diverges in bounded continuation space, even under a finite stack bound. *)
From Coq Require Import List ZArith NArith String Bool Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLMetatheory.
Import ListNotations.
Module KLTail.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLMetatheory.KLMetatheory.

Section Rules.
Variable P : profile.
Variables (rho : lenv) (k : list frame) (s : store).

Lemma tail_if : forall a b bv,
 next P (Cfg (Ret (VBool bv)) (KIf a b rho :: k) s) = MTau (Cfg (Eval rho (if bv then a else b)) k s).
Proof. intros; destruct bv; reflexivity. Qed.
Lemma tail_let : forall x b v,
 next P (Cfg (Ret v) (KLet x b rho :: k) s) = MTau (Cfg (Eval ((x, v) :: rho) b) k s).
Proof. reflexivity. Qed.
Lemma tail_cond : forall b rest,
 next P (Cfg (Ret (VBool true)) (KCond b rest rho :: k) s) = MTau (Cfg (Eval rho b) k s).
Proof. reflexivity. Qed.
Lemma tail_type : forall e, next P (Cfg (Eval rho (EType e)) k s) = MTau (Cfg (Eval rho e) k s).
Proof. reflexivity. Qed.
Lemma tail_closure : forall x b env a,
 apply_value P (VLam x b env) [a] k s = MTau (Cfg (Eval ((x, a) :: env) b) k s).
Proof. reflexivity. Qed.
Lemma tail_thaw : forall b env,
 apply_value P (VFrozen b env) [] k s = MTau (Cfg (Eval env b) k s).
Proof. reflexivity. Qed.
Lemma tail_named_call : forall g ps body args,
 lookup g (gfuns s) = Some (FUser ps body) -> List.length args = List.length ps ->
 call_named P g args k s = MTau (Cfg (Eval (combine ps args) body) k s).
Proof.
 intros g ps body args L E; unfold call_named; rewrite L, <- E, Nat.ltb_irrefl.
 rewrite skipn_all, firstn_all; reflexivity.
Qed.
Lemma tail_last_argument : forall g done v,
 next P (Cfg (Ret v) (KCallArgs g done [] rho :: k) s) = call_named P g (rev (v :: done)) k s.
Proof. reflexivity. Qed.

(* Non-tail positions keep a frame. *)
Lemma trap_body_not_tail : forall a h, stack_limit P = None ->
 next P (Cfg (Eval rho (ETrap a h)) k s) = MTau (Cfg (Eval rho a) (KTrap h rho :: k) s).
Proof. intros a h L; cbn; unfold push; rewrite L; reflexivity. Qed.
Lemma and_second_not_tail : forall b, stack_limit P = None ->
 next P (Cfg (Ret (VBool true)) (KAnd b rho :: k) s) = MTau (Cfg (Eval rho b) (KAndR :: k) s).
Proof. intros b L; cbn; unfold push; rewrite L; reflexivity. Qed.
End Rules.

(* Stack enforcement: pushing beyond the bound is a modeled resource failure. *)
Lemma stack_bound_enforced : forall P n f k c s, stack_limit P = Some n -> n <= List.length k ->
 push P f k c s = Cfg (Fail RStack) k s.
Proof.
 intros P n f k c s L H; unfold push; rewrite L.
 destruct (Nat.leb n (List.length k)) eqn:E; [reflexivity|apply Nat.leb_gt in E; lia].
Qed.

(* ---------- a tail-recursive loop diverges in bounded space ---------- *)
Section Loop.
Variables (W : Type) (O : W -> request -> response -> W -> Prop)
  (pending : W -> option env_event) (tick : W -> W) (P : profile).
Hypothesis quiet : forall w, pending w = None.
Variables (f x : name) (s : store) (k : list frame).
Hypothesis defined : lookup f (gfuns s) = Some (FUser [x] (ECall f [EVar x])).
Hypothesis room : match stack_limit P with Some n => List.length k < n | None => True end.

Definition loop_state (v : value) : config := Cfg (Eval [(x, v)] (ECall f [EVar x])) k s.

Lemma push_room : forall fr c, push P fr k c s = Cfg c (fr :: k) s.
Proof.
 intros fr c; unfold push; destruct (stack_limit P) as [n|]; [|reflexivity].
 destruct (Nat.leb n (List.length k)) eqn:E; [apply Nat.leb_le in E; lia|reflexivity].
Qed.

Lemma loop_cycle : forall v,
 next P (loop_state v) = MTau (Cfg (Eval [(x, v)] (EVar x)) (KCallArgs f [] [] [(x, v)] :: k) s) /\
 next P (Cfg (Eval [(x, v)] (EVar x)) (KCallArgs f [] [] [(x, v)] :: k) s) =
   MTau (Cfg (Ret v) (KCallArgs f [] [] [(x, v)] :: k) s) /\
 next P (Cfg (Ret v) (KCallArgs f [] [] [(x, v)] :: k) s) = MTau (loop_state v).
Proof.
 intro v; split; [|split].
 - unfold loop_state, next; cbn [ctl kont mem eval_move]. rewrite push_room; reflexivity.
 - unfold next; cbn. rewrite text_eqb_refl; reflexivity.
 - rewrite tail_last_argument. cbn [rev app].
   rewrite (tail_named_call P k s f [x] (ECall f [EVar x]) [v] defined eq_refl); reflexivity.
Qed.

Theorem loop_silent_forever : forall v w,
 silent_forever (cstep W O pending tick P) (loop_state v, w).
Proof.
 cofix CIH; intros v w. destruct (loop_cycle v) as [A [B C]].
 eapply sf_step; [apply cs_tau; [apply quiet|exact A]|].
 eapply sf_step; [apply cs_tau; [apply quiet|exact B]|].
 eapply sf_step; [apply cs_tau; [apply quiet|exact C]|].
 apply CIH.
Qed.

Theorem loop_diverges : forall v w,
 behaves (cstep W O pending tick P) (cfinal W P) (loop_state v, w) (Diverges []).
Proof. intros; eapply beh_div; [constructor|apply loop_silent_forever]. Qed.

(* Every configuration of the loop keeps the continuation within one frame of
   the caller's: the recursion does not consume stack. *)
Theorem loop_bounded_continuation : forall v,
 List.length (kont (loop_state v)) = List.length k /\
 List.length (kont (Cfg (Ret v) (KCallArgs f [] [] [(x, v)] :: k) s)) = S (List.length k).
Proof. intros; split; reflexivity. Qed.
End Loop.
End KLTail.
