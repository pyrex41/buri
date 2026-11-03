(* E2E-08: a contract calculus over the KLambda small-step semantics
   (KLSemantics.next / KLMetatheory). Assertions are shallow Rocq predicates on
   values, stores (heap, global values, global functions) and local IO traces
   in the Observation vocabulary. Three judgments are kept distinct by a mode:

   * Partial  -- partial correctness: never goes wrong, and every final state
                 reached satisfies the postcondition; divergence is allowed.
   * Total    -- total correctness: every execution, under every environment
                 response, reaches a final state satisfying the postcondition.
   * Always I -- a temporal safety property: partial correctness and, on every
                 execution prefix (including prefixes of diverging and
                 reacting executions), every emitted event satisfies I.

   The meaning of a triple is continuation-passing: for every continuation k
   whose obligations hold for the postconditions, the configuration
   Eval rho e on top of k satisfies the mode's semantic predicate G.
   Partial modes are step-indexed (safe n); total correctness is an inductive
   "every path terminates" predicate (term). Program resource failure is never
   merged with a result: it is the named outcome ResourceOut r, admitted only
   for the resources of the recorded policy RP, which must cover every limit
   the profile actually has (policy_ok). Going wrong is never admitted.

   Calls through the global function namespace are judged against a context of
   call contracts (cspec). User functions are validated by the recursion
   theorems (rec_partial, step-indexed; rec_total, an explicit nat measure
   that strictly decreases at every recursive call); every other contract in
   the context -- primitive or host -- is a named premise of the soundness
   theorems (ctx_at), never assumed. No completeness claim is made. *)
From Coq Require Import List ZArith NArith String Bool Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLMetatheory.
Import ListNotations.
Module ContractLogic.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics.

(* ---------- assertions ---------- *)
Definition pre := store -> Prop.
(* Postconditions see the result, the final store and the local trace of the
   evaluated expression (events in order, failed and partial writes included). *)
Definition post := value -> store -> trace -> Prop.
Definition epost := exn -> store -> trace -> Prop.
Definition observer := trace -> kl_outcome -> Prop.
Definition shift (t : trace) (Q : post) : post := fun v s u => Q v s (t ++ u).
Definition shiftE (t : trace) (E : epost) : epost := fun x s u => E x s (t ++ u).

Inductive mode := Partial | Total | Always (Iv : event -> Prop).
Definition inv_of (m : mode) : event -> Prop := match m with Always Iv => Iv | _ => fun _ => True end.

(* Explicit heap/global footprints (dynamic-frames style). A footprint names
   the heap locations, global values and global functions an expression may
   change; allocation of fresh locations is always allowed. *)
Record footprint := Footprint { fp_locs : list nat; fp_globals : list name; fp_funs : list name }.
Definition agree (fp : footprint) (s0 s : store) : Prop :=
 List.length (heap s0) <= List.length (heap s) /\
 (forall l, ~ In l (fp_locs fp) -> l < List.length (heap s0) -> nth_error (heap s) l = nth_error (heap s0) l) /\
 (forall x, ~ In x (fp_globals fp) -> lookup x (gvals s) = lookup x (gvals s0)) /\
 (forall x, ~ In x (fp_funs fp) -> lookup x (gfuns s) = lookup x (gfuns s0)).
(* An assertion is framed by fp when it cannot observe changes inside fp. *)
Definition stable (fp : footprint) (R : pre) := forall s0 s, agree fp s0 s -> R s0 -> R s.

(* Atomic expressions: one internal step to a value, no effect. *)
Definition atom (rho : lenv) (e : expr) : option value := match e with
 | ENum n => Some (VNum n) | EStr t => Some (VStr t) | ESym x => Some (VSym x)
 | EBool b => Some (VBool b) | ENil => Some VNil
 | EVar x => lookup x rho
 | ELam x b => Some (VLam x b rho) | EFreeze b => Some (VFrozen b rho)
 | _ => None end.

(* Argument lists are evaluated left to right into a call or an application. *)
Inductive target := TCall (f : name) | TApp (fv : value).
Definition tval (tg : target) : value := match tg with TCall f => VPartial f [] | TApp fv => fv end.
Definition aframe (tg : target) (done : list value) (rest : list expr) (rho : lenv) : frame :=
 match tg with TCall f => KCallArgs f done rest rho | TApp fv => KArgs fv done rest rho end.

(* A call contract for the global name c_name. The postconditions are
   relational: they also receive the arguments and the pre-call store. *)
Record cspec := CSpec {
 c_name : name;
 c_pre : list value -> store -> Prop;
 c_post : list value -> store -> post;
 c_exn : list value -> store -> epost }.

Section Logic.
Variable P : profile.
Variable RP : resource -> Prop.
(* The resource policy covers every limit the profile has. *)
Definition policy_ok := (stack_limit P <> None -> RP RStack) /\ (heap_limit P <> None -> RP RHeap).
Definition obs_ok (Phi : observer) := forall h r, RP r -> Phi h (ResourceOut r).

(* ---------- semantic predicates ---------- *)
Fixpoint safe (Iv : event -> Prop) (Phi : observer) (n : nat) (h : trace) (c : config) {struct n} : Prop :=
 match n with
 | O => True
 | S n => match next P c with
   | MTau c' => safe Iv Phi n h c'
   | MIO q kk => forall r, Iv (EvIO q r) /\ safe Iv Phi n (h ++ [EvIO q r]) (kk r)
   | MFinal o => Phi h o
   | MWrong _ => False end end.

Inductive term (Phi : observer) : trace -> config -> Prop :=
 | term_final h c o : next P c = MFinal o -> Phi h o -> term Phi h c
 | term_tau h c c' : next P c = MTau c' -> term Phi h c' -> term Phi h c
 | term_io h c q kk : next P c = MIO q kk -> (forall r, term Phi (h ++ [EvIO q r]) (kk r)) -> term Phi h c.

Definition G (m : mode) (Phi : observer) (n : nat) (h : trace) (c : config) : Prop :=
 match m with Total => term Phi h c | _ => safe (inv_of m) Phi n h c end.

Lemma safe_next : forall Iv Phi n h c1 c2, next P c1 = next P c2 -> safe Iv Phi n h c1 -> safe Iv Phi n h c2.
Proof. intros Iv Phi [|n] h c1 c2 E H; [exact I|]. cbn in *. rewrite <- E. exact H. Qed.
Lemma term_next : forall Phi h c1 c2, next P c1 = next P c2 -> term Phi h c1 -> term Phi h c2.
Proof.
 intros Phi h c1 c2 E H; inversion H; subst; rewrite E in *.
 - eapply term_final; eauto. - eapply term_tau; eauto. - eapply term_io; eauto.
Qed.
Lemma G_next : forall m Phi n h c1 c2, next P c1 = next P c2 -> G m Phi n h c1 -> G m Phi n h c2.
Proof. intros [] Phi n h c1 c2 E; cbn; [apply safe_next|apply term_next|apply safe_next]; exact E. Qed.

Lemma safe_S : forall Iv Phi n h c, safe Iv Phi (S n) h c = match next P c with
   | MTau c' => safe Iv Phi n h c'
   | MIO q kk => forall r, Iv (EvIO q r) /\ safe Iv Phi n (h ++ [EvIO q r]) (kk r)
   | MFinal o => Phi h o
   | MWrong _ => False end.
Proof. reflexivity. Qed.
Lemma safe_down : forall Iv Phi n h c, safe Iv Phi (S n) h c -> safe Iv Phi n h c.
Proof.
 intros Iv Phi n; induction n as [|n IH]; intros h c H; [exact I|].
 rewrite safe_S in H |- *. destruct (next P c).
 - apply IH; exact H.
 - intro r; destruct (H r) as [A B]; split; [exact A|apply IH; exact B].
 - exact H.
 - exact H.
Qed.
Lemma G_down : forall m Phi n h c, G m Phi (S n) h c -> G m Phi n h c.
Proof. intros [] Phi n h c; cbn; auto using safe_down. Qed.
Lemma G_le : forall m Phi j n h c, j <= n -> G m Phi n h c -> G m Phi j h c.
Proof. intros m Phi j n h c L; induction L; auto using G_down. Qed.

Lemma G_tau : forall m Phi n h c c', next P c = MTau c' -> G m Phi n h c' -> G m Phi (S n) h c.
Proof.
 intros [] Phi n h c c' E H; cbn in *; try (rewrite E; exact H).
 eapply term_tau; eauto.
Qed.
(* Backward internal steps preserve every judgment at the same index. *)
Lemma G_tau_same : forall m Phi n h c c', next P c = MTau c' -> G m Phi n h c' -> G m Phi n h c.
Proof. intros; apply G_down; eapply G_tau; eauto. Qed.
Lemma G_final : forall m Phi n h c o, next P c = MFinal o -> Phi h o -> G m Phi n h c.
Proof.
 intros [] Phi [|n] h c o E H; cbn; try exact I; try (rewrite E; exact H); eapply term_final; eauto.
Qed.
Lemma G_io : forall m Phi n h c q kk, next P c = MIO q kk ->
 (forall r, inv_of m (EvIO q r) /\ G m Phi n (h ++ [EvIO q r]) (kk r)) -> G m Phi (S n) h c.
Proof.
 intros [] Phi n h c q kk E H; cbn in *; try (rewrite E; exact H).
 eapply term_io; [exact E|]. intro r; exact (proj2 (H r)).
Qed.
Lemma G_fail : forall m Phi n h r k s, obs_ok Phi -> RP r -> G m Phi n h (Cfg (Fail r) k s).
Proof. intros; eapply G_final; [reflexivity|]. auto. Qed.
Lemma G_zero : forall m Phi h c, m <> Total -> G m Phi 0 h c.
Proof. intros [] Phi h c N; cbn; [exact I|contradiction|exact I]. Qed.

Lemma G_push : forall m Phi n h f k c s, policy_ok -> obs_ok Phi ->
 G m Phi n h (Cfg c (f :: k) s) -> G m Phi n h (push P f k c s).
Proof.
 intros m Phi n h f k c s [PS _] O H; unfold push. destruct (stack_limit P) as [l|] eqn:SL; [|exact H].
 destruct (Nat.leb l (List.length k)); [|exact H].
 apply G_fail; [exact O|]. apply PS; try rewrite SL; discriminate.
Qed.

(* ---------- triples ---------- *)
Definition conts m Phi n h k (Q : post) (E : epost) :=
 (forall v s t, Q v s t -> G m Phi n (h ++ t) (Cfg (Ret v) k s)) /\
 (forall x s t, E x s t -> G m Phi n (h ++ t) (Cfg (Throw x) k s)).
Definition sem_at m n (Pre : pre) (start : list frame -> store -> config) (Q : post) (E : epost) :=
 forall j, j <= n -> forall Phi h k s, obs_ok Phi -> Pre s -> conts m Phi j h k Q E -> G m Phi j h (start k s).
Definition triple_at m n Pre rho e Q E := sem_at m n Pre (fun k s => Cfg (Eval rho e) k s) Q E.
Definition app_at m n fv vs Pre Q E := sem_at m n Pre (fun k s => Cfg (Ret fv) (KApply vs :: k) s) Q E.
Definition args_at m n (Pre : pre) rho (es : list expr) tg (Qs : list value -> store -> trace -> Prop) (E : epost) :=
 match es with
 | [] => False
 | a :: rest => forall j, j <= n -> forall Phi h k s done, obs_ok Phi -> Pre s ->
   (forall vs s' t, Qs vs s' t -> G m Phi j (h ++ t) (Cfg (Ret (tval tg)) (KApply (rev done ++ vs) :: k) s')) ->
   (forall x s' t, E x s' t -> G m Phi j (h ++ t) (Cfg (Throw x) k s')) ->
   G m Phi j h (Cfg (Eval rho a) (aframe tg done rest rho :: k) s) end.
(* Index-free validity. In the partial modes "for all n" is partial
   correctness; in Total mode G does not depend on n. *)
Definition triple m Pre rho e Q E := forall n, triple_at m n Pre rho e Q E.
Definition app_sem m fv vs Pre Q E := forall n, app_at m n fv vs Pre Q E.

Definition call_at m n (c : cspec) := forall vs s0,
 app_at m n (VPartial (c_name c) []) vs (fun s => s = s0 /\ c_pre c vs s0) (c_post c vs s0) (c_exn c vs s0).
Definition ctx_at m n (Gamma : list cspec) := forall c, In c Gamma -> call_at m n c.

Lemma sem_down : forall m n j Pre start Q E, j <= n -> sem_at m n Pre start Q E -> sem_at m j Pre start Q E.
Proof. intros m n j Pre start Q E L H i Li; apply H; lia. Qed.
Lemma ctx_down : forall m n j Gamma, j <= n -> ctx_at m n Gamma -> ctx_at m j Gamma.
Proof. intros m n j Gamma L H c I vs s0; eapply sem_down; [exact L|apply H; exact I]. Qed.
Lemma conts_weaken : forall m Phi n h k Q Q' E E', conts m Phi n h k Q E ->
 (forall v s t, Q' v s t -> Q v s t) -> (forall x s t, E' x s t -> E x s t) -> conts m Phi n h k Q' E'.
Proof. intros m Phi n h k Q Q' E E' [A B] HQ HE; split; intros; [apply A|apply B]; auto. Qed.
Lemma sem_conseq : forall m n Pre Pre' start Q Q' E E', sem_at m n Pre' start Q' E' ->
 (forall s, Pre s -> Pre' s) -> (forall v s t, Q' v s t -> Q v s t) -> (forall x s t, E' x s t -> E x s t) ->
 sem_at m n Pre start Q E.
Proof. intros m n Pre Pre' start Q Q' E E' H HP HQ HE j L Phi h k s O Ps C; apply H; auto. eapply conts_weaken; eauto. Qed.

(* ---------- machine facts used by the rules ---------- *)
Lemma atom_next : forall rho e v k s, atom rho e = Some v -> next P (Cfg (Eval rho e) k s) = MTau (Cfg (Ret v) k s).
Proof. intros rho e v k s A; destruct e; cbn in A |- *; try discriminate; try (injection A as <-; reflexivity). rewrite A; reflexivity. Qed.
Lemma throw_next : forall x f k s, (forall hd rho, f <> KTrap hd rho) -> next P (Cfg (Throw x) (f :: k) s) = MTau (Cfg (Throw x) k s).
Proof. intros x f k s N; destruct f; cbn; try reflexivity. exfalso; eapply N; reflexivity. Qed.
Lemma aframe_not_trap : forall tg done rest rho hd rho', aframe tg done rest rho <> KTrap hd rho'.
Proof. intros [] *; discriminate. Qed.
Lemma aframe_last : forall tg done rho v k s,
 next P (Cfg (Ret v) (aframe tg done [] rho :: k) s) = next P (Cfg (Ret (tval tg)) (KApply (rev done ++ [v]) :: k) s).
Proof. intros [] *; reflexivity. Qed.
Lemma aframe_more : forall tg done a rest rho v k s,
 next P (Cfg (Ret v) (aframe tg done (a :: rest) rho :: k) s) = MTau (Cfg (Eval rho a) (aframe tg (v :: done) rest rho :: k) s).
Proof. intros [] *; reflexivity. Qed.
Lemma partial_app_next : forall f prev vs k s,
 next P (Cfg (Ret (VPartial f prev)) (KApply vs :: k) s) = next P (Cfg (Ret (VPartial f [])) (KApply (prev ++ vs) :: k) s).
Proof. reflexivity. Qed.

Ltac conts_split := match goal with C : conts _ _ _ _ _ _ _ |- _ => destruct C as [HQ HE] end.
Ltac app_nil h := rewrite <- (app_nil_r h) at 1.

(* ---------- the calculus ---------- *)
Inductive deriv (m : mode) (Gamma : list cspec) : pre -> lenv -> expr -> post -> epost -> Prop :=
 | r_val rho e v Q E : atom rho e = Some v -> deriv m Gamma (fun s => Q v s []) rho e Q E
 | r_unbound rho x Q E : lookup x rho = None -> deriv m Gamma (fun s => E (XUnboundVar x) s []) rho (EVar x) Q E
 | r_let Pre rho x a b R Q E : deriv m Gamma Pre rho a R E ->
     (forall v s1 t1, R v s1 t1 -> deriv m Gamma (fun s => s = s1) ((x, v) :: rho) b (shift t1 Q) (shiftE t1 E)) ->
     deriv m Gamma Pre rho (ELet x a b) Q E
 | r_if Pre rho c a b R Q E : deriv m Gamma Pre rho c R E ->
     (forall s1 t1, R (VBool true) s1 t1 -> deriv m Gamma (fun s => s = s1) rho a (shift t1 Q) (shiftE t1 E)) ->
     (forall s1 t1, R (VBool false) s1 t1 -> deriv m Gamma (fun s => s = s1) rho b (shift t1 Q) (shiftE t1 E)) ->
     (forall v s1 t1, R v s1 t1 -> (forall bb, v <> VBool bb) -> E XNotBoolean s1 t1) ->
     deriv m Gamma Pre rho (EIf c a b) Q E
 | r_type Pre rho a Q E : deriv m Gamma Pre rho a Q E -> deriv m Gamma Pre rho (EType a) Q E
 | r_defun rho f ps b Q E : nodupb ps = true ->
     deriv m Gamma (fun s => Q (VSym f) (Store (heap s) (gvals s) ((f, FUser ps b) :: gfuns s)) []) rho (EDefun f ps b) Q E
 | r_defun_bad rho f ps b Q E : nodupb ps = false ->
     deriv m Gamma (fun s => E XBadDefinition s []) rho (EDefun f ps b) Q E
 (* trap-error: body exceptions R are handled by evaluating the handler and
    applying its value to the exception value. *)
 | r_trap Pre rho a hd R Rh Q E : deriv m Gamma Pre rho a Q R ->
     (forall x s1 t1, R x s1 t1 -> deriv m Gamma (fun s => s = s1) rho hd (Rh x t1) (shiftE t1 E)) ->
     (forall x s1 t1 hv s2 t2, R x s1 t1 -> Rh x t1 hv s2 t2 ->
        appj m Gamma hv [VExn x] (fun s => s = s2) (shift (t1 ++ t2) Q) (shiftE (t1 ++ t2) E)) ->
     deriv m Gamma Pre rho (ETrap a hd) Q E
 | r_app Pre rho hd args R Qs Q E : deriv m Gamma Pre rho hd R E ->
     (forall fv s1 t1, R fv s1 t1 -> dargs m Gamma (fun s => s = s1) rho args (TApp fv) (Qs fv t1) (shiftE t1 E)) ->
     (forall fv s1 t1 vs s2 t2, R fv s1 t1 -> Qs fv t1 vs s2 t2 ->
        appj m Gamma fv vs (fun s => s = s2) (shift (t1 ++ t2) Q) (shiftE (t1 ++ t2) E)) ->
     deriv m Gamma Pre rho (EApp hd args) Q E
 | r_app0 Pre rho hd R Q E : deriv m Gamma Pre rho hd R E ->
     (forall fv s1 t1, R fv s1 t1 -> appj m Gamma fv [] (fun s => s = s1) (shift t1 Q) (shiftE t1 E)) ->
     deriv m Gamma Pre rho (EApp hd []) Q E
 | r_call Pre rho f args Qs Q E : dargs m Gamma Pre rho args (TCall f) Qs E ->
     (forall vs s1 t1, Qs vs s1 t1 -> appj m Gamma (VPartial f []) vs (fun s => s = s1) (shift t1 Q) (shiftE t1 E)) ->
     deriv m Gamma Pre rho (ECall f args) Q E
 | r_call0 Pre rho f Q E : appj m Gamma (VPartial f []) [] Pre Q E -> deriv m Gamma Pre rho (ECall f []) Q E
 | r_conseq Pre Pre' rho e Q Q' E E' : deriv m Gamma Pre' rho e Q' E' -> (forall s, Pre s -> Pre' s) ->
     (forall v s t, Q' v s t -> Q v s t) -> (forall x s t, E' x s t -> E x s t) -> deriv m Gamma Pre rho e Q E
 | r_exists (A : Type) (Pre : A -> pre) rho e Q E : (forall a, deriv m Gamma (Pre a) rho e Q E) ->
     deriv m Gamma (fun s => exists a, Pre a s) rho e Q E
 | r_frame Pre rho e Q E fp R :
     (forall s0, deriv m Gamma (fun s => s = s0 /\ Pre s) rho e
        (fun v s t => Q v s t /\ agree fp s0 s) (fun x s t => E x s t /\ agree fp s0 s)) ->
     stable fp R ->
     deriv m Gamma (fun s => Pre s /\ R s) rho e (fun v s t => Q v s t /\ R s) (fun x s t => E x s t /\ R s)
with dargs (m : mode) (Gamma : list cspec) : pre -> lenv -> list expr -> target -> (list value -> store -> trace -> Prop) -> epost -> Prop :=
 | da_one Pre rho a tg Qs E : deriv m Gamma Pre rho a (fun v => Qs [v]) E -> dargs m Gamma Pre rho [a] tg Qs E
 | da_cons Pre rho a a' rest tg R Qs E : deriv m Gamma Pre rho a R E ->
     (forall v s1 t1, R v s1 t1 -> dargs m Gamma (fun s => s = s1) rho (a' :: rest) tg
        (fun vs s2 t2 => Qs (v :: vs) s2 (t1 ++ t2)) (shiftE t1 E)) ->
     dargs m Gamma Pre rho (a :: a' :: rest) tg Qs E
with appj (m : mode) (Gamma : list cspec) : value -> list value -> pre -> post -> epost -> Prop :=
 (* a semantically established application fact (e.g. a closure parameter) *)
 | aj_sem fv vs Pre Q E : app_sem m fv vs Pre Q E -> appj m Gamma fv vs Pre Q E
 (* a call that saturates a contract of the context *)
 | aj_ctx c prev vs Pre Q E : In c Gamma ->
     (forall s, Pre s -> c_pre c (prev ++ vs) s /\
        (forall v s' t, c_post c (prev ++ vs) s v s' t -> Q v s' t) /\
        (forall x s' t, c_exn c (prev ++ vs) s x s' t -> E x s' t)) ->
     appj m Gamma (VPartial (c_name c) prev) vs Pre Q E
 (* currying: too few arguments for the current binding *)
 | aj_partial f prev vs Pre Q E :
     (forall s, Pre s -> exists d, lookup f (gfuns s) = Some d /\ List.length (prev ++ vs) < fun_arity d /\
        Q (VPartial f (prev ++ vs)) s []) ->
     appj m Gamma (VPartial f prev) vs Pre Q E
 | aj_lam x b rho' a Pre Q E : deriv m Gamma Pre ((x, a) :: rho') b Q E -> appj m Gamma (VLam x b rho') [a] Pre Q E
 | aj_frozen b rho' Pre Q E : deriv m Gamma Pre rho' b Q E -> appj m Gamma (VFrozen b rho') [] Pre Q E.

Scheme deriv_mut := Induction for deriv Sort Prop
 with dargs_mut := Induction for dargs Sort Prop
 with appj_mut := Induction for appj Sort Prop.
Combined Scheme deriv_combined from deriv_mut, dargs_mut, appj_mut.

(* ---------- soundness of every rule ---------- *)
Section Soundness.
Hypothesis PO : policy_ok.

Theorem soundness : forall m Gamma n, ctx_at m n Gamma ->
 (forall Pre rho e Q E, deriv m Gamma Pre rho e Q E -> triple_at m n Pre rho e Q E) /\
 (forall Pre rho es tg Qs E, dargs m Gamma Pre rho es tg Qs E -> args_at m n Pre rho es tg Qs E) /\
 (forall fv vs Pre Q E, appj m Gamma fv vs Pre Q E -> app_at m n fv vs Pre Q E).
Proof.
 intros m Gamma n Hctx.
 apply (deriv_combined m Gamma
   (fun Pre rho e Q E _ => triple_at m n Pre rho e Q E)
   (fun Pre rho es tg Qs E _ => args_at m n Pre rho es tg Qs E)
   (fun fv vs Pre Q E _ => app_at m n fv vs Pre Q E)).
 - (* r_val *) intros rho e v Q E A j L Phi h k s O Ps C; conts_split.
   eapply G_tau_same; [apply atom_next; exact A|]. app_nil h. apply HQ; exact Ps.
 - (* r_unbound *) intros rho x Q E A j L Phi h k s O Ps C; conts_split.
   eapply G_tau_same; [cbn; rewrite A; reflexivity|]. app_nil h. apply HE; exact Ps.
 - (* r_let *) intros Pre rho x a b R Q E _ IHa _ IHb j L Phi h k s O Ps C; conts_split.
   eapply G_tau_same; [reflexivity|]. apply G_push; [exact PO|exact O|].
   apply (IHa j L Phi h (KLet x b rho :: k) s O Ps). split.
   + intros v s1 t1 Rv. eapply G_tau_same; [reflexivity|].
     apply (IHb v s1 t1 Rv j L Phi (h ++ t1) k s1 O eq_refl). split.
     * intros w s2 t2 Hw. rewrite <- app_assoc. apply HQ; exact Hw.
     * intros y s2 t2 Hy. rewrite <- app_assoc. apply HE; exact Hy.
   + intros y s1 t1 Hy. eapply G_tau_same; [reflexivity|]. apply HE; exact Hy.
 - (* r_if *) intros Pre rho c a b R Q E _ IHc _ IHa _ IHb NB j L Phi h k s O Ps C; conts_split.
   eapply G_tau_same; [reflexivity|]. apply G_push; [exact PO|exact O|].
   apply (IHc j L Phi h (KIf a b rho :: k) s O Ps). split.
   + intros v s1 t1 Rv.
     assert (Cls : v = VBool true \/ v = VBool false \/ (forall bb, v <> VBool bb))
       by (destruct v; try (right; right; intros bb; discriminate); destruct b0; auto).
     destruct Cls as [->|[->|Nb]].
     * eapply G_tau_same; [reflexivity|]. apply (IHa s1 t1 Rv j L Phi (h ++ t1) k s1 O eq_refl). split.
       -- intros w s2 t2 Hw. rewrite <- app_assoc. apply HQ; exact Hw.
       -- intros y s2 t2 Hy. rewrite <- app_assoc. apply HE; exact Hy.
     * eapply G_tau_same; [reflexivity|]. apply (IHb s1 t1 Rv j L Phi (h ++ t1) k s1 O eq_refl). split.
       -- intros w s2 t2 Hw. rewrite <- app_assoc. apply HQ; exact Hw.
       -- intros y s2 t2 Hy. rewrite <- app_assoc. apply HE; exact Hy.
     * eapply G_tau_same.
       { cbn. destruct v; try reflexivity. exfalso; eapply Nb; reflexivity. }
       apply HE. eapply NB; eauto.
   + intros y s1 t1 Hy. eapply G_tau_same; [reflexivity|]. apply HE; exact Hy.
 - (* r_type *) intros Pre rho a Q E _ IH j L Phi h k s O Ps C.
   eapply G_tau_same; [reflexivity|]. apply IH; auto.
 - (* r_defun *) intros rho f ps b Q E N j L Phi h k s O Ps C; conts_split.
   eapply G_tau_same; [cbn; rewrite N; reflexivity|]. app_nil h. apply HQ; exact Ps.
 - (* r_defun_bad *) intros rho f ps b Q E N j L Phi h k s O Ps C; conts_split.
   eapply G_tau_same; [cbn; rewrite N; reflexivity|]. app_nil h. apply HE; exact Ps.
 - (* r_trap *) intros Pre rho a hd R Rh Q E _ IHa _ IHh _ IHapp j L Phi h k s O Ps C; conts_split.
   eapply G_tau_same; [reflexivity|]. apply G_push; [exact PO|exact O|].
   apply (IHa j L Phi h (KTrap hd rho :: k) s O Ps). split.
   + intros v s1 t1 Hv. eapply G_tau_same; [reflexivity|]. apply HQ; exact Hv.
   + intros x s1 t1 Hx. eapply G_tau_same; [reflexivity|].
     apply (IHh x s1 t1 Hx j L Phi (h ++ t1) (KApply [VExn x] :: k) s1 O eq_refl). split.
     * intros hv s2 t2 Hh. apply (IHapp x s1 t1 hv s2 t2 Hx Hh j L Phi ((h ++ t1) ++ t2) k s2 O eq_refl). split.
       -- intros w s3 t3 Hw. unfold shift in Hw; repeat rewrite <- app_assoc in Hw; repeat rewrite <- app_assoc. apply HQ; exact Hw.
       -- intros y s3 t3 Hy. unfold shiftE in Hy; repeat rewrite <- app_assoc in Hy; repeat rewrite <- app_assoc. apply HE; exact Hy.
     * intros y s2 t2 Hy. eapply G_tau_same; [reflexivity|]. rewrite <- app_assoc. apply HE; exact Hy.
 - (* r_app *) intros Pre rho hd args R Qs Q E _ IHh _ IHargs _ IHapp j L Phi h k s O Ps C; conts_split.
   eapply G_tau_same; [reflexivity|]. apply G_push; [exact PO|exact O|].
   apply (IHh j L Phi h (KHead args rho :: k) s O Ps). split.
   + intros fv s1 t1 Rf. pose proof (IHargs fv s1 t1 Rf) as IA.
     destruct args as [|a rest]; [contradiction|]. cbn [args_at] in IA.
     eapply G_tau_same; [reflexivity|].
     apply (IA j L Phi (h ++ t1) k s1 [] O eq_refl).
     * intros vs s2 t2 Hq. apply (IHapp fv s1 t1 vs s2 t2 Rf Hq j L Phi ((h ++ t1) ++ t2) k s2 O eq_refl). split.
       -- intros w s3 t3 Hw. unfold shift in Hw; repeat rewrite <- app_assoc in Hw; repeat rewrite <- app_assoc. apply HQ; exact Hw.
       -- intros y s3 t3 Hy. unfold shiftE in Hy; repeat rewrite <- app_assoc in Hy; repeat rewrite <- app_assoc. apply HE; exact Hy.
     * intros y s2 t2 Hy. rewrite <- app_assoc. apply HE; exact Hy.
   + intros y s1 t1 Hy. eapply G_tau_same; [reflexivity|]. apply HE; exact Hy.
 - (* r_app0 *) intros Pre rho hd R Q E _ IHh _ IHapp j L Phi h k s O Ps C; conts_split.
   eapply G_tau_same; [reflexivity|]. apply G_push; [exact PO|exact O|].
   apply (IHh j L Phi h (KHead [] rho :: k) s O Ps). split.
   + intros fv s1 t1 Rf. eapply G_next; [|apply (IHapp fv s1 t1 Rf j L Phi (h ++ t1) k s1 O eq_refl)]; [reflexivity|]. split.
     * intros w s2 t2 Hw. rewrite <- app_assoc. apply HQ; exact Hw.
     * intros y s2 t2 Hy. rewrite <- app_assoc. apply HE; exact Hy.
   + intros y s1 t1 Hy. eapply G_tau_same; [reflexivity|]. apply HE; exact Hy.
 - (* r_call *) intros Pre rho f args Qs Q E _ IHargs _ IHapp j L Phi h k s O Ps C; conts_split.
   destruct args as [|a rest]; [contradiction|]. cbn [args_at] in IHargs.
   eapply G_tau_same; [reflexivity|]. apply G_push; [exact PO|exact O|].
   apply (IHargs j L Phi h k s [] O Ps).
   + intros vs s1 t1 Hq. apply (IHapp vs s1 t1 Hq j L Phi (h ++ t1) k s1 O eq_refl). split.
     * intros w s2 t2 Hw. rewrite <- app_assoc. apply HQ; exact Hw.
     * intros y s2 t2 Hy. rewrite <- app_assoc. apply HE; exact Hy.
   + exact HE.
 - (* r_call0 *) intros Pre rho f Q E _ IHapp j L Phi h k s O Ps C.
   eapply G_next; [|apply (IHapp j L Phi h k s O Ps C)]. reflexivity.
 - (* r_conseq *) intros Pre Pre' rho e Q Q' E E' _ IH HP HQ HE. eapply sem_conseq; eauto.
 - (* r_exists *) intros A Pre rho e Q E _ IH j L Phi h k s O [a Ps] C. eapply IH; eauto.
 - (* r_frame *) intros Pre rho e Q E fp R _ IH St j L Phi h k s O [Ps Rs] C.
   apply (IH s j L Phi h k s O (conj eq_refl Ps)).
   eapply conts_weaken; [exact C| |]; cbn; intros ? s' t [H1 H2]; split; [exact H1| |exact H1|]; eapply St; eauto.
 - (* da_one *) intros Pre rho a tg Qs E _ IH j L Phi h k s done O Ps HQ HE.
   apply (IH j L Phi h (aframe tg done [] rho :: k) s O Ps). split.
   + intros v s1 t1 Hq. eapply G_next; [symmetry; apply aframe_last|]. apply HQ; exact Hq.
   + intros y s1 t1 Hy. eapply G_tau_same; [apply throw_next; intros; apply aframe_not_trap|]. apply HE; exact Hy.
 - (* da_cons *) intros Pre rho a a' rest tg R Qs E _ IHa _ IHr j L Phi h k s done O Ps HQ HE.
   apply (IHa j L Phi h (aframe tg done (a' :: rest) rho :: k) s O Ps). split.
   + intros v s1 t1 Rv. eapply G_tau_same; [apply aframe_more|].
     pose proof (IHr v s1 t1 Rv) as IR. cbn [args_at] in IR.
     apply (IR j L Phi (h ++ t1) k s1 (v :: done) O eq_refl).
     * intros vs s2 t2 Hq. rewrite <- app_assoc.
       replace (rev (v :: done) ++ vs) with (rev done ++ v :: vs) by (cbn; rewrite <- app_assoc; reflexivity).
       apply HQ; exact Hq.
     * intros y s2 t2 Hy. rewrite <- app_assoc. apply HE; exact Hy.
   + intros y s1 t1 Hy. eapply G_tau_same; [apply throw_next; intros; apply aframe_not_trap|]. apply HE; exact Hy.
 - (* aj_sem *) intros fv vs Pre Q E H. apply H.
 - (* aj_ctx *) intros c prev vs Pre Q E I H j L Phi h k s O Ps C.
   destruct (H s Ps) as (Hpre & HQ' & HE').
   eapply G_next; [symmetry; apply partial_app_next|].
   apply (Hctx c I (prev ++ vs) s j L Phi h k s O (conj eq_refl Hpre)).
   eapply conts_weaken; [exact C|exact HQ'|exact HE'].
 - (* aj_partial *) intros f prev vs Pre Q E H j L Phi h k s O Ps C; conts_split.
   destruct (H s Ps) as (d & Lk & Lt & Hq).
   eapply G_tau_same.
   { cbn [next ctl kont mem ret_move apply_value]. unfold call_named. rewrite Lk.
     destruct d as [p|ps b]; cbn [fun_arity] in Lt; apply Nat.ltb_lt in Lt; rewrite Lt; reflexivity. }
   app_nil h. apply HQ; exact Hq.
 - (* aj_lam *) intros x b rho' a Pre Q E _ IH j L Phi h k s O Ps C.
   eapply G_tau_same; [reflexivity|]. apply IH; auto.
 - (* aj_frozen *) intros b rho' Pre Q E _ IH j L Phi h k s O Ps C.
   eapply G_tau_same; [reflexivity|]. apply IH; auto.
Qed.

Corollary deriv_sound : forall m Gamma Pre rho e Q E, (forall n, ctx_at m n Gamma) ->
 deriv m Gamma Pre rho e Q E -> triple m Pre rho e Q E.
Proof. intros m Gamma Pre rho e Q E H D n. exact (proj1 (soundness m Gamma n (H n)) _ _ _ _ _ D). Qed.
Corollary appj_sound : forall m Gamma fv vs Pre Q E, (forall n, ctx_at m n Gamma) ->
 appj m Gamma fv vs Pre Q E -> app_sem m fv vs Pre Q E.
Proof. intros m Gamma fv vs Pre Q E H D n. exact (proj2 (proj2 (soundness m Gamma n (H n))) _ _ _ _ _ D). Qed.

(* ---------- recursion ---------- *)
Record fdef := FDef { fd_spec : cspec; fd_params : list name; fd_body : expr }.
(* Every admissible call finds this body under this name with exact arity. *)
Definition binds (F : fdef) := forall vs s, c_pre (fd_spec F) vs s ->
 lookup (c_name (fd_spec F)) (gfuns s) = Some (FUser (fd_params F) (fd_body F)) /\
 List.length vs = List.length (fd_params F).

Lemma body_next : forall F vs s k, binds F -> c_pre (fd_spec F) vs s ->
 next P (Cfg (Ret (VPartial (c_name (fd_spec F)) [])) (KApply vs :: k) s) =
 MTau (Cfg (Eval (combine (fd_params F) vs) (fd_body F)) k s).
Proof.
 intros F vs s k B Hp. destruct (B vs s Hp) as [Lk Ln].
 cbn [next ctl kont mem ret_move apply_value app]. unfold call_named. rewrite Lk.
 rewrite Ln, Nat.ltb_irrefl. rewrite <- Ln, skipn_all, firstn_all. reflexivity.
Qed.

Lemma body_call : forall m n F, binds F ->
 (forall vs s0, c_pre (fd_spec F) vs s0 ->
    triple_at m n (fun s => s = s0) (combine (fd_params F) vs) (fd_body F)
      (c_post (fd_spec F) vs s0) (c_exn (fd_spec F) vs s0)) ->
 call_at m (S n) (fd_spec F).
Proof.
 intros m n F B H vs s0 j L Phi h k s O [<- Hp] C.
 destruct j as [|j].
 - eapply G_tau_same; [apply body_next; eauto|]. apply (H vs s Hp 0 ltac:(lia) Phi h k s O eq_refl C).
 - eapply G_tau; [apply body_next; eauto|]. apply (H vs s Hp j ltac:(lia) Phi h k s O eq_refl).
   destruct C as [A Bc]; split; intros; apply G_down; auto.
Qed.

Definition body_ok m Gamma (F : fdef) := forall vs s0, c_pre (fd_spec F) vs s0 ->
 deriv m Gamma (fun s => s = s0) (combine (fd_params F) vs) (fd_body F)
   (c_post (fd_spec F) vs s0) (c_exn (fd_spec F) vs s0).

(* Partial correctness of mutually recursive user functions: the bodies are
   derived assuming the contracts of all of them (and of the external
   context), by induction on the step index. No measure is needed, and
   none is claimed: the conclusion permits divergence. *)
Theorem rec_partial : forall m Fs Gx, m <> Total ->
 (forall n, ctx_at m n Gx) -> Forall binds Fs ->
 Forall (body_ok m (map fd_spec Fs ++ Gx)) Fs ->
 forall n, ctx_at m n (map fd_spec Fs ++ Gx).
Proof.
 intros m Fs Gx NT HX HB HO n; induction n as [|n IH]; intros c I.
 - apply in_app_or in I; destruct I as [I|I]; [|apply HX; exact I].
   intros vs s0 j L Phi h k s O _ _. replace j with 0 by lia. apply G_zero; exact NT.
 - apply in_app_or in I; destruct I as [I|I]; [|apply HX; exact I].
   apply in_map_iff in I; destruct I as [F [<- IF]].
   apply body_call; [exact (proj1 (Forall_forall _ _) HB F IF)|].
   intros vs s0 Hp. exact (proj1 (soundness m _ n IH) _ _ _ _ _ (proj1 (Forall_forall _ _) HO F IF vs s0 Hp)).
Qed.

(* Total correctness: each function carries an explicit nat measure on its
   arguments and store. A body is derived assuming only calls whose measure is
   strictly below that of the current call (ctx_below). *)
Record tdef := TDef { td_def : fdef; td_meas : list value -> store -> nat }.
Definition restrict (T : tdef) (b : nat) : cspec :=
 let c := fd_spec (td_def T) in
 CSpec (c_name c) (fun vs s => c_pre c vs s /\ td_meas T vs s < b) (c_post c) (c_exn c).
Definition ctx_below (Ts : list tdef) (Gx : list cspec) (b : nat) := map (fun T => restrict T b) Ts ++ Gx.
Definition body_ok_total (Ts : list tdef) Gx (T : tdef) := forall vs s0, c_pre (fd_spec (td_def T)) vs s0 ->
 deriv Total (ctx_below Ts Gx (td_meas T vs s0)) (fun s => s = s0)
   (combine (fd_params (td_def T)) vs) (fd_body (td_def T))
   (c_post (fd_spec (td_def T)) vs s0) (c_exn (fd_spec (td_def T)) vs s0).

Lemma restrict_binds : forall T b, binds (td_def T) -> binds (FDef (restrict T b) (fd_params (td_def T)) (fd_body (td_def T))).
Proof. intros T b B vs s [Hp _]. exact (B vs s Hp). Qed.

Theorem rec_total : forall Ts Gx,
 (forall n, ctx_at Total n Gx) -> Forall (fun T => binds (td_def T)) Ts ->
 Forall (body_ok_total Ts Gx) Ts ->
 forall n, ctx_at Total n (map (fun T => fd_spec (td_def T)) Ts ++ Gx).
Proof.
 intros Ts Gx HX HB HO.
 assert (Below : forall b n, ctx_at Total n (ctx_below Ts Gx b)).
 { induction b as [b IH] using lt_wf_ind. intros n c I.
   apply in_app_or in I; destruct I as [I|I]; [|apply HX; exact I].
   apply in_map_iff in I; destruct I as [T [<- IT]].
   intros vs s0 j L Phi h k s O [<- [Hp Lt]] C.
   pose proof (proj1 (Forall_forall _ _) HB T IT) as BT.
   pose proof (proj1 (Forall_forall _ _) HO T IT vs s Hp) as D.
   pose proof (proj1 (soundness Total _ j (IH _ Lt j)) _ _ _ _ _ D) as Tr.
   eapply G_tau_same; [exact (body_next (td_def T) vs s k BT Hp)|].
   exact (Tr j (le_n _) Phi h k s O eq_refl C). }
 intros n c I. apply in_app_or in I; destruct I as [I|I]; [|apply HX; exact I].
 apply in_map_iff in I; destruct I as [T [<- IT]].
 intros vs s0 j L Phi h k s O [<- Hp] C.
 assert (In (restrict T (S (td_meas T vs s))) (ctx_below Ts Gx (S (td_meas T vs s))))
   by (apply in_or_app; left; apply in_map_iff; eauto).
 exact (Below _ n _ H vs s j L Phi h k s O (conj eq_refl (conj Hp (le_n _))) C).
Qed.
End Soundness.

(* ---------- meaning in the closed KLambda system ---------- *)
(* The top-level observer of a closed program: a normal result satisfies Q,
   an exception satisfies E, a resource failure is admitted only for RP, and
   no other outcome (exit, kill, cancel) is admitted. *)
Definition top (Q : post) (E : epost) : observer := fun t o => match o with
 | Normal v => exists s, Q v s t
 | Error x => exists s, E x s t
 | ResourceOut r => RP r
 | _ => False end.
Lemma top_ok : forall Q E, obs_ok (top Q E).
Proof. intros Q E h r H; exact H. Qed.
Lemma top_conts : forall m n Q E, conts m (top Q E) n [] [] Q E.
Proof. intros m n Q E; split; intros; eapply G_final; [reflexivity|cbn; eauto|reflexivity|cbn; eauto]. Qed.

Lemma triple_top : forall m Pre rho e Q E s n, triple m Pre rho e Q E -> Pre s ->
 G m (top Q E) n [] (Cfg (Eval rho e) [] s).
Proof. intros m Pre rho e Q E s n T Ps. exact (T n n (le_n _) _ [] [] s (top_ok Q E) Ps (top_conts m n Q E)). Qed.

Section Closed.
Variable W : Type.
Variable O : W -> request -> response -> W -> Prop.
Variable tick : W -> W.
(* No pending signal or cancellation: the behaviors below are those of the
   program against this environment, with every response O allows. *)
Definition none (_ : W) : option env_event := None.
Definition cstep := KLMetatheory.cstep W O none tick P.
Definition oracle_total := forall w q, exists r w', O w q r w'.

Lemma term_star : forall Phi h c w t c' w', term Phi h c ->
 star cstep (c, w) t (c', w') -> term Phi (h ++ t) c'.
Proof.
 intros Phi h c w t c' w' T S. remember (c, w) as cw eqn:E1. remember (c', w') as cw' eqn:E2.
 revert h c w T E1 E2. induction S as [x|x l [c1 w1] t0 x2 St S IH]; intros h c w T E1 E2; subst.
 - injection E2 as -> ->. rewrite app_nil_r; exact T.
 - inversion St; subst; [| |discriminate].
   + inversion T; subst; try congruence.
     match goal with H1 : next P c = MTau ?a, H2 : next P c = MTau ?b |- _ => rewrite H1 in H2; injection H2 as <- end.
     cbn [trace_of app]. eapply IH; eauto.
   + inversion T; subst; try congruence.
     match goal with H1 : next P c = MIO ?a ?b, H2 : next P c = MIO ?a' ?b' |- _ => rewrite H1 in H2; injection H2 as <- <- end.
     cbn [trace_of]. rewrite app_assoc. eapply IH; eauto.
Qed.

Lemma term_not_silent : forall Phi h c w, term Phi h c -> ~ silent_forever cstep (c, w).
Proof.
 intros Phi h c w T; revert w; induction T as [h c o F _|h c c' N T IH|h c q kk N T IH]; intros w SF;
 inversion SF as [x [c2 w2] St SF']; subst; inversion St; subst; try congruence; try discriminate.
 match goal with H1 : next P c = MTau ?a |- _ => rewrite N in H1; injection H1 as <- end.
 eapply IH; eauto.
Qed.

Lemma star_first : forall a t b, star cstep a t b -> t <> [] ->
 exists l a1 t', cstep a l a1 /\ star cstep a1 t' b /\ t = trace_of l ++ t'.
Proof. intros a t b S N; destruct S as [|x l y t z St S]; [contradiction|]. exists l, y, t; auto. Qed.

Lemma rf_back : forall a u b T, star cstep a u b -> reacts_forever cstep b T -> exists T', reacts_forever cstep a T'.
Proof.
 intros a u b T S R. inversion R as [x t b' T0 S1 Ne R1]; subst.
 exists (prepend (u ++ t) T0). apply rf_step with (s' := b'); [eapply star_trans; eauto| |exact R1].
 destruct u; [exact Ne|discriminate].
Qed.

Lemma term_not_reacts : forall Phi h c w T, term Phi h c -> ~ reacts_forever cstep (c, w) T.
Proof.
 intros Phi h c w T Tm; revert w T; induction Tm as [h c o F _|h c c' N Tm IH|h c q kk N Tm IH]; intros w T R;
 inversion R as [x t b' T0 S1 Ne R1]; subst; destruct (star_first _ _ _ S1 Ne) as (l & [c2 w2] & t' & St & S2 & _);
 inversion St; subst; try congruence; try discriminate.
 - match goal with H1 : next P c = MTau ?a |- _ => rewrite N in H1; injection H1 as <- end.
   destruct (rf_back _ _ _ _ S2 R1) as [T' R']. eapply IH; exact R'.
 - match goal with H1 : next P c = MIO ?a ?b |- _ => rewrite N in H1; injection H1 as <- <- end.
   destruct (rf_back _ _ _ _ S2 R1) as [T' R']. eapply IH; exact R'.
Qed.

Lemma term_not_stuck : forall Phi h c w, oracle_total -> term Phi h c -> ~ stuck cstep (KLMetatheory.cfinal W P) (c, w).
Proof.
 intros Phi h c w OT T [N F]; destruct T as [h c o Fo _|h c c' Nx _|h c q kk Nx _].
 - exact (F o Fo).
 - apply (N Tau (c', tick w)). apply KLMetatheory.cs_tau; [reflexivity|exact Nx].
 - destruct (OT w q) as (r & w' & Ow). apply (N (Obs (EvIO q r)) (kk r, w')).
   eapply KLMetatheory.cs_io; [reflexivity|exact Nx|exact Ow].
Qed.

Lemma term_exists : forall Phi h c w, oracle_total -> term Phi h c ->
 exists t c' w' o, star cstep (c, w) t (c', w') /\ final P c' o.
Proof.
 intros Phi h c w OT T; revert w; induction T as [h c o F _|h c c' N T IH|h c q kk N T IH]; intro w.
 - exists [], c, w, o; split; [constructor|exact F].
 - destruct (IH (tick w)) as (t & c2 & w2 & o & S & F). exists ([] ++ t), c2, w2, o; split; [|exact F].
   change ([] ++ t) with (trace_of Tau ++ t). eapply star_step; [|exact S].
   apply KLMetatheory.cs_tau; [reflexivity|exact N].
 - destruct (OT w q) as (r & w' & Ow). destruct (IH r w') as (t & c2 & w2 & o & S & F).
   exists ([EvIO q r] ++ t), c2, w2, o; split; [|exact F].
   change ([EvIO q r] ++ t) with (trace_of (Obs (EvIO q r)) ++ t). eapply star_step; [|exact S].
   eapply KLMetatheory.cs_io; [reflexivity|exact N|exact Ow].
Qed.

(* Total correctness: under every environment that answers every request
   (with any responses it chooses, including failed and partial writes), every
   maximal behavior of the closed program terminates, with an outcome admitted
   by top Q E (normal result in Q, exception in E, resource failure only in
   RP), and at least one behavior exists. Divergence, reaction and going
   wrong are excluded. *)
Theorem total_meaning : forall Pre rho e Q E s w, policy_ok -> oracle_total ->
 triple Total Pre rho e Q E -> Pre s ->
 (forall b, KLMetatheory.behaviors W O none tick P (Cfg (Eval rho e) [] s) w b ->
    exists t o, b = Terminates t o /\ top Q E t o) /\
 (exists t o, KLMetatheory.behaviors W O none tick P (Cfg (Eval rho e) [] s) w (Terminates t o)).
Proof.
 intros Pre rho e Q E s w PO OT Tr Ps. pose proof (triple_top Total Pre rho e Q E s 0 Tr Ps) as T. cbn [G] in T.
 split.
 - intros b B; unfold KLMetatheory.behaviors in B.
   inversion B as [t [c' w'] o S F|t [c' w'] S SF|T' R|t [c' w'] S St]; subst.
   + exists t, o; split; [reflexivity|]. pose proof (term_star _ _ _ _ _ _ _ T S) as T2.
     unfold KLMetatheory.cfinal, final in F; cbn in F.
     inversion T2; subst; try congruence. rewrite F in H; injection H as <-; exact H0.
   + exfalso; exact (term_not_silent _ _ _ w' (term_star _ _ _ _ _ _ _ T S) SF).
   + exfalso; exact (term_not_reacts _ _ _ w T' T R).
   + exfalso; exact (term_not_stuck _ _ _ w' OT (term_star _ _ _ _ _ _ _ T S) St).
 - destruct (term_exists _ _ _ w OT T) as (t & c' & w' & o & S & F).
   exists t, o. econstructor; [exact S|exact F].
Qed.

(* Partial-mode facts are invariant along every finite execution prefix. *)
Lemma safe_star : forall Iv Phi h c w t c' w', (forall n, safe Iv Phi n h c) ->
 star cstep (c, w) t (c', w') -> (forall n, safe Iv Phi n (h ++ t) c') /\ Forall Iv t.
Proof.
 intros Iv Phi h c w t c' w' H Hs. remember (c, w) as cw eqn:E1. remember (c', w') as cw' eqn:E2.
 revert h c w H E1 E2. induction Hs as [x|x l [c1 w1] t0 x2 St Hs IH]; intros h c w H E1 E2; subst.
 - injection E2 as -> ->. rewrite app_nil_r; auto.
 - inversion St; subst; [| |discriminate].
   + assert (H1 : forall n, safe Iv Phi n h c1) by (intro n; specialize (H (S n)); rewrite safe_S in H;
       match goal with N : next P c = _ |- _ => rewrite N in H end; exact H).
     cbn [trace_of app]. eapply IH; eauto.
   + assert (H1 : Iv (EvIO q r) /\ forall n, safe Iv Phi n (h ++ [EvIO q r]) (kk r)).
     { split; [|intro n]; specialize (H (S n)) || specialize (H 1); rewrite safe_S in H;
       match goal with N : next P c = _ |- _ => rewrite N in H end; apply (H r). }
     destruct H1 as [Hi H1]. destruct (IH (h ++ [EvIO q r]) (kk r) w1 H1 eq_refl eq_refl) as [A B].
     cbn [trace_of]. rewrite app_assoc. split; [exact A|constructor; assumption].
Qed.

Lemma star_split_cons : forall a x t b, star cstep a (x :: t) b ->
 exists am, star cstep a [x] am /\ star cstep am t b.
Proof.
 intros a x t b S. remember (x :: t) as u eqn:E. revert x t E.
 induction S as [y|y l y1 t0 y2 St S IH]; intros x t E; [discriminate|].
 destruct l as [|ev]; cbn [trace_of app] in E.
 - destruct (IH x t E) as (am & A & B). exists am; split; [|exact B].
   change [x] with (trace_of Tau ++ [x]). eapply star_step; eauto.
 - injection E as -> ->. exists y1; split; [|exact S].
   change [x] with (trace_of (Obs x) ++ []). eapply star_step; [exact St|constructor].
Qed.

Lemma prepend_cons : forall e t T, prepend (e :: t) T = SCons e (prepend t T).
Proof. reflexivity. Qed.

(* Every event of an infinitely reacting execution occurs in a finite prefix. *)
Lemma reacts_events : forall e T, in_stream e T -> forall a, reacts_forever cstep a T ->
 exists t b, star cstep a t b /\ In e t.
Proof.
 intros e T I; induction I as [S|e' S I IH]; intros a R;
 inversion R as [x t a' T0 S1 Ne R1]; destruct t as [|x0 t]; try contradiction;
 repeat match goal with Hq : prepend (_ :: _) _ = SCons _ _ |- _ =>
   rewrite prepend_cons in Hq; injection Hq; clear Hq; intros; subst end.
 - exists (e :: t), a'; split; [exact S1|left; reflexivity].
 - destruct t as [|x1 t].
   + cbn [prepend] in IH. destruct (IH a' R1) as (u & b & S2 & Iu).
     exists ([e'] ++ u), b; split; [eapply star_trans; eauto|apply in_or_app; right; exact Iu].
   + destruct (star_split_cons _ _ _ _ S1) as (am & A & B).
     assert (Ram : reacts_forever cstep am (prepend (x1 :: t) T0))
       by (apply rf_step with (s' := a'); [exact B|discriminate|exact R1]).
     destruct (IH am Ram) as (u & b & S2 & Iu).
     exists ([e'] ++ u), b; split; [eapply star_trans; eauto|apply in_or_app; right; exact Iu].
Qed.

(* Partial correctness and the temporal judgment: no behavior goes wrong,
   every terminating behavior has an outcome admitted by top Q E, and under
   Always I every event of every behavior -- terminating, diverging or
   infinitely reacting -- satisfies I. Termination is not claimed. *)
Theorem partial_meaning : forall m Pre rho e Q E s w, m <> Total -> oracle_total ->
 triple m Pre rho e Q E -> Pre s ->
 forall b, KLMetatheory.behaviors W O none tick P (Cfg (Eval rho e) [] s) w b ->
 match b with Terminates t o => top Q E t o | GoesWrong _ => False | _ => True end /\
 (forall ev, occurs ev b -> inv_of m ev).
Proof.
 intros m Pre rho e Q E s w NT OT Tr Ps b B.
 assert (H : forall n, safe (inv_of m) (top Q E) n [] (Cfg (Eval rho e) [] s)).
 { intro n; pose proof (triple_top m Pre rho e Q E s n Tr Ps) as T; destruct m; cbn [G] in T; [exact T|contradiction|exact T]. }
 unfold KLMetatheory.behaviors in B.
 inversion B as [t [c' w'] o S F|t [c' w'] S SF|T' R|t [c' w'] S St]; subst.
 - destruct (safe_star _ _ _ _ _ _ _ _ H S) as [A Fi]. split.
   + specialize (A 1). rewrite safe_S in A. unfold KLMetatheory.cfinal, final in F; cbn in F. rewrite F in A; exact A.
   + intros ev Ie; cbn in Ie. exact (proj1 (Forall_forall _ _) Fi ev Ie).
 - destruct (safe_star _ _ _ _ _ _ _ _ H S) as [_ Fi]. split; [exact I|].
   intros ev Ie; cbn in Ie. exact (proj1 (Forall_forall _ _) Fi ev Ie).
 - split; [exact I|]. intros ev Ie; cbn in Ie.
   destruct (reacts_events ev T' Ie _ R) as (u & [c2 w2] & S2 & Iu).
   destruct (safe_star _ _ _ _ _ _ _ _ H S2) as [_ Fi]. exact (proj1 (Forall_forall _ _) Fi ev Iu).
 - destruct (safe_star _ _ _ _ _ _ _ _ H S) as [A _]. exfalso. destruct St as [N F].
   specialize (A 1). rewrite safe_S in A. destruct (next P c') eqn:Nx.
   + apply (N Tau (c, tick w')). apply KLMetatheory.cs_tau; [reflexivity|exact Nx].
   + destruct (OT w' q) as (r & w2 & Ow). apply (N (Obs (EvIO q r)) (k r, w2)).
     eapply KLMetatheory.cs_io; [reflexivity|exact Nx|exact Ow].
   + exact (F o Nx).
   + exact A.
Qed.
End Closed.

(* ---------- meaning in terms of the fuel evaluator KLMetatheory.run ---------- *)
Section Run.
Variable W : Type.
Variable respond : W -> request -> response * W.
Variable tick : W -> W.
Definition krun := KLMetatheory.run W respond (none W) tick P.

Lemma term_run : forall Phi h c w, term Phi h c -> exists n t o, krun n c w = VDone t o /\ Phi (h ++ t) o.
Proof.
 intros Phi h c w T; revert w; induction T as [h c o F Ho|h c c' N T IH|h c q kk N T IH]; intro w.
 - exists 0, [], o; split; [unfold krun; cbn; rewrite F; reflexivity|rewrite app_nil_r; exact Ho].
 - destruct (IH (tick w)) as (n & t & o & R & Ho). exists (S n), t, o; split; [|exact Ho].
   unfold krun in *; cbn [KLMetatheory.run]. rewrite N. unfold KLMetatheory.cnext. rewrite N.
   cbn -[KLMetatheory.run]. rewrite R. reflexivity.
 - destruct (respond w q) as [r w'] eqn:Rw. destruct (IH r w') as (n & t & o & R & Ho).
   exists (S n), ([EvIO q r] ++ t), o; split; [|rewrite app_assoc; exact Ho].
   unfold krun in *; cbn [KLMetatheory.run]. rewrite N. unfold KLMetatheory.cnext. rewrite N.
   cbn -[KLMetatheory.run]. rewrite Rw, R. reflexivity.
Qed.

(* Total correctness, evaluator form: for every deterministic environment the
   fuel evaluator returns a decided terminating verdict with enough fuel. *)
Theorem total_run : forall Pre rho e Q E s w, triple Total Pre rho e Q E -> Pre s ->
 exists n t o, krun n (Cfg (Eval rho e) [] s) w = VDone t o /\ top Q E t o.
Proof.
 intros Pre rho e Q E s w Tr Ps. pose proof (triple_top Total Pre rho e Q E s 0 Tr Ps) as T. cbn [G] in T.
 exact (term_run _ [] _ w T).
Qed.

(* Partial correctness, evaluator form: whatever fuel is given, a terminating
   verdict satisfies the contract and the evaluator never reports going
   wrong; exhaustion makes no claim. *)
Theorem partial_run : forall m Pre rho e Q E s w n, m <> Total -> triple m Pre rho e Q E -> Pre s ->
 match krun n (Cfg (Eval rho e) [] s) w with
 | VDone t o => top Q E t o | VWrong _ => False | _ => True end.
Proof.
 intros m Pre rho e Q E s w n NT Tr Ps.
 assert (H : forall n, safe (inv_of m) (top Q E) n [] (Cfg (Eval rho e) [] s)).
 { intro j; pose proof (triple_top m Pre rho e Q E s j Tr Ps) as T; destruct m; cbn [G] in T; [exact T|contradiction|exact T]. }
 pose proof (KLMetatheory.run_sound W respond (none W) tick P n (Cfg (Eval rho e) [] s) w) as RS.
 unfold krun. destruct (KLMetatheory.run W respond (none W) tick P n (Cfg (Eval rho e) [] s) w); try exact I.
 - destruct RS as (c' & w' & S & F).
   destruct (safe_star W _ tick _ _ _ _ _ _ _ _ H S) as [A _]. specialize (A 1). rewrite safe_S in A.
   unfold KLMetatheory.cfinal, final in F; cbn in F. rewrite F in A; exact A.
 - destruct RS as (c' & w' & S & [N F]).
   destruct (safe_star W _ tick _ _ _ _ _ _ _ _ H S) as [A _]. specialize (A 1). rewrite safe_S in A.
   destruct (next P c') eqn:Nx.
   + apply (N Tau (c, tick w')). apply KLMetatheory.cs_tau; [reflexivity|exact Nx].
   + destruct (respond w' q) as [r w2] eqn:Rw. apply (N (Obs (EvIO q r)) (k r, w2)).
     eapply KLMetatheory.cs_io; [reflexivity|exact Nx|exact Rw].
   + exact (F o Nx).
   + exact A.
Qed.
End Run.
End Logic.
End ContractLogic.
