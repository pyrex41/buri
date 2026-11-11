(* Shen/JIT Phase 2, front track: the Prolog rewrites of norm (r1-f-prolog).
   lower.shen (934cfa5) has four rewrites for the Prolog compiler's output:
   - bound-now: (shen.bind! X Y B (freeze E)) to
       (let a1 X' (let a2 Y' (let a3 B' (do (shen.bindv a1 a2 a3) (let r E' (if (= r false) (shen.unwind a1 a3 r) r))))))
     normalised, so bindv and unwind are inlined in it, as norm inlined them in shen.bind!'s own body;
   - unified-now: (is X Y B L K (freeze E)) and is! to a let chain calling shen-jit.unify= or
     shen-jit.unify=!, port defuns over the port primitives shen-jit.same?, shen-jit.deref,
     shen-jit.pvar? and shen-jit.pvar-offset;
   - cut-fail (v0.6): (shen.cut B L K (freeze (when false B2 L2 K2 C))), every argument a variable,
     to (if (shen.unlocked? L) (shen.lock K L) false);
   - deref= (v0.6): (= (shen.deref X B) (shen.deref Y B)) to (shen-jit.deref= X Y B).

   What this file proves (each Theorem in Audit_Jit, "Closed under the global context"):
   - bind_rule_sound: the bound-now rule, as a front rule of the F00 shape (`rule`, `rule_sound`,
     the same text as JitFrontCheck's, which is not on p2/int at this branch's base), is sound for
     every store D: given a recursive checker sound at every scope, a pair the rule accepts is in
     KRef. The rule reads the source call's arguments X0, Y0, B0 against the expansion's let values
     by the recursive checker, and the frozen body E0 against each place the expansion runs it, by
     the recursive checker in the scope of that place's free names; the expansion's body N against
     shen.bind!'s lowered body e_B in D by `beq` (alpha-equivalence with the three parameters renamed
     to a1 a2 a3, the fourth thawed in place, and a let whose name is unused read as (do A B) with
     the kernel's do from D). No transitivity of KRef is used: the source steps from the call into
     e_B (ERel's frames, ret_frame_tau), and e_B and N are related by a direct induction (beq_sound).
   - bind_site_unsound: JitFrontD.bind_site_sound_statement (D00's statement for the same rewrite,
     to be proved by "F-inline (or the bind family)") is FALSE, with a Rocq counterexample: a frozen
     body that reads KLPort's closure-identity key (EVar id_key). bind_site checks the thawed body's
     free names against the expansion's binders (inl_eq's `hidden`) and the fresh names, but not
     against id_key, which the source's freeze closure binds (tagged_env) and the expansion, which
     runs the body in place, does not. bind_rule adds that guard; Example bind_rule_rejects_id_key
     pins it.
   - The scan (prolog_scan, Rocq vm_compute over the 955 parsed stage 0 sources; a test, not proof;
     run by stage0_to_rocq.py --prolog on /lps/p6/sj/build/stage0 at 934cfa5): cut-fail's shape 0
     definitions (0 sites), deref='s 0 (0), shen.cut with a frozen fourth argument 8 (16),
     bound-now's direct shape 6 (25), the let-frozen shape 5 (23 lets), unified-now's 4 (7). So
     the absence of a cut-fail or deref= rule changes no stage 0 verdict; see the residuals below.

   Residuals (named, each with a ledger entry in spec/obligations.json):
   - OB-JIT-FRONT-PROLOG-UNIFY (decision-gated: identity primitives and port primitives without an
     approved source meaning). unified-now's target calls shen-jit.unify= or shen-jit.unify=!,
     whose bodies call shen-jit.same? (pointer identity), shen-jit.deref, shen-jit.pvar? and
     shen-jit.pvar-offset. Under jit_rules these are named calls into the store, which D cannot pin
     (no KL body exists for them), so no rule for unified-now is sound for every store meeting D;
     there is none here. It fires in 4 definitions (7 sites) of stage 0.
   - OB-JIT-FRONT-PROLOG-DEREFEQ (decision-gated: identity primitives). deref= replaces two deep
     copies and = by shen-jit.deref=, which answers true through shen-jit.same? on one cell where
     = on the copies compares contents (false on a NaN leaf: OB-JIT-NAN-IDENTITY). There is no rule.
     Vacuous for stage 0: the source shape occurs in no stage 0 definition (prolog_scan).
   - OB-JIT-FRONT-PROLOG-CUTFAIL (no rule, vacuous for stage 0). Its soundness needs shen.cut's,
     when's, shen.unlocked?'s and shen.lock's lowered bodies in D and a proof that the source call
     runs to e_cut's residual (if (and (= W false) U) (shen.lock K L) W) with W false; it is not
     proved here. The source shape occurs in no stage 0 definition (prolog_scan: 16 calls of
     shen.cut with a frozen fourth argument, in 8 definitions, none whose frozen body is a `when`
     call), so no stage 0 verdict depends on it.
   - bound-now through a let-bound freeze (12 of stage 0's 37 sites): frozen-in copies E into the
     bind call; the rule for that shape is the freeze-copying family's (it rewrites the source to the
     direct shape, then this rule applies).
   - Every D holding shen.bind! fails D_compiled' today (JitFrontD's D_why: shen-jit.pvar-offset, a
     port primitive with no approved meaning, OB-JIT-PORT-PRIMS), so the 6 definitions with
     bound-now sites stay residual in the full pipeline whatever this rule proves.

   No axiom, no Admitted. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef JitKRefGround JitKRefBase JitKRefCompatClo JitKRefPrim JitKRefCompatCtl JitKRefCompatCall JitKRefFv JitKRefFund JitLowerStage0 JitNorm JitNormStage0 JitFrontD.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitFrontProlog.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitKRef.JitKRef JitKRefGround.JitKRefGround JitKRefBase.JitKRefBase
 JitLowerStage0.JitLowerStage0.
Module F := JitFrontD.JitFrontD.
Definition do_name : name := JitNorm.JitNorm.do_name.

(* ======================= the rule shape (F00's, same text) ======================= *)
Definition rule := (list name -> expr -> expr -> bool) -> list name -> expr -> expr -> bool.

Fixpoint forall2b {A B} (f : A -> B -> bool) (l0 : list A) (l : list B) : bool := match l0, l with
 | [], [] => true
 | a :: l0, b :: l => f a b && forall2b f l0 l
 | _, _ => false end.

(* ======================= beq: e_B against the expansion's body ======================= *)
(* `beq fuel tk p4 rn e0 e`: e0 (source, shen.bind!'s lowered body e_B, run in bind!'s frame) against
   e (target, the expansion's body N). rn pairs a source binder with a target binder, innermost
   first; it starts with bind!'s first three parameters paired with the expansion's fresh names.
   - congruence and renaming, as JitFrontD.aeq, every binder pair binder_ok;
   - a variable must be bound in rn: e_B has no free name but its parameters, so a free one is
     refused rather than compared by name;
   - (apply p4), p4 the fourth parameter and unbound in rn, against any e: the source thaws the
     frozen argument, the target runs e in place. tk e decides that e refines the frozen body (the
     rule passes its recursive checker); no free name of e may be a target binder of rn (it would
     read the expansion's binding, not the caller's) or KLPort's id_key (the source runs the
     frozen body in the closure's environment, whose head binds id_key to the closure's own cell);
   - (let X A B), X not free in B, against (do A' B'): the kernel's do, from D, returns its second
     argument, as the let does. *)
Fixpoint beq (fuel : nat) (tk : expr -> bool) (p4 : name) (rn : list (name * name)) (e0 e : expr) {struct fuel} : bool :=
 match fuel with O => false | S fuel =>
 let go := beq fuel tk p4 in
 match e0 with
 | EApp (EVar p) [] =>
   if F.free_in rn p then
     text_eqb p p4 && forallb (fun y => negb (F.hidden rn y)) (fv e) && negb (bound (fv e) id_key) && tk e
   else match e with EApp h [] => go rn (EVar p) h | _ => false end
 | _ =>
 match e0, e with
 | ENum a, ENum b => F.num_eqb a b
 | EStr a, EStr b => text_eqb a b
 | ESym a, ESym b => text_eqb a b
 | EBool a, EBool b => Bool.eqb a b
 | ENil, ENil => true
 | EVar x, EVar y => negb (F.free_in rn x) && F.var_ok rn x y
 | ELam x b0, ELam y b => F.binder_ok x y && go ((x, y) :: rn) b0 b
 | ELet x a0 b0, ELet y a b => F.binder_ok x y && go rn a0 a && go ((x, y) :: rn) b0 b
 | ELet x a0 b0, ECall d [a; b] => text_eqb d do_name && negb (bound (fv b0) x) && go rn a0 a && go rn b0 b
 | EIf c0 a0 b0, EIf c a b => go rn c0 c && go rn a0 a && go rn b0 b
 | EAnd a0 b0, EAnd a b => go rn a0 a && go rn b0 b
 | EOr a0 b0, EOr a b => go rn a0 a && go rn b0 b
 | ETrap a0 b0, ETrap a b => go rn a0 a && go rn b0 b
 | ECond l0, ECond l => forall2b (fun p0 p => go rn (fst p0) (fst p) && go rn (snd p0) (snd p)) l0 l
 | EFreeze a0, EFreeze a => go rn a0 a
 | EType a0, EType a => go rn a0 a
 | EApp h0 l0, EApp h l => go rn h0 h && forall2b (go rn) l0 l
 | ECall f0 l0, ECall f l => text_eqb f0 f && forall2b (go rn) l0 l
 | _, _ => false end end end.

(* The scope a thawed place is checked in: the names of g free in it. *)
Definition gfv (g : list name) (e : expr) : list name := filter (fun x => bound (fv e) x) g.

(* ======================= the bound-now rule ======================= *)
(* Source (shen.bind! X0 Y0 B0 (freeze E0)); target (let a1 X (let a2 Y (let a3 B N))), bound-now's
   expansion. D must hold shen.bind! with four distinct parameters, the fourth not id_key, and the
   kernel's do (two distinct parameters, returning the second). The fresh names are outside the
   scope g (the let values are checked in g, under the earlier lets) and paired with bind!'s first
   three parameters by binder_ok. Each check here is used by bind_rule_sound's proof. *)
Definition bind_rule (D : list (name * fundef)) : rule := fun rec g e0 e =>
 match e0, e with
 | ECall f [x0; y0; b0; EFreeze ex0], ELet a1 x (ELet a2 y (ELet a3 b n)) =>
   text_eqb f F.bind_name &&
   match lookup F.bind_name D, lookup do_name D with
   | Some (FUser [p1; p2; p3; p4] eB), Some (FUser [v1; v2] (EVar v2')) =>
     negb (text_eqb v1 v2) && text_eqb v2 v2' &&
     nodupb [p1; p2; p3; p4] && negb (text_eqb p4 id_key) &&
     F.binder_ok p1 a1 && F.binder_ok p2 a2 && F.binder_ok p3 a3 && F.disjoint [a1; a2; a3] g &&
     rec g x0 x && rec g y0 y && rec g b0 b &&
     beq (S (F.dsize eB)) (fun e' => rec (gfv g e') ex0 e') p4 [(p3, a3); (p2, a2); (p1, a1)] eB n
   | _, _ => false end
 | _, _ => false end.

Section Sound.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules sealed).
Notation P := jit_profile.
Notation srun := (JitKRef.JitKRef.srun sealed).
Notation ObsT := (JitKRef.JitKRef.ObsT sealed).
Notation VRel := (JitKRef.JitKRef.VRel sealed D).
Notation SRel := (JitKRef.JitKRef.SRel sealed D).
Notation KRel := (JitKRef.JitKRef.KRel sealed D).
Notation ERel := (JitKRef.JitKRef.ERel sealed D).
Notation KRef := (JitKRef.JitKRef.KRef sealed D).
Notation D_wf := (JitKRef.JitKRef.D_wf sealed D).
Notation fund_below := (JitKRef.JitKRef.fund_below sealed D).

(* F00's soundness notions, same text. *)
Definition chk_sound (c : list name -> expr -> expr -> bool) : Prop :=
 forall g a b, c g a b = true -> KRef g a b.
Definition rule_sound (r : rule) : Prop :=
 forall rec, chk_sound rec -> forall g e0 e, r rec g e0 e = true -> KRef g e0 e.

(* ---------- small facts ---------- *)
Lemma bound_iff : forall l x, bound l x = true <-> In x l.
Proof.
 intros l x. unfold bound. rewrite existsb_exists. split.
 - intros (y & I & E). apply text_eqb_eq in E. subst. exact I.
 - intros I. exists x. split; [exact I|apply text_eqb_refl].
Qed.

Lemma num_eqb_eq : forall a b, F.num_eqb a b = true -> a = b.
Proof.
 intros [x|x] [y|y] H; cbn in H; try discriminate.
 - apply Z.eqb_eq in H; subst; reflexivity.
 - apply N.eqb_eq in H; subst; reflexivity.
Qed.

Lemma free_in_cons : forall x y rn z, F.free_in ((x, y) :: rn) z = (negb (text_eqb x z) && F.free_in rn z)%bool.
Proof. intros. unfold F.free_in. cbn. rewrite negb_orb. reflexivity. Qed.

Lemma hidden_cons : forall x y rn z, F.hidden ((x, y) :: rn) z = (text_eqb y z || F.hidden rn z)%bool.
Proof. intros. reflexivity. Qed.

(* var_ok on a name bound in rn reads the pair that binds it. *)
Lemma var_ok_bound : forall rn x y, F.var_ok rn x y = true -> F.free_in rn x = false -> In (x, y) rn.
Proof.
 induction rn as [|[a b] rn IH]; intros x y V Fr; cbn in V.
 - unfold F.free_in in Fr. cbn in Fr. discriminate.
 - rewrite free_in_cons in Fr. destruct (text_eqb a x) eqn:A.
   + apply text_eqb_eq in A, V. subst. left. reflexivity.
   + destruct (text_eqb b y); [discriminate|]. cbn in Fr. right. apply IH; assumption.
Qed.

Lemma lookup_cons_ne : forall {A} x y (v : A) rho, x <> y -> lookup x ((y, v) :: rho) = lookup x rho.
Proof.
 intros A x y v rho N. cbn. destruct (text_eqb x y) eqn:E; [apply text_eqb_eq in E; contradiction|reflexivity].
Qed.

Lemma lookup_cons_eq : forall {A} x (v : A) rho, lookup x ((x, v) :: rho) = Some v.
Proof. intros. cbn. rewrite text_eqb_refl. reflexivity. Qed.

Lemma In_fv_filter : forall x y l, In y (filter (fun z => negb (text_eqb z x)) l) <-> In y l /\ y <> x.
Proof.
 intros x y l. rewrite filter_In. split.
 - intros [I E]. split; [exact I|]. intros ->. rewrite text_eqb_refl in E. discriminate.
 - intros [I N]. split; [exact I|]. destruct (text_eqb y x) eqn:E; [apply text_eqb_eq in E; contradiction|reflexivity].
Qed.
Lemma forall2b_sound : forall {A B} (f : A -> B -> bool) (Q : A -> B -> Prop) l0 l,
 (forall a b, In a l0 -> In b l -> f a b = true -> Q a b) -> forall2b f l0 l = true -> Forall2 Q l0 l.
Proof.
 intros A B f Q l0. induction l0 as [|a l0 IH]; intros [|b l] H E; cbn in E; try discriminate.
 - constructor.
 - apply andb_true_iff in E as [E1 E2]. constructor.
   + apply H; [left; reflexivity|left; reflexivity|exact E1].
   + apply IH; [intros a' b' I J; apply H; right; assumption|exact E2].
Qed.

Lemma lookup_tags : forall {A} (t r : list (name * A)) z, (forall y, In y (map fst t) -> y = id_key) -> z <> id_key ->
 lookup z (t ++ r) = lookup z r.
Proof.
 intros A t r z Ht N. induction t as [|[y0 u] t IH]; [reflexivity|]. cbn [app].
 rewrite lookup_cons_ne; [apply IH; intros y I; apply Ht; right; exact I|].
 intros E. apply N. rewrite E. apply Ht. left. reflexivity.
Qed.

Lemma binder_ok_ne : forall x y, F.binder_ok x y = true -> x <> id_key /\ y <> id_key.
Proof.
 intros x y H. unfold F.binder_ok in H. apply andb_true_iff in H as [A B].
 split; intros ->; [rewrite text_eqb_refl in A|rewrite text_eqb_refl in B]; discriminate.
Qed.

(* ---------- the target-only frame lemmas ---------- *)
(* A target frame that only unwinds an exception costs the target one step. *)
Lemma ObsT_throw_tgt : forall k w f x K0 K s0 s, JitKRefBase.JitKRefBase.nontrap f = true ->
 ObsT k w (Cfg (Throw x) K0 s0) (Cfg (Throw x) K s) -> ObsT (S k) w (Cfg (Throw x) K0 s0) (Cfg (Throw x) (f :: K) s).
Proof.
 intros k w f x K0 K s0 s N H. apply ObsT_step.
 - unfold nonterm. rewrite throw_frame_next by exact N. exact I.
 - intros l c1 St. destruct (step_r_cases _ _ _ _ St) as [[E ->]|[(q & kk & r & E & _)|(r & y & Rc & _)]].
   + rewrite throw_frame_next in E by exact N. injection E as <-. cbn [trace_of]. apply ObsT_ObsTr. exact H.
   + rewrite throw_frame_next in E by exact N. discriminate.
   + cbn in Rc. discriminate.
Qed.

(* A source frame that only unwinds an exception: the source steps silently past it. *)
Lemma ObsT_throw_src : forall k w f0 x K0 c s0, JitKRefBase.JitKRefBase.nontrap f0 = true ->
 ObsT k w (Cfg (Throw x) K0 s0) c -> ObsT k w (Cfg (Throw x) (f0 :: K0) s0) c.
Proof.
 intros k w f0 x K0 c s0 N H. eapply ObsT_anti; [|exact H].
 eapply srun_tau; [apply throw_frame_next; exact N|apply srun_refl].
Qed.

Section Do.
Variables (v1 v2 : name).
Hypothesis Hdo : In (do_name, FUser [v1; v2] (EVar v2)) D.
Hypothesis Hv12 : v1 <> v2.

Lemma next_do : forall s a v rho K, JitKRef.JitKRef.StoreHas D s ->
 next_r R P (Cfg (Ret v) (KCallArgs do_name [a] [] rho :: K) s) = MTau (Cfg (Eval [(v1, a); (v2, v)] (EVar v2)) K s).
Proof.
 intros s a v rho K Hs. change (call_named_r R P do_name (rev [v; a]) K s = MTau (Cfg (Eval [(v1, a); (v2, v)] (EVar v2)) K s)).
 cbn [rev app]. rewrite (call_named_user sealed do_name [v1; v2] (EVar v2) [a; v] K s); [reflexivity|apply Hs; exact Hdo|reflexivity].
Qed.

Lemma lookup_do : forall (a v : value), lookup v2 [(v1, a); (v2, v)] = Some v.
Proof. intros a v. rewrite lookup_cons_ne by (intros ->; apply Hv12; reflexivity). apply lookup_cons_eq. Qed.

(* The kernel's do as the target's tail: after its second argument, the target calls do and returns
   that argument. *)
Lemma KRel_do_tail : forall k w K0 K a rho, KRel k w K0 K -> KRel k w K0 (KCallArgs do_name [a] [] rho :: K).
Proof.
 intros k w K0 K a rho HK. apply KRel_iff. intros j L w' W. split.
 - intros v0 v s0 s HV HS. destruct j as [|j]; [apply ObsT_0|].
   assert (Hs : JitKRef.JitKRef.StoreHas D s) by (destruct HS as (_ & _ & H & _); exact H).
   apply ObsT_running.
   + reflexivity.
   + unfold nonterm. rewrite next_do by exact Hs. exact I.
   + intros x. cbn [kont mem]. destruct j as [|j]; [apply ObsT_0|]. apply ObsT_throw_tgt; [reflexivity|].
     apply (KRel_throw sealed D); [eapply KRel_mono; [|exact W|exact HK]; lia|].
     eapply SRel_down; [|exact HS]; lia.
   + intros c1 E. rewrite next_do in E by exact Hs. injection E as <-.
     exists (Cfg (Ret v0) K0 s0). split; [apply srun_refl|]. destruct j as [|j]; [apply ObsT_0|].
     apply ObsT_running.
     * reflexivity.
     * unfold nonterm. rewrite (sval_next sealed _ _ v) by apply lookup_do. exact I.
     * intros x. cbn [kont mem]. apply (KRel_throw sealed D); [eapply KRel_mono; [|exact W|exact HK]; lia|].
       eapply SRel_down; [|exact HS]; lia.
     * intros c2 E2. rewrite (sval_next sealed _ _ v) in E2 by apply lookup_do. injection E2 as <-.
       exists (Cfg (Ret v0) K0 s0). split; [apply srun_refl|].
       apply (KRel_ret sealed D); [eapply KRel_mono; [|exact W|exact HK]; lia|eapply VRel_down; [|exact HV]; lia|].
       eapply SRel_down; [|exact HS]; lia.
     * intros q kk r E2. rewrite (sval_next sealed _ _ v) in E2 by apply lookup_do. discriminate.
   + intros q kk r E. rewrite next_do in E by exact Hs. discriminate.
 - intros x s0 s HS. destruct j as [|j]; [apply ObsT_0|]. apply ObsT_throw_tgt; [reflexivity|].
   apply (KRel_throw sealed D); [eapply KRel_mono; [|exact W|exact HK]; lia|eapply SRel_down; [|exact HS]; lia].
Qed.

(* (let X A B), X not free in B, against (do A' B'). *)
Lemma ERel_letdo : forall k w x a0 b0 rho0 a b rho, ERel k w rho0 a0 rho a ->
 (forall j w' v0, (j <= k)%nat -> wext w w' -> ERel j w' ((x, v0) :: rho0) b0 rho b) ->
 ERel k w rho0 (ELet x a0 b0) rho (ECall do_name [a; b]).
Proof.
 intros k w x a0 b0 rho0 a b rho Ha Hb.
 eapply ERel_push with (rho0' := rho0) (e0' := a0) (rho' := rho) (e' := a)
   (F0 := fun K => KLet x b0 rho0 :: K) (F := fun K => KCallArgs do_name [] [b] rho :: K).
 - intros; reflexivity.
 - intros; reflexivity.
 - intros j w' K0 K Lj W HK. apply ret_frame_tau; [exact HK|reflexivity|reflexivity| |].
   + intros i w'' v0 v s0 s c1 Li W' HV HS E. rewrite next_KCallArgs_cons in E. injection E as <-.
     eexists; split; [eapply srun_tau; [apply next_KLet|apply srun_refl]|].
     eapply ERel_apply; [apply (Hb i); [lia|eapply wext_trans; [exact W|exact W']]|apply le_n|eapply wext_self; exact HS| |].
     * apply KRel_do_tail. eapply KRel_mono; [|exact W'|exact HK]; lia.
     * eapply SRel_down; [|exact HS]; lia.
   + intros v s. eexists. apply next_KCallArgs_cons.
 - intros j w' L W. eapply ERel_mono; [|exact W|exact Ha]; lia.
Qed.
End Do.

(* ======================= beq is sound ======================= *)
Section Beq.
Hypothesis Dw : D_wf.
Variables (tk : expr -> bool) (p4 : name) (ex0 : expr) (rc0 rho_b : lenv) (g : list name) (kb : nat) (wb : world).
(* tk: each thawed place refines the frozen body, in the scope of its free names. *)
Hypothesis HTK : forall e, tk e = true -> KRef (gfv g e) ex0 e.
(* The frozen closure's environment (rc0, the caller's behind the closure's own cell) against the
   target's at the call (rho_b), on g except id_key. *)
Hypothesis HE : forall x, In x g -> x <> id_key ->
 exists v0 v, lookup x rc0 = Some v0 /\ lookup x rho_b = Some v /\ VRel kb wb v0 v.
Hypothesis Hp4 : p4 <> id_key.
Variables (v1 v2 : name).
Hypothesis Hdo : In (do_name, FUser [v1; v2] (EVar v2)) D.
Hypothesis Hv12 : v1 <> v2.

(* The invariant of the induction, on the free names of the two subterms:
   - a source name bound in rn reads, through rn, a related target value;
   - p4, while no source binder hides it, reads the frozen closure;
   - a target name no target binder of rn hides, other than id_key, reads the caller's value;
   - no binder of rn is id_key. *)
Definition Inv (k : nat) (w : world) (rn : list (name * name)) (rho0 rho : lenv) (e0 e : expr) : Prop :=
 (k <= kb)%nat /\ wext wb w /\
 (forall x y, In x (fv e0) -> F.free_in rn x = false -> F.var_ok rn x y = true ->
   exists v0 v, lookup x rho0 = Some v0 /\ lookup y rho = Some v /\ VRel k w v0 v) /\
 (In p4 (fv e0) -> F.free_in rn p4 = true -> lookup p4 rho0 = Some (VFrozen ex0 rc0)) /\
 (forall z, In z (fv e) -> F.hidden rn z = false -> z <> id_key -> lookup z rho = lookup z rho_b) /\
 (forall a b, In (a, b) rn -> a <> id_key /\ b <> id_key).

Lemma Inv_mono : forall k j w w' rn rho0 rho e0 e, (j <= k)%nat -> wext w w' ->
 Inv k w rn rho0 rho e0 e -> Inv j w' rn rho0 rho e0 e.
Proof.
 intros k j w w' rn rho0 rho e0 e L W (L1 & W1 & I2 & I3 & I4 & I5).
 split; [lia|]. split; [eapply wext_trans; eauto|]. split; [|split; [exact I3|split; [exact I4|exact I5]]].
 intros x y A B C. destruct (I2 x y A B C) as (v0 & v & E0 & E & V). exists v0, v.
 split; [exact E0|split; [exact E|eapply VRel_mono; eauto]].
Qed.

Lemma Inv_sub : forall k w rn rho0 rho e0 e e0' e', incl (fv e0') (fv e0) -> incl (fv e') (fv e) ->
 Inv k w rn rho0 rho e0 e -> Inv k w rn rho0 rho e0' e'.
Proof.
 intros k w rn rho0 rho e0 e e0' e' S0 S1 (L1 & W1 & I2 & I3 & I4 & I5).
 split; [exact L1|]. split; [exact W1|]. split; [intros x y A; apply I2, S0, A|].
 split; [intros A; apply I3, S0, A|]. split; [intros z A; apply I4, S1, A|exact I5].
Qed.

Lemma Inv_bind : forall k w rn rho0 rho e0 e x y b0 b v0 v t0 t,
 (forall z, In z (map fst t0) -> z = id_key) -> (forall z, In z (map fst t) -> z = id_key) ->
 F.binder_ok x y = true ->
 (forall z, In z (fv b0) -> z <> x -> In z (fv e0)) -> (forall z, In z (fv b) -> z <> y -> In z (fv e)) ->
 Inv k w rn rho0 rho e0 e -> VRel k w v0 v ->
 Inv k w ((x, y) :: rn) ((x, v0) :: t0 ++ rho0) ((y, v) :: t ++ rho) b0 b.
Proof.
 intros k w rn rho0 rho e0 e x y b0 b v0 v t0 t Ht0 Ht Bo S0 S1 (L & W & I2 & I3 & I4 & I5) HV.
 destruct (binder_ok_ne _ _ Bo) as [Nx Ny].
 split; [exact L|]. split; [exact W|]. split; [|split; [|split]].
 - intros x' y' Ix Fr V. cbn [F.var_ok] in V. destruct (text_eqb x x') eqn:Ex.
   + apply text_eqb_eq in Ex. apply text_eqb_eq in V. subst x' y'. exists v0, v.
     rewrite !lookup_cons_eq. split; [reflexivity|split; [reflexivity|exact HV]].
   + destruct (text_eqb y y') eqn:Ey; [discriminate|].
     rewrite free_in_cons, Ex in Fr. cbn [negb andb] in Fr.
     assert (Nxx : x' <> x) by (intros ->; rewrite text_eqb_refl in Ex; discriminate).
     assert (Nyy : y' <> y) by (intros ->; rewrite text_eqb_refl in Ey; discriminate).
     destruct (I5 x' y' (var_ok_bound rn x' y' V Fr)) as [Ax Ay].
     destruct (I2 x' y' (S0 x' Ix Nxx) Fr V) as (u0 & u & E0 & E & U).
     exists u0, u. rewrite (lookup_cons_ne x' x), (lookup_tags t0 rho0 x') by assumption.
     rewrite (lookup_cons_ne y' y), (lookup_tags t rho y') by assumption. auto.
 - intros Ip Fp. rewrite free_in_cons in Fp. apply andb_true_iff in Fp as [Np Fp].
   assert (N : p4 <> x) by (intros ->; rewrite text_eqb_refl in Np; discriminate).
   rewrite (lookup_cons_ne p4 x), (lookup_tags t0 rho0 p4) by assumption. apply I3; [apply S0; assumption|exact Fp].
 - intros z Iz Hz Nz. rewrite hidden_cons in Hz. apply orb_false_iff in Hz as [Hy Hz].
   assert (N : z <> y) by (intros ->; rewrite text_eqb_refl in Hy; discriminate).
   rewrite (lookup_cons_ne z y), (lookup_tags t rho z) by assumption. apply I4; [apply S1; assumption|exact Hz|exact Nz].
 - intros a b' [E|I]; [injection E as <- <-; split; assumption|apply I5; exact I].
Qed.

Lemma Inv_tag : forall k w rn rho0 rho e0 e b0 b t0 t,
 (forall z, In z (map fst t0) -> z = id_key) -> (forall z, In z (map fst t) -> z = id_key) ->
 incl (fv b0) (fv e0) -> incl (fv b) (fv e) ->
 Inv k w rn rho0 rho e0 e -> Inv k w rn (t0 ++ rho0) (t ++ rho) b0 b.
Proof.
 intros k w rn rho0 rho e0 e b0 b t0 t Ht0 Ht S0 S1 (L & W & I2 & I3 & I4 & I5).
 split; [exact L|]. split; [exact W|]. split; [|split; [|split]].
 - intros x y Ix Fr V. destruct (I5 x y (var_ok_bound rn x y V Fr)) as [Ax Ay].
   rewrite (lookup_tags t0 rho0 x), (lookup_tags t rho y) by assumption. apply I2; [apply S0; exact Ix|exact Fr|exact V].
 - intros Ip Fp. rewrite (lookup_tags t0 rho0 p4) by assumption. apply I3; [apply S0; exact Ip|exact Fp].
 - intros z Iz Hz Nz. rewrite (lookup_tags t rho z) by assumption. apply I4; [apply S1; exact Iz|exact Hz|exact Nz].
 - exact I5.
Qed.

(* A source let whose name its body does not use. *)
Lemma Inv_dead : forall k w rn rho0 rho e0 e x v0 b0 b, ~ In x (fv b0) ->
 incl (fv b0) (fv e0) -> incl (fv b) (fv e) ->
 Inv k w rn rho0 rho e0 e -> Inv k w rn ((x, v0) :: rho0) rho b0 b.
Proof.
 intros k w rn rho0 rho e0 e x v0 b0 b Nx S0 S1 (L & W & I2 & I3 & I4 & I5).
 split; [exact L|]. split; [exact W|]. split; [|split; [|split]].
 - intros x' y Ix Fr V. rewrite (lookup_cons_ne x' x) by (intros ->; contradiction).
   apply I2; [apply S0; exact Ix|exact Fr|exact V].
 - intros Ip Fp. rewrite (lookup_cons_ne p4 x) by (intros ->; contradiction). apply I3; [apply S0; exact Ip|exact Fp].
 - intros z Iz. apply I4, S1, Iz.
 - exact I5.
Qed.

Lemma fund_k : forall k, fund_below k.
Proof.
 intros k. apply (JitKRefFund.JitKRefFund.fund_below_le sealed D (S k)); [lia|].
 apply JitKRefFund.JitKRefFund.fund_gen. exact Dw.
Qed.

Ltac incl_tac := let z := fresh "z" in let Iz := fresh "Iz" in
 intros z Iz; cbn [fv] in *;
 repeat (rewrite in_app_iff in * ); tauto.

Lemma in_fv_sub_list : forall (a : expr) l z, In a l -> In z (fv a) ->
 In z ((fix go (l : list expr) : list name := match l with [] => [] | a :: l => fv a ++ go l end) l).
Proof.
 intros a l z. induction l as [|b l IH]; intros I Z; [destruct I|]. cbn. apply in_app_iff.
 destruct I as [<-|I]; [left; exact Z|right; apply IH; assumption].
Qed.

Lemma in_fv_cond : forall (p : expr * expr) l z, In p l -> In z (fv (fst p)) \/ In z (fv (snd p)) ->
 In z ((fix go (l : list (expr * expr)) : list name := match l with
     | [] => [] | (c, b) :: l => fv c ++ fv b ++ go l end) l).
Proof.
 intros p l z. induction l as [|[c b] l IH]; intros I Z; [destruct I|]. cbn. rewrite !in_app_iff.
 destruct I as [<-|I]; [cbn in Z; tauto|right; right; apply IH; assumption].
Qed.

Theorem beq_sound : forall fuel rn e0 e k w rho0 rho, beq fuel tk p4 rn e0 e = true ->
 Inv k w rn rho0 rho e0 e -> ERel k w rho0 e0 rho e.
Proof.
 induction fuel as [|fuel IH]; intros rn e0 e k w rho0 rho H I; [discriminate|].
 pose proof (fund_k k) as FB.
 pose proof (JitKRefPrim.JitKRefPrim.prim_compat sealed D) as PC.
 assert (Sub : forall e0' e' j w', (j <= k)%nat -> wext w w' -> incl (fv e0') (fv e0) -> incl (fv e') (fv e) ->
   beq fuel tk p4 rn e0' e' = true -> ERel j w' rho0 e0' rho e').
 { intros e0' e' j w' L W S0 S1 B. apply (IH rn); [exact B|]. eapply Inv_sub; [exact S0|exact S1|].
   eapply Inv_mono; [exact L|exact W|exact I]. }
 assert (Sub0 : forall e0' e', incl (fv e0') (fv e0) -> incl (fv e') (fv e) ->
   beq fuel tk p4 rn e0' e' = true -> ERel k w rho0 e0' rho e').
 { intros e0' e' S0 S1 B. apply (Sub e0' e' k w); [lia|apply wext_refl; destruct I as (_ & W & _); exact (proj2 W)|exact S0|exact S1|exact B]. }
 pose proof I as I0. destruct I as (Lk & Wk & I2 & I3 & I4 & I5).
 assert (Ww : wf_world w) by exact (proj2 Wk).
 destruct e0 as [n0|t0|s0|bb0| |x0|x0 b0|x0 a0 b0|c0 a0 b0|a0 b0|a0 b0|cl0|a0 h0|b0|a0|f0 ps0 b0|h0 l0|f0 l0];
  cbn [beq] in H.
 - (* ENum *) destruct e; try discriminate. apply num_eqb_eq in H. subst.
   eapply JitKRefCompatCtl.JitKRefCompatCtl.ERel_sval; [reflexivity|reflexivity|].
   apply (JitKRefCompatCtl.JitKRefCompatCtl.VRel_lit sealed D k w (ENum n)). reflexivity.
 - destruct e; try discriminate. apply text_eqb_eq in H. subst.
   eapply JitKRefCompatCtl.JitKRefCompatCtl.ERel_sval; [reflexivity|reflexivity|].
   apply (JitKRefCompatCtl.JitKRefCompatCtl.VRel_lit sealed D k w (EStr t)). reflexivity.
 - destruct e; try discriminate. apply text_eqb_eq in H. subst.
   eapply JitKRefCompatCtl.JitKRefCompatCtl.ERel_sval; [reflexivity|reflexivity|].
   apply (JitKRefCompatCtl.JitKRefCompatCtl.VRel_lit sealed D k w (ESym s)). reflexivity.
 - destruct e; try discriminate. apply Bool.eqb_prop in H. subst.
   eapply JitKRefCompatCtl.JitKRefCompatCtl.ERel_sval; [reflexivity|reflexivity|].
   apply (JitKRefCompatCtl.JitKRefCompatCtl.VRel_lit sealed D k w (EBool b)). reflexivity.
 - destruct e; try discriminate.
   eapply JitKRefCompatCtl.JitKRefCompatCtl.ERel_sval; [reflexivity|reflexivity|].
   apply (JitKRefCompatCtl.JitKRefCompatCtl.VRel_lit sealed D k w ENil). reflexivity.
 - (* EVar *) destruct e; try discriminate. apply andb_true_iff in H as [Fr V].
   apply negb_true_iff in Fr.
   destruct (I2 x0 x ltac:(left; reflexivity) Fr V) as (v0 & v & E0 & E & HV).
   eapply JitKRefCompatCtl.JitKRefCompatCtl.ERel_sval; [exact E0|exact E|exact HV].
 - (* ELam *) destruct e; try discriminate. apply andb_true_iff in H as [Bo B].
   apply JitKRefCompatClo.JitKRefCompatClo.lam_core. intros j w' l0 l a0 a L W Il HA.
   apply (IH ((x0, x) :: rn)); [exact B|].
   change ((x0, a0) :: (id_key, VVec l0) :: rho0) with ((x0, a0) :: [(id_key, VVec l0)] ++ rho0).
   change ((x, a) :: (id_key, VVec l) :: rho) with ((x, a) :: [(id_key, VVec l)] ++ rho).
   apply (Inv_bind j w' rn rho0 rho (ELam x0 b0) (ELam x e)).
   + intros z [<-|[]]; reflexivity.
   + intros z [<-|[]]; reflexivity.
   + exact Bo.
   + intros z Iz Nz. cbn [fv]. apply In_fv_filter. split; assumption.
   + intros z Iz Nz. cbn [fv]. apply In_fv_filter. split; assumption.
   + apply (Inv_mono k j w w'); [lia|exact W|exact I0].
   + exact HA.
 - (* ELet *) destruct e; try discriminate.
   + (* let against let *) apply andb_true_iff in H as [H Bb]. apply andb_true_iff in H as [Bo Ba].
     apply JitKRefCompatCtl.JitKRefCompatCtl.ERel_let.
     * apply Sub0; [incl_tac|incl_tac|exact Ba].
     * intros j w' v0 v L W HV. apply (IH ((x0, x) :: rn)); [exact Bb|].
       change ((x0, v0) :: rho0) with ((x0, v0) :: [] ++ rho0). change ((x, v) :: rho) with ((x, v) :: [] ++ rho).
       apply (Inv_bind j w' rn rho0 rho (ELet x0 a0 b0) (ELet x e1 e2)).
       -- intros z [].
       -- intros z [].
       -- exact Bo.
       -- intros z Iz Nz. cbn [fv]. apply in_app_iff. right. apply In_fv_filter. split; assumption.
       -- intros z Iz Nz. cbn [fv]. apply in_app_iff. right. apply In_fv_filter. split; assumption.
       -- apply (Inv_mono k j w w'); [exact L|exact W|exact I0].
       -- exact HV.
   + (* let against do *) destruct args as [|a [|b [|]]]; try discriminate.
     apply andb_true_iff in H as [H Bb]. apply andb_true_iff in H as [H Ba]. apply andb_true_iff in H as [Ed Nb].
     apply text_eqb_eq in Ed. subst f. apply negb_true_iff in Nb.
     assert (Nx : ~ In x0 (fv b0)) by (intros Ix; apply bound_iff in Ix; congruence).
     apply (ERel_letdo v1 v2 Hdo Hv12).
     * apply Sub0; [incl_tac|incl_tac|exact Ba].
     * intros j w' v0 L W. apply (IH rn); [exact Bb|].
       apply (Inv_dead j w' rn rho0 rho (ELet x0 a0 b0) (ECall do_name [a; b])); [exact Nx| | |].
       -- intros z Iz. cbn [fv]. apply in_app_iff. right. apply In_fv_filter. split; [exact Iz|intros ->; contradiction].
       -- incl_tac.
       -- apply (Inv_mono k j w w'); [exact L|exact W|exact I0].
 - (* EIf *) destruct e; try discriminate. apply andb_true_iff in H as [H Bb]. apply andb_true_iff in H as [Bc Ba].
   apply JitKRefCompatCtl.JitKRefCompatCtl.ERel_if; apply Sub0; try incl_tac; assumption.
 - (* EAnd *) destruct e; try discriminate. apply andb_true_iff in H as [Ba Bb].
   apply JitKRefCompatCtl.JitKRefCompatCtl.ERel_and; apply Sub0; try incl_tac; assumption.
 - (* EOr *) destruct e; try discriminate. apply andb_true_iff in H as [Ba Bb].
   apply JitKRefCompatCtl.JitKRefCompatCtl.ERel_or; apply Sub0; try incl_tac; assumption.
 - (* ECond *) destruct e; try discriminate. apply JitKRefCompatCtl.JitKRefCompatCtl.ERel_cond.
   eapply forall2b_sound; [|exact H]. intros p0 p Ip0 Ip Bp. apply andb_true_iff in Bp as [B1 B2].
   split; apply Sub0; try assumption; intros z Iz; cbn [fv]; eapply in_fv_cond; eauto.
 - (* ETrap *) destruct e; try discriminate. apply andb_true_iff in H as [Ba Bh].
   apply JitKRefCompatCtl.JitKRefCompatCtl.ERel_trap; [apply JitKRefCompatCtl.JitKRefCompatCtl.AppExn_fb; exact FB| |];
    apply Sub0; try incl_tac; assumption.
 - (* EFreeze *) destruct e; try discriminate.
   apply JitKRefCompatClo.JitKRefCompatClo.frz_core. intros j w' l0 l L W Il.
   apply (IH rn); [exact H|].
   change ((id_key, VVec l0) :: rho0) with ([(id_key, VVec l0)] ++ rho0).
   change ((id_key, VVec l) :: rho) with ([(id_key, VVec l)] ++ rho).
   apply (Inv_tag j w' rn rho0 rho (EFreeze b0) (EFreeze e)).
   + intros z [<-|[]]; reflexivity.
   + intros z [<-|[]]; reflexivity.
   + intros z Iz; exact Iz.
   + intros z Iz; exact Iz.
   + apply (Inv_mono k j w w'); [lia|exact W|exact I0].
 - (* EType *) destruct e; try discriminate. apply JitKRefCompatCtl.JitKRefCompatCtl.ERel_type.
   apply Sub0; [intros z Iz; exact Iz|intros z Iz; exact Iz|exact H].
 - (* EDefun *) destruct e; discriminate.
 - (* EApp *)
   assert (Gen : forall h l, e = EApp h l -> (beq fuel tk p4 rn h0 h && forall2b (beq fuel tk p4 rn) l0 l)%bool = true ->
     ERel k w rho0 (EApp h0 l0) rho (EApp h l)).
   { intros h l Ee B. subst e. apply andb_true_iff in B as [Bh Bl].
     apply JitKRefCompatClo.JitKRefCompatClo.compat_app_core; [exact FB|exact PC| |].
     - intros j w' L W. apply (Sub h0 h j w'); [lia|exact W| | |exact Bh]; intros z Iz; cbn [fv]; apply in_app_iff; left; exact Iz.
     - eapply forall2b_sound; [|exact Bl]. intros a0 a Ia0 Ia Ba j w' L W.
       apply (Sub a0 a j w'); [lia|exact W| | |exact Ba]; intros z Iz; cbn [fv]; apply in_app_iff; right;
        eapply in_fv_sub_list; eauto. }
   destruct h0 as [| | | | |p| | | | | | | | | | | |]; try (destruct e; try discriminate; apply Gen; [reflexivity|exact H]).
   destruct l0 as [|a0 l0]; [|destruct e; try discriminate; apply Gen; [reflexivity|exact H]].
   destruct (F.free_in rn p) eqn:Fp.
   + (* the thawed place *)
     apply andb_true_iff in H as [H Tk]. apply andb_true_iff in H as [H Nid]. apply andb_true_iff in H as [Ep Hid].
     apply text_eqb_eq in Ep. subst p. apply negb_true_iff in Nid.
     assert (Lp : lookup p4 rho0 = Some (VFrozen ex0 rc0)) by (apply I3; [left; reflexivity|exact Fp]).
     apply ERel_anti. intros j w' K0 s0 s L W HS. exists rc0, ex0, s0. split; [|split; [exact HS|]].
     * eapply srun_tau; [reflexivity|]. eapply srun_tau; [apply sval_next; exact Lp|].
       eapply srun_tau; [reflexivity|apply srun_refl].
     * apply (HTK e Tk j w' rc0 rho); [exact (proj2 (wext_trans _ _ _ Wk W))|].
       intros x Ix. apply filter_In in Ix as [Ig Ie]. apply bound_iff in Ie.
       assert (Nk : x <> id_key) by (intros ->; apply bound_iff in Ie; congruence).
       assert (Hx : F.hidden rn x = false).
       { apply forallb_forall with (x := x) in Hid; [|exact Ie]. apply negb_true_iff in Hid. exact Hid. }
       destruct (HE x Ig Nk) as (v0 & v & E0 & E & HV). exists v0, v.
       split; [exact E0|]. split; [rewrite (I4 x Ie Hx Nk); exact E|].
       eapply VRel_mono; [|exact (wext_trans _ _ _ Wk W)|exact HV]. lia.
   + destruct e; try discriminate. destruct args; try discriminate.
     apply JitKRefCompatClo.JitKRefCompatClo.compat_app_core; [exact FB|exact PC| |constructor].
     intros j w' L W. apply (Sub (EVar p) e j w'); [lia|exact W|incl_tac|incl_tac|exact H].
 - (* ECall *) destruct e; try discriminate. apply andb_true_iff in H as [Ef Bl]. apply text_eqb_eq in Ef. subst f0.
   apply JitKRefCompatCall.JitKRefCompatCall.compat_call_core; [exact FB|exact PC|].
   eapply forall2b_sound; [|exact Bl]. intros a0 a Ia0 Ia Ba j w' L W.
   apply (Sub a0 a j w'); [lia|exact W| | |exact Ba]; intros z Iz; cbn [fv]; eapply in_fv_sub_list; eauto.
Qed.
End Beq.

Section Bind.

(* ======================= the bound-now rule is sound ======================= *)
Lemma len_app' : forall {A} (l1 l2 : list A), List.length (l1 ++ l2) = (List.length l1 + List.length l2)%nat.
Proof. intros A l1 l2. induction l1 as [|a l1 IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma len_rev' : forall {A} (l : list A), List.length (rev l) = List.length l.
Proof. intros A l. induction l as [|a l IH]; cbn; [reflexivity|]. rewrite len_app', IH. cbn. lia. Qed.

Lemma lookup_some_In : forall {A} x (l : list (name * A)) v, lookup x l = Some v -> In (x, v) l.
Proof.
 intros A x l v. induction l as [|[y u] l IH]; cbn; [discriminate|]. destruct (text_eqb x y) eqn:E.
 - intros H. injection H as <-. apply text_eqb_eq in E. subst. left. reflexivity.
 - intros H. right. apply IH. exact H.
Qed.

Lemma text_eqb_false : forall a b, text_eqb a b = false -> a <> b.
Proof. intros a b E ->. rewrite text_eqb_refl in E. discriminate. Qed.

Lemma EnvRel_notin : forall k w g rho0 rho y v, ~ In y g ->
 EnvRel_with (VRel k) w g rho0 rho -> EnvRel_with (VRel k) w g rho0 ((y, v) :: rho).
Proof.
 intros k w g rho0 rho y v N HE x Ix. destruct (HE x Ix) as (v0 & u & E0 & E & U). exists v0, u.
 rewrite lookup_cons_ne by (intros ->; contradiction). auto.
Qed.

Lemma next_ca_call : forall v g done rho K s,
 next_r R P (Cfg (Ret v) (KCallArgs g done [] rho :: K) s) = call_named_r R P g (rev (v :: done)) K s.
Proof. reflexivity. Qed.

Lemma next_ELet : forall r y a T K s, next_r R P (Cfg (Eval r (ELet y a T)) K s) = MTau (Cfg (Eval r a) (KLet y T r :: K) s).
Proof. reflexivity. Qed.

(* The source's argument frame against the target's let frame: the next argument against the next
   let's value. *)
Lemma KRel_ca_let : forall k w f done0 a0 rest0 rho0 x y a T rho K0 K,
 KRel k w K0 K ->
 (forall j w' v0 v, (j <= k)%nat -> wext w w' -> VRel j w' v0 v ->
    ERel j w' rho0 a0 ((x, v) :: rho) a /\
    KRel j w' (KCallArgs f (v0 :: done0) rest0 rho0 :: K0) (KLet y T ((x, v) :: rho) :: K)) ->
 KRel k w (KCallArgs f done0 (a0 :: rest0) rho0 :: K0) (KLet x (ELet y a T) rho :: K).
Proof.
 intros k w f done0 a0 rest0 rho0 x y a T rho K0 K HK H.
 apply ret_frame_tau; [exact HK|reflexivity|reflexivity| |intros v s; eexists; apply next_KLet].
 intros j w' v0 v s0 s c1 L W HV HS E. rewrite next_KLet in E. injection E as <-.
 eexists; split; [eapply srun_tau; [apply next_KCallArgs_cons|apply srun_refl]|].
 destruct j as [|j]; [apply ObsT_0|].
 destruct (H j w' v0 v ltac:(lia) W ltac:(eapply VRel_down; [|exact HV]; lia)) as [Ha HK'].
 apply ObsT_running.
 - reflexivity.
 - unfold nonterm. rewrite next_ELet. exact I.
 - intros x'. cbn [kont mem]. apply ObsT_throw_src; [reflexivity|].
   apply (KRel_throw sealed D); [eapply KRel_mono; [|exact W|exact HK]; lia|eapply SRel_down; [|exact HS]; lia].
 - intros c2 E2. rewrite next_ELet in E2. injection E2 as <-. eexists; split; [apply srun_refl|].
   eapply ERel_apply; [exact Ha|apply le_n|eapply wext_self; exact HS|exact HK'|eapply SRel_down; [|exact HS]; lia].
 - intros q kk r E2. rewrite next_ELet in E2. discriminate.
Qed.

(* The last argument, (freeze E0), and the call, against the last let: the source allocates the
   closure (a cell the target does not have) and enters the callee's body. *)
Lemma KRel_ca_last : forall k w f ps eB done0 ex rho0 x n rho K0 K,
 In (f, FUser ps eB) D -> List.length ps = S (S (List.length done0)) ->
 KRel k w K0 K ->
 (forall j w' v0 v l, (j <= k)%nat -> wext w w' -> VRel j w' v0 v ->
    ERel j w' (combine ps (rev (VFrozen ex ((id_key, VVec l) :: rho0) :: v0 :: done0))) eB ((x, v) :: rho) n) ->
 KRel k w (KCallArgs f done0 [EFreeze ex] rho0 :: K0) (KLet x n rho :: K).
Proof.
 intros k w f ps eB done0 ex rho0 x n rho K0 K Id Lp HK H.
 apply ret_frame_tau; [exact HK|reflexivity|reflexivity| |intros v s; eexists; apply next_KLet].
 intros j w' v0 v s0 s c1 L W HV HS E. rewrite next_KLet in E. injection E as <-.
 assert (Hs0 : JitKRef.JitKRef.StoreHas D s0) by (destruct HS as (_ & H0 & _); exact H0).
 eexists; split.
 - eapply srun_tau; [apply next_KCallArgs_cons|].
   eapply srun_tau; [apply JitKRefCompatClo.JitKRefCompatClo.next_frz|].
   eapply srun_tau; [|apply srun_refl].
   rewrite next_ca_call. apply call_named_user; [exact (Hs0 f _ Id)|rewrite len_rev', Lp; reflexivity].
 - eapply ERel_apply.
   + apply (H j w' v0 v (List.length (heap s0))); [lia|exact W|eapply VRel_down; [|exact HV]; lia].
   + apply le_n.
   + eapply wext_self; exact HS.
   + eapply KRel_mono; [|exact W|exact HK]; lia.
   + apply SRel_with_cell. eapply SRel_down; [|exact HS]; lia.
Qed.

(* The rule's checks, read off. *)
Lemma bind_rule_inv : forall rec g e0 e, bind_rule D rec g e0 e = true ->
 exists x0 y0 b0 ex0 a1 x a2 y a3 b n p1 p2 p3 p4 eB v1 v2,
 e0 = ECall F.bind_name [x0; y0; b0; EFreeze ex0] /\ e = ELet a1 x (ELet a2 y (ELet a3 b n)) /\
 lookup F.bind_name D = Some (FUser [p1; p2; p3; p4] eB) /\ lookup do_name D = Some (FUser [v1; v2] (EVar v2)) /\
 text_eqb v1 v2 = false /\ nodupb [p1; p2; p3; p4] = true /\ text_eqb p4 id_key = false /\
 F.binder_ok p1 a1 = true /\ F.binder_ok p2 a2 = true /\ F.binder_ok p3 a3 = true /\ F.disjoint [a1; a2; a3] g = true /\
 rec g x0 x = true /\ rec g y0 y = true /\ rec g b0 b = true /\
 beq (S (F.dsize eB)) (fun e' => rec (gfv g e') ex0 e') p4 [(p3, a3); (p2, a2); (p1, a1)] eB n = true.
Proof.
 intros rec g e0 e H. unfold bind_rule in H.
 destruct e0 as [| | | | | | | | | | | | | | | | |f args]; try discriminate H.
 destruct e as [| | | | | | |a1 x e1| | | | | | | | | |];
  try (destruct args as [|? [|? [|? [|[| | | | | | | | | | | | |?| | | |] [|]]]]]; discriminate H).
 destruct e1 as [| | | | | | |a2 y e2| | | | | | | | | |];
  try (destruct args as [|? [|? [|? [|[| | | | | | | | | | | | |?| | | |] [|]]]]]; discriminate H).
 destruct e2 as [| | | | | | |a3 b n| | | | | | | | | |];
  try (destruct args as [|? [|? [|? [|[| | | | | | | | | | | | |?| | | |] [|]]]]]; discriminate H).
 destruct args as [|x0 [|y0 [|b0 [|fz [|]]]]]; try discriminate H;
  destruct fz as [| | | | | | | | | | | | |ex0| | | |]; try discriminate H.
 apply andb_true_iff in H as [Ef H]. apply text_eqb_eq in Ef. subst f.
 destruct (lookup F.bind_name D) as [[q|ps eB]|] eqn:LB; try discriminate H.
 destruct ps as [|p1 [|p2 [|p3 [|p4 [|]]]]]; try discriminate H.
 destruct (lookup do_name D) as [[q|vs ed]|] eqn:LD; try discriminate H.
 destruct vs as [|v1 [|v2 [|]]]; try discriminate H.
 destruct ed as [| | | | |v2'| | | | | | | | | | | |]; try discriminate H.
 repeat (apply andb_true_iff in H as [H ?]).
 match goal with E : text_eqb v2 v2' = true |- _ => apply text_eqb_eq in E; subst v2' end.
 exists x0, y0, b0, ex0, a1, x, a2, y, a3, b, n, p1, p2, p3, p4, eB, v1, v2.
 repeat split; try reflexivity; try assumption; apply negb_true_iff; assumption.
Qed.

Theorem bind_rule_sound : D_wf -> rule_sound (bind_rule D).
Proof.
 intros Dw rec Hrec g e0 e H.
 destruct (bind_rule_inv rec g e0 e H) as (x0 & y0 & b0 & ex0 & a1 & x & a2 & y & a3 & b & n & p1 & p2 & p3 & p4 & eB & v1 & v2 &
   -> & -> & LB & LD & V12 & ND & P4 & B1 & B2 & B3 & Dj & Rx & Ry & Rb & Bq).
 apply text_eqb_false in V12. apply text_eqb_false in P4.
 (* distinct parameters *)
 cbn [nodupb bound existsb] in ND. rewrite !orb_false_r in ND.
 repeat (apply andb_true_iff in ND as [? ND]). rewrite !negb_orb in *.
 repeat match goal with Hn : (negb _ && _)%bool = true |- _ => apply andb_true_iff in Hn as [? ?] end.
 repeat match goal with Hn : negb (text_eqb _ _) = true |- _ => apply negb_true_iff in Hn; apply text_eqb_false in Hn end.
 (* the fresh names are outside g *)
 unfold F.disjoint in Dj. cbn [forallb] in Dj. rewrite andb_true_r in Dj.
 apply andb_true_iff in Dj as [G1 Dj]. apply andb_true_iff in Dj as [G2 G3].
 apply negb_true_iff in G1, G2, G3.
 assert (N1 : ~ In a1 g) by (intros I; apply bound_iff in I; congruence).
 assert (N2 : ~ In a2 g) by (intros I; apply bound_iff in I; congruence).
 assert (N3 : ~ In a3 g) by (intros I; apply bound_iff in I; congruence).
 destruct (binder_ok_ne _ _ B1) as [Np1 Na1]. destruct (binder_ok_ne _ _ B2) as [Np2 Na2].
 destruct (binder_ok_ne _ _ B3) as [Np3 Na3].
 pose proof (lookup_some_In _ _ _ LB) as IB. pose proof (lookup_some_In _ _ _ LD) as ID.
 pose proof (Hrec _ _ _ Rx) as Kx. pose proof (Hrec _ _ _ Ry) as Ky. pose proof (Hrec _ _ _ Rb) as Kb.
 intros k w rho0 rho Ww HEnv.
 apply (ERel_push sealed D k w rho0 _ rho _ rho0 x0 rho x
   (fun K0 => KCallArgs F.bind_name [] [y0; b0; EFreeze ex0] rho0 :: K0) (fun K => KLet a1 (ELet a2 y (ELet a3 b n)) rho :: K)).
 - intros; reflexivity.
 - intros; reflexivity.
 - intros j1 w1 K0 K L1 W1 HK. apply KRel_ca_let; [exact HK|]. intros j2 w2 vx0 vx L2 W2 HV2. split.
   + apply Ky; [exact (proj2 W2)|]. apply EnvRel_notin; [exact N1|].
     eapply EnvRel_mono; [|eapply wext_trans; [exact W1|exact W2]|exact HEnv]. lia.
   + apply KRel_ca_let; [eapply KRel_mono; [exact L2|exact W2|exact HK]|]. intros j3 w3 vy0 vy L3 W3 HV3. split.
     * apply Kb; [exact (proj2 W3)|]. apply EnvRel_notin; [exact N2|]. apply EnvRel_notin; [exact N1|].
       eapply EnvRel_mono; [|eapply wext_trans; [eapply wext_trans; [exact W1|exact W2]|exact W3]|exact HEnv]. lia.
     * apply (KRel_ca_last _ _ F.bind_name [p1; p2; p3; p4] eB [vy0; vx0]); [exact IB|reflexivity|eapply KRel_mono; [|exact W3|eapply KRel_mono; [exact L2|exact W2|exact HK]]; lia|].
       intros j4 w4 vb0 vb l L4 W4 HV4. cbn [rev app combine].
       assert (W14 : wext w w4) by (eapply wext_trans; [eapply wext_trans; [eapply wext_trans; [exact W1|exact W2]|exact W3]|exact W4]).
       apply (beq_sound Dw (fun e' => rec (gfv g e') ex0 e') p4 ex0 ((id_key, VVec l) :: rho0) rho g j4 w4)
         with (v1 := v1) (v2 := v2) (fuel := S (F.dsize eB)) (rn := [(p3, a3); (p2, a2); (p1, a1)]).
       -- intros e' T. exact (Hrec _ _ _ T).
       -- intros x' Ix Nx. rewrite lookup_cons_ne by exact Nx. destruct (HEnv x' Ix) as (u0 & u & E0 & E & U).
          exists u0, u. split; [exact E0|split; [exact E|eapply VRel_mono; [|exact W14|exact U]; lia]].
       -- exact P4.
       -- exact ID.
       -- exact V12.
       -- exact Bq.
       -- split; [apply le_n|]. split; [apply wext_refl; exact (proj2 W4)|]. split; [|split; [|split]].
          ++ intros x' y' Ix Fr V. cbn [F.var_ok] in V. unfold F.free_in in Fr. cbn [existsb fst] in Fr.
             destruct (text_eqb p3 x') eqn:E3.
             ** apply text_eqb_eq in E3. apply text_eqb_eq in V. subst x' y'. exists vb0, vb.
                rewrite (lookup_cons_ne p3 p1), (lookup_cons_ne p3 p2), lookup_cons_eq by congruence.
                rewrite lookup_cons_eq. split; [reflexivity|split; [reflexivity|exact HV4]].
             ** destruct (text_eqb a3 y') eqn:F3; [discriminate|]. destruct (text_eqb p2 x') eqn:E2.
                --- apply text_eqb_eq in E2. apply text_eqb_eq in V. subst x' y'. exists vy0, vy.
                    rewrite (lookup_cons_ne p2 p1), lookup_cons_eq by congruence.
                    rewrite (lookup_cons_ne a2 a3) by (apply text_eqb_false in F3; congruence). rewrite lookup_cons_eq.
                    split; [reflexivity|split; [reflexivity|eapply VRel_mono; [|exact W4|exact HV3]; lia]].
                --- destruct (text_eqb a2 y') eqn:F2; [discriminate|]. destruct (text_eqb p1 x') eqn:E1.
                    +++ apply text_eqb_eq in E1. apply text_eqb_eq in V. subst x' y'. exists vx0, vx.
                        rewrite lookup_cons_eq.
                        rewrite (lookup_cons_ne a1 a3) by (apply text_eqb_false in F3; congruence).
                        rewrite (lookup_cons_ne a1 a2) by (apply text_eqb_false in F2; congruence). rewrite lookup_cons_eq.
                        split; [reflexivity|split; [reflexivity|]].
                        eapply VRel_mono; [|eapply wext_trans; [exact W3|exact W4]|exact HV2]; lia.
                    +++ discriminate.
          ++ intros Ip Fp. rewrite (lookup_cons_ne p4 p1), (lookup_cons_ne p4 p2), (lookup_cons_ne p4 p3) by congruence.
             rewrite lookup_cons_eq. reflexivity.
          ++ intros z Iz Hz Nz. unfold F.hidden in Hz. cbn [existsb snd] in Hz. rewrite orb_false_r in Hz.
             apply orb_false_iff in Hz as [Z3 Hz]. apply orb_false_iff in Hz as [Z2 Z1].
             apply text_eqb_false in Z1, Z2, Z3.
             rewrite (lookup_cons_ne z a3), (lookup_cons_ne z a2), (lookup_cons_ne z a1) by congruence. reflexivity.
          ++ intros a' b' [E|[E|[E|[]]]]; injection E as <- <-; split; assumption.
 - intros j1 w1 L1 W1. apply Kx; [exact (proj2 W1)|]. eapply EnvRel_mono; [|exact W1|exact HEnv]. lia.
Qed.
End Bind.
End Sound.

(* ======================= D00's bind_site_sound_statement is false ======================= *)
(* The counterexample: shen.bind!'s body only thaws its fourth parameter, and the frozen body reads
   KLPort's closure-identity key. The source's freeze closure binds id_key to its own fresh cell
   (tagged_env), so the source returns that cell, (VVec 0); the expansion runs the body in place,
   where id_key is the caller's (here a number). bind_site accepts the pair (it checks the thawed
   body's free names against the fresh names and inl_eq's hidden target binders, not against
   id_key), and every premise of the statement holds, yet the target returns 0 where the source
   can only return the cell or raise a resource error. *)
Definition cx_n (t : string) : name := of_string t.
Definition cx_sealed : list name := [F.bind_name; do_name].
Definition cx_D : list (name * fundef) :=
 [(F.bind_name, FUser [cx_n "p1"; cx_n "p2"; cx_n "p3"; cx_n "p4"] (EApp (EVar (cx_n "p4")) []));
  (do_name, FUser [cx_n "d1"; cx_n "d2"] (EVar (cx_n "d2")))].
Definition cx_one : expr := ENum (NInt 1).
Definition cx_args : list expr := [cx_one; cx_one; cx_one; EFreeze (EVar id_key)].
Definition cx_e : expr :=
 ELet (cx_n "a1") cx_one (ELet (cx_n "a2") cx_one (ELet (cx_n "a3") cx_one (EVar id_key))).
Definition cx_rho : lenv := [(id_key, VNum (NInt 0))].
Definition cx_st : store := Store [] [] cx_D.

Example cx_bind_site : F.bind_site false cx_D cx_args cx_e = true.
Proof. vm_compute. reflexivity. Qed.

(* bind_rule refuses the same pair: the thawed place reads id_key. *)
Example bind_rule_rejects_id_key : bind_rule cx_D (fun _ _ _ => true) [id_key] (ECall F.bind_name cx_args) cx_e = false.
Proof. vm_compute. reflexivity. Qed.

(* A deterministic run, iterated from its end. *)
Fixpoint iter_tau (sealed : list name) (n : nat) (c : config) : option config := match n with
 | O => Some c
 | S n => match iter_tau sealed n c with
   | Some c' => match next_r (jit_rules sealed) jit_profile c' with MTau c'' => Some c'' | _ => None end
   | None => None end end.

Lemma runs_snoc : forall sealed n c t c' c'', JitKRef.JitKRef.runs sealed n c t c' ->
 next_r (jit_rules sealed) jit_profile c' = MTau c'' -> JitKRef.JitKRef.runs sealed (S n) c t c''.
Proof.
 intros sealed n c t c' c'' H. induction H as [c|n c l c1 t c2 St Hr IH]; intros E.
 - change [] with (trace_of Tau ++ []). econstructor; [apply step_r_tau; exact E|constructor].
 - econstructor; [exact St|apply IH; exact E].
Qed.

Lemma iter_runs : forall sealed n c c', iter_tau sealed n c = Some c' -> JitKRef.JitKRef.runs sealed n c [] c'.
Proof.
 intros sealed n. induction n as [|n IH]; intros c c' H; cbn in H.
 - injection H as <-. constructor.
 - destruct (iter_tau sealed n c) as [c1|] eqn:E; [|discriminate].
   destruct (next_r (jit_rules sealed) jit_profile c1) eqn:N; try discriminate. injection H as <-.
   eapply runs_snoc; [apply IH; exact E|exact N].
Qed.

Lemma iter_none : forall sealed n c, iter_tau sealed n c = None -> iter_tau sealed (S n) c = None.
Proof. intros sealed n c H. cbn. rewrite H. reflexivity. Qed.

Lemma iter_none_ge : forall sealed m c, iter_tau sealed m c = None -> forall i, (m <= i)%nat -> iter_tau sealed i c = None.
Proof.
 intros sealed m c H i L. induction L as [|i L IH]; [exact H|]. apply iter_none. exact IH.
Qed.

Definition no_io (m : move) : bool := match m with MIO _ _ => false | _ => true end.

(* Every configuration a source run reaches, when the deterministic chain never asks for IO and its
   continuations hold no trap: a configuration of the chain, or an exception unwinding trap-free
   frames (a resource error raised on the way). *)
Lemma star_reach : forall sealed c0 m,
 (forall i c, (i <= m)%nat -> iter_tau sealed i c0 = Some c ->
   no_io (next_r (jit_rules sealed) jit_profile c) = true /\ forallb JitKRefBase.JitKRefBase.nontrap (kont c) = true) ->
 iter_tau sealed (S m) c0 = None ->
 forall t c, JitKRef.JitKRef.srun sealed c0 t c ->
 (exists i, (i <= m)%nat /\ iter_tau sealed i c0 = Some c) \/
 (exists x K s, c = Cfg (Throw x) K s /\ forallb JitKRefBase.JitKRefBase.nontrap K = true).
Proof.
 intros sealed c0 m Hc Hn t c Hs.
 assert (Bd : forall i c, iter_tau sealed i c0 = Some c -> (i <= m)%nat).
 { intros i c1 E. destruct (Nat.le_gt_cases i m) as [L|L]; [exact L|].
   rewrite (iter_none_ge sealed (S m) c0 Hn i L) in E. discriminate. }
 assert (G : forall c1, (exists i, (i <= m)%nat /\ iter_tau sealed i c0 = Some c1) \/
   (exists x K s, c1 = Cfg (Throw x) K s /\ forallb JitKRefBase.JitKRefBase.nontrap K = true) ->
   forall t c2, JitKRef.JitKRef.srun sealed c1 t c2 ->
   (exists i, (i <= m)%nat /\ iter_tau sealed i c0 = Some c2) \/
   (exists x K s, c2 = Cfg (Throw x) K s /\ forallb JitKRefBase.JitKRefBase.nontrap K = true)).
 { intros c1 Hc1 t1 c2 H2. unfold JitKRef.JitKRef.srun in H2.
   induction H2 as [c1|c1 l c1' t1 c2 St H2 IH]; [exact Hc1|]. apply IH. clear IH H2.
   destruct (step_r_cases sealed _ _ _ St) as [[E ->]|[(q & kk & r & E & -> & ->)|(r & x & Rc & Rx & -> & ->)]].
   - destruct Hc1 as [(i & L & Ei)|(x & K & s & -> & NK)].
     + left. exists (S i). split; [|cbn; rewrite Ei, E; reflexivity].
       apply (Bd (S i) c1'). cbn. rewrite Ei, E. reflexivity.
     + right. destruct K as [|f K]; [discriminate|]. cbn in NK. apply andb_true_iff in NK as [Nf NK].
       rewrite throw_frame_next in E by exact Nf. injection E as <-. exists x, K, s. split; [reflexivity|exact NK].
   - exfalso. destruct Hc1 as [(i & L & Ei)|(x & K & s & -> & NK)].
     + destruct (Hc i c1 L Ei) as [Io _]. rewrite E in Io. discriminate.
     + destruct K as [|f K]; [discriminate|]. cbn in NK. apply andb_true_iff in NK as [Nf _].
       rewrite throw_frame_next in E by exact Nf. discriminate.
   - right. destruct Hc1 as [(i & L & Ei)|(y & K & s & -> & NK)].
     + exists x, (kont c1), (mem c1). split; [reflexivity|]. exact (proj2 (Hc i c1 L Ei)).
     + cbn in Rc. discriminate. }
 apply (G c0 ltac:(left; exists 0%nat; split; [lia|reflexivity]) t c Hs).
Qed.

Theorem bind_site_unsound : ~ F.bind_site_sound_statement cx_sealed cx_D.
Proof.
 intros H.
 assert (NB : F.bind_name <> do_name) by (apply text_eqb_false; vm_compute; reflexivity).
 assert (Dw : JitKRef.JitKRef.D_wf cx_sealed cx_D).
 { split.
   - constructor; [left; reflexivity|constructor; [right; left; reflexivity|constructor]].
   - cbn. constructor; [intros [E|[]]; exact (NB (eq_sym E))|constructor; [intros []|constructor]]. }
 assert (Hdo : F.D_has_kernel_do cx_D).
 { exists (cx_n "d1"), (cx_n "d2"). split; [apply text_eqb_false; vm_compute; reflexivity|right; left; reflexivity]. }
 assert (Hargs : Forall2 (JitKRef.JitKRef.KRef cx_sealed cx_D [id_key]) cx_args cx_args).
 { assert (L1 : JitKRef.JitKRef.KRef cx_sealed cx_D [id_key] cx_one cx_one)
     by (apply (JitKRefCompatCtl.JitKRefCompatCtl.compat_lit cx_sealed cx_D [id_key] cx_one (VNum (NInt 1))); reflexivity).
   unfold cx_args. constructor; [exact L1|constructor; [exact L1|constructor; [exact L1|constructor; [|constructor]]]].
   apply (JitKRefCompatClo.JitKRefCompatClo.compat_freeze cx_sealed cx_D [id_key] (EVar id_key) (EVar id_key)).
   apply (JitKRefCompatCtl.JitKRefCompatCtl.compat_var cx_sealed cx_D [id_key] id_key). left. reflexivity. }
 specialize (H false [id_key] cx_args cx_args cx_e Dw (fun E => ltac:(discriminate E)) Hdo cx_bind_site Hargs).
 assert (HEnv : EnvRel_with (JitKRef.JitKRef.VRel cx_sealed cx_D 20) [] [id_key] cx_rho cx_rho).
 { intros x [<-|[]]. exists (VNum (NInt 0)), (VNum (NInt 0)). unfold cx_rho. rewrite lookup_cons_eq.
   split; [reflexivity|split; [reflexivity|]].
   exact (JitKRefCompatCtl.JitKRefCompatCtl.VRel_lit cx_sealed cx_D 20 [] (ENum (NInt 0)) (VNum (NInt 0)) eq_refl). }
 assert (Wf : wf_world []) by (split; constructor).
 specialize (H 20 [] cx_rho cx_rho Wf HEnv).
 assert (HS : JitKRef.JitKRef.SRel cx_sealed cx_D 20 [] cx_st cx_st).
 { assert (SH : JitKRef.JitKRef.StoreHas cx_D cx_st).
   { intros f d [E|[E|[]]]; injection E as <- <-; vm_compute; reflexivity. }
   split; [exact Wf|split; [exact SH|split; [exact SH|split; [reflexivity|split; [constructor|intros l0 l []]]]]]. }
 pose proof (proj1 (ERel_iff cx_sealed cx_D 20 [] cx_rho _ cx_rho cx_e) H 20 (le_n 20) [] (wext_refl [] Wf) [] []
   (JitKRefGround.JitKRefGround.KRel_top cx_sealed cx_D 20 [] Wf) cx_st cx_st HS) as O.
 assert (Ht : JitKRef.JitKRef.runs cx_sealed 10 (Cfg (Eval cx_rho cx_e) [] cx_st) [] (Cfg (Ret (VNum (NInt 0))) [] cx_st)).
 { apply iter_runs. vm_compute. reflexivity. }
 destruct (O 10 [] _ ltac:(lia) Ht) as [Hret _].
 destruct (Hret (VNum (NInt 0)) cx_st eq_refl) as (v0 & s0 & w' & Hs & _ & HG & _).
 set (c0 := Cfg (Eval cx_rho (ECall F.bind_name cx_args)) [] cx_st) in Hs.
 assert (HC : forall i c, (i <= 15)%nat -> iter_tau cx_sealed i c0 = Some c ->
   no_io (next_r (jit_rules cx_sealed) jit_profile c) = true /\ forallb JitKRefBase.JitKRefBase.nontrap (kont c) = true).
 { intros i c L Ei. assert (Ck : forallb (fun i => match iter_tau cx_sealed i c0 with
       | Some c => no_io (next_r (jit_rules cx_sealed) jit_profile c) && forallb JitKRefBase.JitKRefBase.nontrap (kont c)
       | None => true end) (seq 0 16) = true) by (vm_compute; reflexivity).
   rewrite forallb_forall in Ck. specialize (Ck i ltac:(apply in_seq; lia)). rewrite Ei in Ck.
   apply andb_true_iff in Ck. exact Ck. }
 assert (HN : iter_tau cx_sealed 16 c0 = None) by (vm_compute; reflexivity).
 destruct (star_reach cx_sealed c0 15 HC HN [] _ Hs) as [(i & L & Ei)|(x & K & s & E & _)].
 - assert (Ck : forallb (fun i => match iter_tau cx_sealed i c0 with
       | Some (Cfg (Ret v) [] _) => match v with VVec 0 => true | _ => false end
       | _ => true end) (seq 0 16) = true) by (vm_compute; reflexivity).
   rewrite forallb_forall in Ck. specialize (Ck i ltac:(apply in_seq; lia)). rewrite Ei in Ck.
   destruct v0; try discriminate Ck. cbn in HG. contradiction.
 - discriminate E.
Qed.

(* ======================= the Prolog shapes in stage 0's sources (a TEST harness, not proof) ======================= *)
(* Run by tests/shen-jit/stage0_to_rocq.py --prolog over the decoded .forms of every stage 0 file. For each
   shape, the number of definitions with at least one occurrence and the number of occurrences, in
   the parsed source bodies. The shapes over-approximate lower.shen's guards (any arguments, any
   scope), so a 0 is a 0 for the rewrite.
   - cut_frozen: (shen.cut _ _ _ (freeze _)), what cut-fail's pattern starts with;
   - cut_fail: (shen.cut _ _ _ (freeze (when _ ...))), cut-fail's source shape;
   - deref_eq: (= (shen.deref _ _) (shen.deref _ _)), deref='s source shape;
   - bound_now: (shen.bind! _ _ _ (freeze _)), bound-now's direct shape (bind_rule's);
   - bound_let: (let G (freeze _) ...) with (shen.bind! _ _ _ G) inside, the let-frozen shape;
   - unified_now: (is _ _ _ _ _ (freeze _)) or (is! ...), unified-now's shape. *)
Definition cut_name : name := kw "shen.cut".
Definition when_name : name := kw "when".
Definition deref_name : name := kw "shen.deref".
Definition is_cut_frozen (e : expr) : bool := match e with
 | ECall f [_; _; _; EFreeze _] => text_eqb f cut_name | _ => false end.
Definition is_cut_fail (e : expr) : bool := match e with
 | ECall f [_; _; _; EFreeze (ECall h _)] => text_eqb f cut_name && text_eqb h when_name | _ => false end.
Definition is_deref_eq (e : expr) : bool := match e with
 | ECall f [ECall d1 [_; _]; ECall d2 [_; _]] => text_eqb f (kw "=") && text_eqb d1 deref_name && text_eqb d2 deref_name
 | _ => false end.
Definition is_unified_now (e : expr) : bool := match e with
 | ECall f [_; _; _; _; _; EFreeze _] => text_eqb f (kw "is") || text_eqb f (kw "is!") | _ => false end.

Definition shape_count (P : expr -> bool) (bs : list expr) : nat * nat :=
 (List.length (filter (fun b => existsb P (F.subterms b)) bs),
  fold_left (fun n b => n + List.length (filter P (F.subterms b))) bs 0)%nat.

Definition src_bodies (fs : list sx) : list expr :=
 flat_map (fun f => match parse [] (to_value f) with Some (EDefun _ _ b) => [b] | _ => [] end) fs.

Definition prolog_scan (fs : list sx) : list (string * (nat * nat)) :=
 let bs := src_bodies fs in
 [("bodies", (List.length bs, List.length fs));
  ("cut_frozen", shape_count is_cut_frozen bs); ("cut_fail", shape_count is_cut_fail bs);
  ("deref_eq", shape_count is_deref_eq bs); ("bound_now", shape_count F.frozen_bind bs);
  ("bound_let", shape_count F.let_frozen_bind bs); ("unified_now", shape_count is_unified_now bs)]%string.

Example scan_cut_fail : is_cut_fail (ECall cut_name [EVar (kw "B"); EVar (kw "L"); EVar (kw "K");
  EFreeze (ECall when_name [EBool false; EVar (kw "B"); EVar (kw "L"); EVar (kw "K"); EVar (kw "C")])]) = true.
Proof. vm_compute. reflexivity. Qed.
Example scan_deref_eq : is_deref_eq (ECall (kw "=") [ECall deref_name [EVar (kw "X"); EVar (kw "B")];
  ECall deref_name [EVar (kw "Y"); EVar (kw "B")]]) = true.
Proof. vm_compute. reflexivity. Qed.

(* No rule of this file fires on the two v0.6 shapes: bind_rule refuses them whatever the recursive
   checker says (the norm checker has no cut-fail or deref= rule; see the header's residuals). *)
Example bind_rule_not_cut_fail : forall D rec g e, bind_rule D rec g (ECall cut_name [EVar (kw "B"); EVar (kw "L"); EVar (kw "K");
  EFreeze (ECall when_name [EBool false; EVar (kw "B"); EVar (kw "L"); EVar (kw "K"); EVar (kw "C")])]) e = false.
Proof.
 intros D rec g e. destruct e as [| | | | | | |a1 x e1| | | | | | | | | |]; try reflexivity;
  destruct e1 as [| | | | | | |a2 y e2| | | | | | | | | |]; try reflexivity; destruct e2; reflexivity.
Qed.
Example bind_rule_not_deref_eq : forall D rec g e, bind_rule D rec g (ECall (kw "=") [ECall deref_name [EVar (kw "X"); EVar (kw "B")];
  ECall deref_name [EVar (kw "Y"); EVar (kw "B")]]) e = false.
Proof.
 intros D rec g e. destruct e as [| | | | | | |a1 x e1| | | | | | | | | |]; try reflexivity;
  destruct e1 as [| | | | | | |a2 y e2| | | | | | | | | |]; try reflexivity; destruct e2; reflexivity.
Qed.
End JitFrontProlog.
