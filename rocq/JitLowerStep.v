(* Shen/JIT Phase 2: one step of the simulation. From a related pair, the source takes steps and the
   bytecode keeps up, or both finish with related results. See JitLowerRel.v for what the relation
   admits. Nothing here concerns machine code, the image, or how the code was produced. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitMeta JitProfile JitLowerRel JitLowerKont JitLowerStable JitLowerPrim.
Import ListNotations.
Module JitLowerStep.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitLowerKont.JitLowerKont JitLowerStable.JitLowerStable JitLowerPrim.JitLowerPrim.
Local Open Scope N_scope.

(* ---------- a measure: what the source can do while the bytecode stands still ---------- *)
Fixpoint esize (e : expr) : nat := match e with
 | ELet _ a b => 2 + esize a + esize b
 | EIf c a b => 3 + esize c + esize a + esize b
 | EAnd a b | EOr a b => 3 + esize a + esize b
 | ECond cl => 1 + (fix go (l : list (expr * expr)) : nat := match l with
     | [] => 0 | (c, b) :: l => 2 + esize c + esize b + go l end) cl
 | EType a => 1 + esize a
 | ECall _ args => 1 + (fix go (l : list expr) : nat := match l with
     | [] => 0 | a :: l => 1 + esize a + go l end) args
 | _ => 1 end%nat.
Definition fsize (f : frame) : nat := match f with
 | KLet _ b _ => 1 + esize b
 | KIf a b _ => 1 + esize a + esize b
 | KAnd b _ | KOr b _ => 2 + esize b
 | KAndR | KOrR => 1
 | KCond b rest _ => 1 + esize b + esize (ECond rest)
 | KCallArgs f _ es _ => esize (ECall f es)
 | _ => 1 end%nat.
Fixpoint ksize (k : list frame) : nat := match k with [] => 0 | f :: k => fsize f + ksize k end%nat.
Definition msr (c : config) : nat := match ctl c with
 | Eval _ e => 1 + esize e + ksize (kont c)
 | _ => 1 + ksize (kont c) end%nat.

Section Sim.
Variables (E : B.env) (pt : B.tree (B.prim * nat)) (sealed : list name).
Notation R := (jit_rules sealed).
Notation P := jit_profile.

Inductive Sstar : config -> config -> Prop :=
 | SS_refl c : Sstar c c
 | SS_step c c1 c2 : step_r R P c Tau c1 -> Sstar c1 c2 -> Sstar c c2.
Lemma Sstar_trans : forall a b c, Sstar a b -> Sstar b c -> Sstar a c.
Proof. intros a b c H; induction H; intros; [auto|econstructor; eauto]. Qed.
Lemma S1 : forall c c' c2, next_r R P c = MTau c' -> Sstar c' c2 -> Sstar c c2.
Proof. intros. econstructor; [apply step_r_tau; eauto|auto]. Qed.

Lemma S1' : forall c c', next_r R P c = MTau c' -> Sstar c c'.
Proof. intros. eapply S1; [eauto|constructor]. Qed.

Definition TS (m m' : B.machine) := B.next E pt m = B.MTau m'.
Inductive TStar : B.machine -> B.machine -> Prop :=
 | TS_refl m : TStar m m
 | TS_step m m1 m2 : TS m m1 -> TStar m1 m2 -> TStar m m2.
Definition TPlus (m m' : B.machine) := exists m1, TS m m1 /\ TStar m1 m'.
Lemma TStar_trans : forall a b c, TStar a b -> TStar b c -> TStar a c.
Proof. intros a b c H; induction H; intros; [auto|econstructor; eauto]. Qed.
Lemma TPlus_star : forall a b, TPlus a b -> TStar a b.
Proof. intros a b [m [H1 H2]]. econstructor; eauto. Qed.

(* The function table, for this store. *)
Record FunRel (s : store) (m : B.machine) : Prop := {
 fr_user : forall f ps b, lookup f (gfuns s) = Some (FUser ps b) -> exists l c caps,
   B.tget (B.sym_of_text f) (B.m_gfun m) = Some (B.VClo l) /\
   B.tget l (B.m_heap m) = Some (B.OClo c caps) /\
   B.code_arity c = N.of_nat (List.length ps) /\ B.code_entry c = None /\ CompFn c ps b;
 fr_none : forall f, lookup f (gfuns s) = None -> forall l, B.tget (B.sym_of_text f) (B.m_gfun m) <> Some (B.VClo l);
 fr_prim : forall f p, lookup f (gfuns s) = Some (FPrim p) -> prim_of_name f = Some p;
 fr_name : forall f p, prim_of_name f = Some p -> lookup f (gfuns s) = Some (FPrim p) }.
Definition Com (s : store) (m : B.machine) := B.m_handlers m = [] /\ FunRel s m.
Lemma FunRel_same : forall s m m', B.m_gfun m' = B.m_gfun m -> B.m_heap m' = B.m_heap m -> FunRel s m -> FunRel s m'.
Proof.
 intros s m m' G H [A1 A2 A3 A4]. constructor; auto.
 - intros f ps b L. destruct (A1 f ps b L) as (l & c & caps & X). rewrite G, H. eauto.
 - intros f L l. rewrite G. apply A2; auto.
Qed.

Notation fp m := (B.m_fp m).
Notation st m := (B.m_stack m).
Notation code m := (B.m_code m).
Notation cs m := (B.m_conts m).

Inductive MS (s : store) : config -> B.machine -> Prop :=
 | MS_eval g top e dst r2 rho k w m :
     Com s m -> Comp (code m) g top e dst (B.m_rest m) r2 -> MEnv (fp m) (st m) g rho -> EnvBelow g top ->
     Above (fp m) top w -> KC (code m) (fp m) (st m) (cs m) w dst r2 k ->
     MS s (Cfg (Eval rho e) k s) m
 | MS_test g top e l r2 rho k w m :
     Com s m -> CompT (code m) g top e l (B.m_rest m) r2 -> MEnv (fp m) (st m) g rho -> EnvBelow g top ->
     Above (fp m) top w -> TK (code m) (fp m) (st m) (cs m) w true l r2 k ->
     MS s (Cfg (Eval rho e) k s) m
 | MS_op g top e o top2 r2 rho k w m :
     Com s m -> CompOp (code m) g top e o top2 (B.m_rest m) r2 -> MEnv (fp m) (st m) g rho -> EnvBelow g top ->
     Above (fp m) top w -> KD (code m) (fp m) (st m) (cs m) w o r2 k ->
     MS s (Cfg (Eval rho e) k s) m
 | MS_ret v v' o k w m :
     Com s m -> read_o (code m) (fp m) (st m) o = Some v' -> VR v v' ->
     KD (code m) (fp m) (st m) (cs m) w o (B.m_rest m) k ->
     MS s (Cfg (Ret v) k s) m.

Inductive Out (s : store) (c : config) (m : B.machine) : Prop :=
 | O_step c' m' : Sstar c c' -> (TPlus m m' \/ (m' = m /\ (msr c' < msr c)%nat)) -> MS s c' m' -> Out s c m
 | O_ok v v' m1 m2 : Sstar c (Cfg (Ret v) [] s) -> TStar m m1 ->
     B.next E pt m1 = B.MFinal (B.FReturn v') m2 -> VR v v' -> Out s c m
 | O_err x l msg tv m1 m2 : Sstar c (Cfg (Throw x) [] s) -> TStar m m1 ->
     B.next E pt m1 = B.MFinal (B.FError (B.VExn l)) m2 -> B.tget l (B.m_heap m2) = Some (B.OExn msg tv) ->
     exn_ok x msg -> Out s c m.

Lemma Out_t : forall s c m m1, TS m m1 -> Out s c m1 -> Out s c m.
Proof.
 intros s c m m1 T O. inversion O; subst.
 - eapply O_step; eauto. left. destruct H0 as [[m2 [A B1]]|[-> _]].
   + exists m1. split; auto. econstructor; eauto.
   + exists m1. split; auto. constructor.
 - eapply O_ok; eauto. econstructor; eauto.
 - eapply O_err; eauto. econstructor; eauto.
Qed.
Lemma Out_s : forall s c c1 m, next_r R P c = MTau c1 -> (msr c1 < msr c)%nat -> Out s c1 m -> Out s c m.
Proof.
 intros s c c1 m N0 L O. inversion O; subst.
 - eapply O_step; [eapply S1; eauto|idtac|eauto]. destruct H0 as [A|[-> B0]]; [left; auto|right; split; [auto|lia]].
 - eapply O_ok; eauto. eapply S1; eauto.
 - eapply O_err; eauto. eapply S1; eauto.
Qed.

(* ---------- frames never catch here ---------- *)
Definition notrap (k : list frame) := Forall (fun f => match f with KTrap _ _ => False | _ => True end) k.
Lemma K_notrap :
 (forall c fp st cs w o r k, KD c fp st cs w o r k -> notrap k) /\
 (forall c fp st cs w gd l r k, TK c fp st cs w gd l r k -> notrap k) /\
 (forall c fp st cs w dst r k, KC c fp st cs w dst r k -> notrap k) /\
 (forall fp st cs k, RK fp st cs k -> notrap k).
Proof.
 apply K_mut; intros; try assumption; try (constructor; [exact I|assumption]); constructor.
Qed.
Lemma unwind : forall x k s, notrap k -> Sstar (Cfg (Throw x) k s) (Cfg (Throw x) [] s).
Proof.
 intros x k; induction k as [|f k IH]; intros s N0; [constructor|].
 inversion N0; subst. eapply S1; [|apply IH; auto]. destruct f; try contradiction; reflexivity.
Qed.

Lemma raise_final : forall m msg v, B.m_handlers m = [] ->
 B.raise m msg v = B.MFinal (B.FError (B.VExn (B.m_next m)))
   (snd (B.alloc m (B.OExn msg v))) /\
 B.tget (B.m_next m) (B.m_heap (snd (B.alloc m (B.OExn msg v)))) = Some (B.OExn msg v).
Proof.
 intros m msg v H. unfold B.raise. rewrite H. cbn. split; [reflexivity|].
 apply JitMeta.JitMeta.tget_tset_same.
Qed.

(* A raise in the bytecode, and the source at the same exception. *)
Lemma finish_raise : forall s c m m1 x k msg tv, B.m_handlers m1 = [] ->
 B.next E pt m = B.raise m1 msg tv -> Sstar c (Cfg (Throw x) k s) -> notrap k -> exn_ok x msg -> Out s c m.
Proof.
 intros s c m m1 x k msg tv H N0 S0 Nt X.
 destruct (raise_final m1 msg tv H) as [A B0].
 eapply O_err; [eapply Sstar_trans; [exact S0|apply unwind; auto]|constructor|rewrite N0; exact A|exact B0|exact X].
Qed.

(* ---------- bytecode steps ---------- *)
Definition wr (m : B.machine) (r : list B.instr) (d : N) (v : B.val) : B.machine :=
 B.set_stack (B.set_rest m r) (B.swrite (B.set_rest m r) d v).

Lemma Com_same : forall s m m', Com s m -> B.m_handlers m' = B.m_handlers m ->
 B.m_gfun m' = B.m_gfun m -> B.m_heap m' = B.m_heap m -> Com s m'.
Proof. intros s m m' [A B0] H G Hp. split; [congruence|eapply FunRel_same; eauto]. Qed.

Lemma ms_write : forall s m r2 d v v' w k, Com s m ->
 KC (code m) (fp m) (st m) (cs m) w (DSlot d) r2 k -> VR v v' ->
 MS s (Cfg (Ret v) k s) (wr m r2 d v').
Proof.
 intros s m r2 d v v' w k C K V. inversion K; subst.
 eapply MS_ret with (o := B.OSlot d) (w := w).
 - eapply Com_same; eauto.
 - cbn. apply slotv_same.
 - exact V.
 - eapply KD_stable; [eassumption|]. intros a N0. cbn. symmetry. apply slotv_other. intro; subst; contradiction.
Qed.

Lemma lit_step : forall sl rho e k s0 v, lit_val e = Some v ->
 next_r (jit_rules sl) jit_profile (Cfg (Eval rho e) k s0) = MTau (Cfg (Ret v) k s0).
Proof. intros sl rho e k s0 v H; destruct e; cbn in H; inversion H; subst; reflexivity. Qed.
Lemma esize_pos : forall e, (1 <= esize e)%nat.
Proof. destruct e; cbn; lia. Qed.

Lemma MEnv_cons : forall f s0 g rho x d v v', MEnv f s0 g rho -> slotv s0 (f + d) = Some v' -> VR v v' ->
 MEnv f s0 ((x, d) :: g) ((x, v) :: rho).
Proof.
 intros f s0 g rho x d v v' M A V y s L. cbn in L |- *. destruct (text_eqb y x).
 - inversion L; subst. eauto.
 - apply M; auto.
Qed.
Lemma EnvBelow_cons : forall g top x d, EnvBelow g top -> d < top -> EnvBelow ((x, d) :: g) top.
Proof. intros g top x d H L y s K. cbn in K. destruct (text_eqb y x); [inversion K; subst; auto|eapply H; eauto]. Qed.
Lemma EnvBelow_mono : forall g a b, EnvBelow g a -> a <= b -> EnvBelow g b.
Proof. intros g a b H L x s K. apply H in K. lia. Qed.
Lemma Prot_below : forall g f top, EnvBelow g top -> Prot g f (fun a => f + top <= a).
Proof. intros g f top H x s K C. apply H in K. lia. Qed.

Lemma CompOp_mono : forall c g top e o top2 r r', CompOp c g top e o top2 r r' -> top <= top2 /\ o_below top2 o.
Proof. intros; induction H; cbn; try lia; auto. Qed.

(* ---------- a call: the bytecode enters a function the source calls ---------- *)
Lemma firstn_len : forall {A} (l : list A) n, List.length l = n -> firstn n l = l.
Proof. intros. subst. apply firstn_all. Qed.
Lemma skipn_len : forall {A} (l : list A) n, List.length l = n -> skipn n l = [].
Proof. intros. subst. apply skipn_all. Qed.

Lemma Sub_above : forall f t, Sub (fun a => f + t <= a) (fun a => f <= a).
Proof. intros f t a A. lia. Qed.
Lemma MEnv_bind : forall ps args f s0 i, List.length ps = List.length args -> ArgsAt s0 (f + i) args ->
 MEnv f s0 (bind ps i) (combine ps args).
Proof.
 induction ps as [|p ps IH]; intros args f s0 i L A x s K; [discriminate|].
 destruct args as [|a args]; [discriminate|]. inversion A; subst. cbn in K |- *.
 destruct (text_eqb x p).
 - inversion K; subst. eauto.
 - eapply IH; [|replace (f + (i + 1)) with (f + i + 1) by lia; eassumption|exact K]. cbn in L; lia.
Qed.
Lemma bind_below : forall ps i, EnvBelow (bind ps i) (i + N.of_nat (List.length ps)).
Proof.
 induction ps as [|p ps IH]; intros i x s K; cbn in K; [discriminate|].
 destruct (text_eqb x p).
 - inversion K; subst. cbn [List.length]. lia.
 - apply IH in K. cbn [List.length]. lia.
Qed.

Lemma enter_shape : forall (m' : B.machine) l c caps n st0 fp0 ks,
 B.tget l (B.m_heap m') = Some (B.OClo c caps) -> B.code_entry c = None ->
 let m2 := B.set_ctl m' st0 fp0 c (B.code_ins c) ks in
 (N.eqb n (B.code_arity c) = true /\ B.e_stack E (fp0 + B.code_frame c) = true /\
    B.enter E m' (B.VClo l) n st0 fp0 ks = B.raise_s m2 "stack overflow") \/
 (N.eqb n (B.code_arity c) = true /\ B.e_stack E (fp0 + B.code_frame c) = false /\
    B.enter E m' (B.VClo l) n st0 fp0 ks = B.MTau (B.set_rest m2 (B.code_ins c))) \/
 (N.eqb n (B.code_arity c) = false /\ exists msg, B.enter E m' (B.VClo l) n st0 fp0 ks = B.raise m2 msg B.VCleared).
Proof.
 intros m' l c caps n st0 fp0 ks H En m2. unfold B.enter. rewrite H. fold m2.
 destruct (N.eqb n (B.code_arity c)) eqn:Q.
 - destruct (B.e_stack E (fp0 + B.code_frame c)) eqn:Es; [left|right; left]; repeat split; auto.
 - right; right. split; [reflexivity|]. rewrite En. eexists. reflexivity.
Qed.

Lemma enter_out : forall s c0 k0 m0 m' f args k1 ps b l c caps n st0 fp0 ks,
 Com s m' -> next_r (jit_rules sealed) jit_profile c0 = call_named_r (jit_rules sealed) jit_profile f args k1 s ->
 running_state c0 = true -> kont c0 = k0 -> mem c0 = s -> notrap k0 -> notrap k1 ->
 lookup f (gfuns s) = Some (FUser ps b) -> B.tget l (B.m_heap m') = Some (B.OClo c caps) ->
 B.code_arity c = N.of_nat (List.length ps) -> B.code_entry c = None -> CompFn c ps b ->
 n = N.of_nat (List.length args) -> B.next E pt m0 = B.enter E m' (B.VClo l) n st0 fp0 ks ->
 RK fp0 st0 ks k1 -> ArgsAt st0 (fp0 + 2) args -> Out s c0 m0.
Proof.
 intros s c0 k0 m0 m' f args k1 ps b l c caps n st0 fp0 ks C Nx Rn Kk Mm Nt0 Nt1 Lk H Ar En Cf Hn Nm Rk Aa.
 assert (Hc : B.m_handlers (B.set_ctl m' st0 fp0 c (B.code_ins c) ks) = []) by (destruct C; auto).
 destruct (enter_shape m' l c caps n st0 fp0 ks H En) as [[Q [Es Ev]]|[[Q [Es Ev]]|[Q [msg Ev]]]];
 rewrite Ar in Q; subst n.
 - (* stack overflow: the source may raise it at any running state *)
   rewrite Ev in Nm. eapply finish_raise with (x := XUser (of_string "stack overflow")) (k := k0); eauto; [|reflexivity].
   econstructor; [eapply step_r_resource with (r := RStack); [exact Rn|reflexivity]|]. rewrite Kk, Mm. constructor.
 - apply N.eqb_eq in Q. apply Nat2N.inj in Q.
   destruct Cf as [r' Cf].
   eapply O_step.
   + eapply S1; [rewrite Nx; unfold call_named_r; rewrite Lk; unfold arity_mismatch; cbn [arity_errors jit_rules andb];
       rewrite Q, Nat.eqb_refl; cbn [negb]; rewrite Nat.ltb_irrefl;
       rewrite (firstn_len args _ Q), (skipn_len args _ Q); reflexivity|constructor].
   + left. exists (B.set_rest (B.set_ctl m' st0 fp0 c (B.code_ins c) ks) (B.code_ins c)). split; [unfold TS; rewrite Nm; exact Ev|constructor].
   + eapply MS_eval with (w := fun a => fp0 + (2 + N.of_nat (List.length ps)) <= a).
     * eapply Com_same; eauto.
     * exact Cf.
     * eapply MEnv_bind; [symmetry; auto|exact Aa].
     * replace (2 + N.of_nat (List.length ps)) with (2 + N.of_nat (List.length ps)) by reflexivity. apply bind_below.
     * intros a A; exact A.
     * eapply KC_ret; [apply Sub_above|exact Rk].
 - apply N.eqb_neq in Q.
   rewrite Ev in Nm. eapply finish_raise with (x := XArity) (k := k1); eauto; [|exact I].
   eapply S1; [|constructor]. rewrite Nx. unfold call_named_r. rewrite Lk. unfold arity_mismatch.
   cbn [arity_errors jit_rules andb].
   assert (Nq : Nat.eqb (List.length args) (List.length ps) = false) by (apply Nat.eqb_neq; intro Z0; apply Q; rewrite Z0; reflexivity).
   rewrite Nq. reflexivity.
Qed.

Lemma undefined_out : forall s c0 k0 m0 m' f args k1 g0,
 Com s m' -> next_r (jit_rules sealed) jit_profile c0 = call_named_r (jit_rules sealed) jit_profile f args k1 s ->
 lookup f (gfuns s) = None -> notrap k1 -> kont c0 = k0 ->
 B.next E pt m0 = g0 (B.callee_named m' (B.sym_of_text f)) -> (forall mv, g0 (inr mv) = mv) -> Out s c0 m0.
Proof.
 intros s c0 k0 m0 m' f args k1 g0 C Nx L Nt Kk Nm G.
 assert (Cn : B.callee_named m' (B.sym_of_text f) = inr (B.raise_v m' "undefined function ~S" (B.VSym (B.sym_of_text f)))).
 { unfold B.callee_named. destruct C as [_ Fr].
   destruct (B.tget (B.sym_of_text f) (B.m_gfun m')) as [[]|] eqn:T; try reflexivity.
   exfalso. eapply (fr_none s m' Fr f L); eauto. }
 rewrite Cn, G in Nm.
 eapply finish_raise with (x := XUndefinedFun f) (k := k1); eauto; [destruct C; auto| |exact I].
 eapply S1; [|constructor]. rewrite Nx. unfold call_named_r. rewrite L. reflexivity.
Qed.

Lemma ArgsAt_snoc : forall s0 vs a v v', ArgsAt s0 a vs -> slotv s0 (a + N.of_nat (List.length vs)) = Some v' -> VR v v' ->
 ArgsAt s0 a (vs ++ [v]).
Proof.
 intros s0 vs a v v' A. induction A; intros S0 V; cbn.
 - econstructor; [rewrite <- S0; f_equal; cbn; lia|exact V|constructor].
 - econstructor; eauto. apply IHA; auto. rewrite <- S0. f_equal. cbn [List.length]. lia.
Qed.

Lemma named_call : forall s c0 k0 m f args k1 i d a n r1 w1,
 Com s m -> next_r (jit_rules sealed) jit_profile c0 = call_named_r (jit_rules sealed) jit_profile f args k1 s ->
 running_state c0 = true -> kont c0 = k0 -> mem c0 = s -> notrap k0 -> not_prim_name f ->
 B.m_rest m = i :: r1 -> call_instr i d a (B.sym_of_text f) n -> n = N.of_nat (List.length args) ->
 ArgsAt (st m) (fp m + a + 2) args -> Above (fp m) a w1 -> w1 (fp m + d) ->
 KD (code m) (fp m) (st m) (cs m) w1 (B.OSlot d) r1 k1 -> Out s c0 m.
Proof.
 intros s c0 k0 m f args k1 i d a n r1 w1 C Nx Rn Kk Mm Nt Np Hr Ci Hn Aa Ab Wd Kd.
 pose (m' := B.set_rest m r1).
 assert (Cm : Com s m') by (eapply Com_same; eauto).
 assert (Nm : B.next E pt m = B.do_call E m' d a n r1 (B.callee_named m' (B.sym_of_text f))).
 { destruct Ci; subst i; unfold B.next; rewrite Hr; reflexivity. }
 assert (Nk1 : notrap k1) by (eapply (proj1 K_notrap); eauto).
 destruct (lookup f (gfuns s)) as [[p|ps b]|] eqn:L.
 - exfalso. destruct C as [_ Fr]. apply (fr_prim s m Fr) in L. unfold not_prim_name in Np. congruence.
 - destruct C as [Ch Fr]. destruct (fr_user s m Fr f ps b L) as (l & c & caps & Tg & Th & Ar & En & Cf).
   assert (Cn : B.callee_named m' (B.sym_of_text f) = inl (B.VClo l)) by (unfold B.callee_named; cbn; rewrite Tg; reflexivity).
   rewrite Cn in Nm.
   assert (Nm2 : B.next E pt m = B.enter E m' (B.VClo l) n (B.tset (B.skey (fp m + a + 1)) (B.VClo l) (st m)) (fp m + a)
     (B.Cont (code m) r1 d a :: cs m)) by exact Nm.
   eapply enter_out with (m' := m') (fp0 := fp m + a) (st0 := B.tset (B.skey (fp m + a + 1)) (B.VClo l) (st m)) (ks := B.Cont (code m) r1 d a :: cs m);
     [exact Cm|exact Nx|exact Rn|exact Kk|exact Mm|exact Nt|exact Nk1|exact L|exact Th|exact Ar|exact En|exact Cf|exact Hn|exact Nm2| |].
   + eapply RK_call with (w := w1).
     * lia.
     * replace (fp m + a - a) with (fp m) by lia. exact Ab.
     * replace (fp m + a - a) with (fp m) by lia.
       eapply KD_stable; [eassumption|]. intros x N0. symmetry. apply slotv_other. intro; subst. apply N0, Ab. lia.
     * replace (fp m + a - a) with (fp m) by lia. exact Wd.
   + eapply ArgsAt_stable; [replace (fp m + a + 2) with (fp m + a + 2) by reflexivity; exact Aa|].
     intros x X1 X2. symmetry. apply slotv_other. lia.
 - eapply undefined_out with (g0 := fun cv => B.do_call E m' d a n r1 cv); eauto.
Qed.

(* ---------- the moves before a tail call ---------- *)
Lemma loc_notin : forall ms i, ~ In i (map fst ms) -> loc ms i = i.
Proof.
 induction ms as [|[u v] ms IH]; intros i H; [reflexivity|]. cbn in H |- *.
 destruct (N.eqb u i) eqn:E0; [apply N.eqb_eq in E0; subst; exfalso; apply H; auto|].
 apply IH; tauto.
Qed.
Lemma loc_in : forall ms u v, NoDup (map fst ms) -> In (u, v) ms -> loc ms u = v.
Proof.
 induction ms as [|[x y] ms IH]; intros u v D I; [contradiction|]. cbn in D. inversion D; subst.
 cbn [loc]. destruct I as [I|I].
 - inversion I; subst. rewrite N.eqb_refl. reflexivity.
 - destruct (N.eqb x u) eqn:E0; [apply N.eqb_eq in E0; subst; exfalso; apply H1; apply (in_map fst _ (u, v) I)|].
   apply IH; auto.
Qed.
Lemma ParamAt_read : forall f s0 ms i vs j, ParamAt f s0 ms i vs -> i <= j -> j < i + N.of_nat (List.length vs) ->
 exists v', slotv s0 (f + loc ms j) = Some v'.
Proof.
 intros f s0 ms i vs j P. induction P; intros J1 J2; cbn [List.length] in J2.
 - lia.
 - destruct (N.eq_dec j i) as [->|Ne]; [eauto|]. apply IHP; lia.
Qed.

Lemma run_moves : forall ms r m lim,
 B.m_rest m = map (fun x => B.IMove (fst x) (snd x)) ms ++ r ->
 Forall (fun x => fst x < lim <= snd x) ms -> NoDup (map fst ms) ->
 (forall x, In x ms -> exists v, slotv (st m) (fp m + snd x) = Some v) ->
 exists m2, TStar m m2 /\ B.m_rest m2 = r /\ fp m2 = fp m /\ code m2 = code m /\ cs m2 = cs m /\
   B.m_handlers m2 = B.m_handlers m /\ B.m_gfun m2 = B.m_gfun m /\ B.m_heap m2 = B.m_heap m /\
   (forall j, j < lim -> slotv (st m2) (fp m + j) = slotv (st m) (fp m + loc ms j)) /\
   (forall a, a < fp m -> slotv (st m2) a = slotv (st m) a).
Proof.
 induction ms as [|[u v] ms IH]; intros r m lim Hr F D Rd.
 - exists m. cbn in Hr. repeat split; try constructor; auto.
 - cbn in Hr. inversion F; subst. cbn in H1. cbn in D. inversion D; subst.
   destruct (Rd (u, v) (or_introl eq_refl)) as [x Rx]. cbn in Rx.
   pose (m1 := wr m (map (fun x => B.IMove (fst x) (snd x)) ms ++ r) u x).
   assert (T1 : TS m m1).
   { unfold TS, B.next. rewrite Hr. change (B.sread (B.set_rest m (map (fun x => B.IMove (fst x) (snd x)) ms ++ r)) v) with (slotv (st m) (fp m + v)).
     rewrite Rx. reflexivity. }
   assert (Sm : forall a, a <> fp m + u -> slotv (st m1) a = slotv (st m) a) by (intros a N0; apply slotv_other; auto).
   assert (Su : slotv (st m1) (fp m + u) = Some x) by apply slotv_same.
   destruct (IH r m1 lim) as (m2 & T2 & Hr2 & Hf & Hc & Hk & Hh & Hg & Hp & Hj & Ha).
   + reflexivity.
   + assumption.
   + assumption.
   + intros y Iy. destruct (Rd y (or_intror Iy)) as [w Rw]. exists w.
     change (fp m1) with (fp m). rewrite Sm; [exact Rw|].
     rewrite Forall_forall in H2. specialize (H2 y Iy). lia.
   + exists m2. split; [econstructor; eauto|]. repeat split; try assumption.
     * intros j Lj. change (fp m1) with (fp m) in Hj. rewrite Hj by exact Lj. cbn [loc].
       destruct (N.eqb u j) eqn:E0.
       -- apply N.eqb_eq in E0; subst. rewrite loc_notin by exact H3. rewrite Su. symmetry. exact Rx.
       -- apply N.eqb_neq in E0. apply Sm.
          assert (Hl : loc ms j = j \/ lim <= loc ms j).
          { assert (G : forall l0, Forall (fun x => fst x < lim <= snd x) l0 -> loc l0 j = j \/ lim <= loc l0 j).
            { induction l0 as [|[p q] l0 IL]; intros Fq; [auto|]. inversion Fq; subst. cbn [loc]. destruct (N.eqb p j); [right; cbn in *; lia|apply IL; auto]. }
            apply G; auto. }
          destruct Hl as [->|Hl]; lia.
     * intros a La. change (fp m1) with (fp m) in Ha. rewrite Ha by exact La. apply Sm. lia.
Qed.

Lemma PA_to_AA : forall f s0 s2 ms i vs, ParamAt f s0 ms i vs ->
 (forall j, i <= j -> j < i + N.of_nat (List.length vs) -> slotv s2 (f + j) = slotv s0 (f + loc ms j)) ->
 ArgsAt s2 (f + i) vs.
Proof.
 intros f s0 s2 ms i vs P. induction P; intros Hh; [constructor|]. econstructor.
 - rewrite Hh; [eassumption|lia|cbn [List.length]; lia].
 - eassumption.
 - replace (f + i + 1) with (f + (i + 1)) by lia. apply IHP. intros j J1 J2. apply Hh; cbn [List.length]; lia.
Qed.

Lemma ParamAt_snoc : forall f s0 ms vs i v v', ParamAt f s0 ms i vs ->
 slotv s0 (f + loc ms (i + N.of_nat (List.length vs))) = Some v' -> VR v v' -> ParamAt f s0 ms i (vs ++ [v]).
Proof.
 intros f s0 ms vs i v v' P. induction P; intros S0 V; cbn.
 - econstructor; [|exact V|constructor]. replace (i + N.of_nat (List.length (@nil value))) with i in S0 by (cbn; lia). exact S0.
 - econstructor; eauto. apply IHP; auto.
   replace (i + 1 + N.of_nat (List.length vs)) with (i + N.of_nat (List.length (v0 :: vs))) by (cbn [List.length]; lia). exact S0.
Qed.
Lemma ParamAt_ms : forall f s0 ms ms2 i vs, ParamAt f s0 ms i vs ->
 (forall j, i <= j -> j < i + N.of_nat (List.length vs) -> loc ms2 j = loc ms j) -> ParamAt f s0 ms2 i vs.
Proof.
 intros f s0 ms ms2 i vs P. induction P; intros Hh; [constructor|]. econstructor; eauto.
 - rewrite Hh; [eassumption|lia|cbn [List.length]; lia].
 - apply IHP. intros j J1 J2. apply Hh; cbn [List.length]; lia.
Qed.

Lemma tail_fire : forall s c0 k0 m f args k1 ms i n r1 lim,
 Com s m -> next_r (jit_rules sealed) jit_profile c0 = call_named_r (jit_rules sealed) jit_profile f args k1 s ->
 running_state c0 = true -> kont c0 = k0 -> mem c0 = s -> notrap k0 -> not_prim_name f ->
 B.m_rest m = map (fun x => B.IMove (fst x) (snd x)) ms ++ i :: r1 ->
 tail_instr i 0 (B.sym_of_text f) n -> n = N.of_nat (List.length args) -> lim = n + 2 ->
 Forall (fun x => 2 <= fst x < lim /\ lim <= snd x) ms -> NoDup (map fst ms) ->
 ParamAt (fp m) (st m) ms 2 args -> RK (fp m) (st m) (cs m) k1 -> Out s c0 m.
Proof.
 intros s c0 k0 m f args k1 ms i n r1 lim C Nx Rn Kk Mm Nt Np Hr Ti Hn Hl F D Pa Rk.
 assert (F1 : Forall (fun x => fst x < lim <= snd x) ms) by (eapply Forall_impl; [|exact F]; intros [u v]; cbn; lia).
 destruct (run_moves ms (i :: r1) m lim Hr F1 D) as (m2 & T & Hr2 & Hf & Hc & Hk & Hh & Hg & Hp & Hj & Ha).
 { intros [u v] I. rewrite Forall_forall in F. specialize (F _ I). cbn in F.
   destruct (ParamAt_read _ _ _ _ _ u Pa) as [w Rw]; [lia|subst; lia|].
   rewrite (loc_in ms u v D I) in Rw. eauto. }
 pose (m' := B.set_rest m2 r1).
 assert (Cm : Com s m').
 { destruct C as [C1 C2]. split; [cbn; congruence|]. eapply FunRel_same; [| |exact C2]; cbn; congruence. }
 assert (Nm : B.next E pt m2 = B.do_tail E m' 0 n (B.callee_named m' (B.sym_of_text f))).
 { destruct Ti; subst i; unfold B.next; rewrite Hr2; reflexivity. }
 assert (Nk1 : notrap k1) by (eapply (proj2 (proj2 (proj2 K_notrap))); eauto).
 cut (Out s c0 m2).
 { clear -T. intros O. induction T; [auto|]. eapply Out_t; eauto. }
 destruct (lookup f (gfuns s)) as [[p|ps b]|] eqn:L.
 - exfalso. destruct C as [_ Fr]. apply (fr_prim s m Fr) in L. unfold not_prim_name in Np. congruence.
 - destruct Cm as [Ch Fr]. destruct (fr_user s m' Fr f ps b L) as (l & c & caps & Tg & Th & Ar & En & Cf).
   assert (Cn : B.callee_named m' (B.sym_of_text f) = inl (B.VClo l)) by (unfold B.callee_named; rewrite Tg; reflexivity).
   rewrite Cn in Nm.
   assert (Nm2 : B.next E pt m2 = B.enter E m' (B.VClo l) n (B.tset (B.skey (fp m2 + 1)) (B.VClo l) (st m2)) (fp m2) (cs m2)) by exact Nm.
   eapply enter_out with (m' := m') (fp0 := fp m2) (st0 := B.tset (B.skey (fp m2 + 1)) (B.VClo l) (st m2)) (ks := cs m2);
     [split; [exact Ch|exact Fr]|exact Nx|exact Rn|exact Kk|exact Mm|exact Nt|exact Nk1|exact L|exact Th|exact Ar|exact En|exact Cf|exact Hn|exact Nm2| |].
   + rewrite Hk, Hf. eapply RK_stable; [exact Rk|]. intros a La. rewrite slotv_other by lia. symmetry. apply Ha. exact La.
   + rewrite Hf. eapply PA_to_AA; [exact Pa|]. intros j J1 J2. rewrite slotv_other by lia.
     apply Hj. subst. lia.
 - eapply undefined_out with (m' := m') (g0 := fun cv => B.do_tail E m' 0 n cv); [exact Cm|exact Nx|exact L|exact Nk1|exact Kk|exact Nm|reflexivity].
Qed.

(* ---------- starting an argument of a tail call ---------- *)
Lemma kill_lookup : forall g s0 x, lookup x (kill s0 g) = if slot_is (lookup x g) s0 then None else lookup x g.
Proof.
 intros g s0 x. unfold kill.
 assert (G : forall l : env, lookup x (filter (fun p : name * N => negb (slot_is (lookup (fst p) g) s0)) l) =
     if slot_is (lookup x g) s0 then None else lookup x l).
 { induction l as [|[y u] l IH]; cbn [filter fst lookup].
   - destruct (slot_is (lookup x g) s0); reflexivity.
   - destruct (text_eqb x y) eqn:Ex.
     + apply text_eqb_eq in Ex; subst.
       destruct (slot_is (lookup y g) s0) eqn:Sl; cbn [negb].
       * exact IH.
       * cbn [lookup]. rewrite text_eqb_refl. reflexivity.
     + destruct (slot_is (lookup y g) s0) eqn:Sl; cbn [negb]; [exact IH|].
       cbn [lookup]. rewrite Ex. exact IH. }
 apply G.
Qed.
Lemma kill_sub : forall g s0 x u, lookup x (kill s0 g) = Some u -> lookup x g = Some u /\ u <> s0.
Proof.
 intros g s0 x u H. rewrite kill_lookup in H. destruct (lookup x g) as [v|]; cbn in H; [|discriminate].
 destruct (N.eqb v s0) eqn:E0; [discriminate|]. inversion H; subst. split; [reflexivity|]. apply N.eqb_neq; auto.
Qed.
Lemma MEnv_kill : forall f s1 g rho s0, MEnv f s1 g rho -> MEnv f s1 (kill s0 g) rho.
Proof. intros f s1 g rho s0 M x u L. apply kill_sub in L as [L _]. eauto. Qed.
Lemma EnvBelow_kill : forall g t s0, EnvBelow g t -> EnvBelow (kill s0 g) t.
Proof. intros g t s0 H x u L. apply kill_sub in L as [L _]. eauto. Qed.

Definition w_top (f t : N) : N -> Prop := fun a => f + t <= a.

Lemma ta_start : forall s m rho a es ms r0 r1 i s0 t f vals k1 g n,
 Com s m -> B.m_rest m = r0 -> CompTA (code m) g s0 t (a :: es) ms r0 (i :: r1) -> MEnv (fp m) (st m) g rho -> EnvBelow g t ->
 not_prim_name f -> s0 = 2 + N.of_nat (List.length vals) ->
 n = N.of_nat (List.length vals + 1 + List.length es) -> n + 2 <= t -> tail_instr i 0 (B.sym_of_text f) n ->
 Forall (fun x => 2 <= fst x < s0 /\ n + 2 <= snd x < t) ms -> NoDup (map fst ms) ->
 ParamAt (fp m) (st m) ms 2 (rev vals) -> RK (fp m) (st m) (cs m) k1 ->
 MS s (Cfg (Eval rho a) (KCallArgs f vals es rho :: k1) s) m.
Proof.
 intros s m rho a es ms r0 r1 i s0 t f vals k1 g n C Hr Ct Me Eb Np Hs Hn Ht Ti F D Pa Rk.
 assert (Nin : ~ In s0 (map fst ms)).
 { intro I. apply in_map_iff in I as ([u v] & E0 & I). rewrite Forall_forall in F. apply F in I. cbn in *. lia. }
 assert (Ls : loc ms s0 = s0) by (apply loc_notin; auto).
 assert (Nn : n = N.of_nat (List.length vals + 1 + List.length es)) by exact Hn.
 assert (Lj : forall j, 2 <= j < s0 -> loc ms j = j \/ n + 2 <= loc ms j < t).
 { clear -F. revert F. generalize ms. induction ms0 as [|[u v] l IL]; intros Fq j Jj; [auto|]. inversion Fq; subst. cbn [loc].
   destruct (N.eqb u j); [right; cbn in *; lia|eapply IL; eauto]. }
 assert (Sl : s0 < n + 2) by (rewrite Hs, Nn; lia).
 assert (F2 : Forall (fun x => 2 <= fst x < s0 + 1 /\ n + 2 <= snd x < t) ms)
   by (eapply Forall_impl; [|exact F]; intros [u v]; cbn; lia).
 subst r0. assert (Keep : s0 = 2 + N.of_nat (List.length vals) /\ n = N.of_nat (List.length vals + 1 + List.length es)) by auto.
 clear Hs Hn Nn. inversion Ct; subst; destruct Keep as [Hs Nn].
 - (* the variable is already in its slot *)
   eapply MS_op with (w := w_top (fp m) t) (top := t) (g := g) (top2 := t).
   + exact C.
   + eapply O_var; eauto.
   + exact Me.
   + exact Eb.
   + intros q0 X; exact X.
   + eapply KD_tail with (g := g) (t0 := t) (t := t) (ms := ms) (s := s0) (i := i) (n := n) (r1 := r1).
     * exact Np.
     * exact Hs.
     * exact Nn.
     * exact Ht.
     * lia.
     * exact Me.
     * apply Prot_below; auto.
     * exact Eb.
     * eassumption.
     * exact Ti.
     * rewrite Ls. reflexivity.
     * rewrite Ls. lia.
     * exact F2.
     * exact D.
     * exact Lj.
     * exact Pa.
     * intros q0 X. right; exact X.
     * exact Rk.
 - (* computed into a temporary *)
   assert (Ne : forall j, 2 <= j < s0 -> s0 <> j) by (intros; lia).
   eapply MS_eval with (w := w_top (fp m) t) (top := t + 1) (g := g) (dst := DSlot t).
   + exact C.
   + eassumption.
   + exact Me.
   + eapply EnvBelow_mono; [exact Eb|lia].
   + intros q0 X. unfold w_top. lia.
   + apply KC_slot; [unfold w_top; lia|].
     eapply KD_tail with (g := g) (t0 := t) (t := t + 1) (ms := (s0, t) :: ms) (s := s0) (i := i) (n := n) (r1 := r1).
     * exact Np.
     * exact Hs.
     * exact Nn.
     * lia.
     * lia.
     * exact Me.
     * apply Prot_below; auto.
     * eapply EnvBelow_mono; [exact Eb|lia].
     * eassumption.
     * exact Ti.
     * cbn [loc]. rewrite N.eqb_refl. reflexivity.
     * cbn [loc]. rewrite N.eqb_refl. lia.
     * constructor; [cbn; lia|]. eapply Forall_impl; [|exact F]; intros [u v]; cbn; lia.
     * cbn [map fst]. constructor; auto.
     * intros j Jj. cbn [loc]. destruct (N.eqb s0 j) eqn:E0; [apply N.eqb_eq in E0; lia|]. apply Lj; auto.
     * eapply ParamAt_ms; [exact Pa|]. intros j J1 J2. cbn [loc]. rewrite rev_length in J2.
       destruct (N.eqb s0 j) eqn:E0; [apply N.eqb_eq in E0; lia|reflexivity].
     * intros q0 X. right. exact X.
     * exact Rk.
 - (* computed in place: the slot's variables are dead afterwards *)
   pose (w1 := fun x => x = fp m + s0 \/ fp m + t <= x).
   eapply MS_eval with (w := w1) (top := t) (g := g) (dst := DSlot s0).
   + exact C.
   + eassumption.
   + exact Me.
   + exact Eb.
   + intros q0 X. right; exact X.
   + apply KC_slot; [left; reflexivity|].
     eapply KD_tail with (g := kill s0 g) (t0 := t) (t := t) (ms := ms) (s := s0) (i := i) (n := n) (r1 := r1).
     * exact Np.
     * exact Hs.
     * exact Nn.
     * exact Ht.
     * lia.
     * apply MEnv_kill; auto.
     * intros q0 u L X. destruct (kill_sub _ _ _ _ L) as [L1 L2]. apply Eb in L1. destruct X; lia.
     * apply EnvBelow_kill; auto.
     * eassumption.
     * exact Ti.
     * rewrite Ls. reflexivity.
     * rewrite Ls. lia.
     * exact F2.
     * exact D.
     * exact Lj.
     * exact Pa.
     * intros q0 X. exact X.
     * exact Rk.
Qed.

(* ---------- instruction by instruction ---------- *)
Lemma read_eq : forall m o, B.read_op m o = read_o (code m) (fp m) (st m) o.
Proof. intros m o; destruct o; reflexivity. Qed.
Lemma n_const : forall m d k r v, B.m_rest m = B.IConst d k :: r -> konst (code m) k = Some v -> TS m (wr m r d v).
Proof.
 intros m d k r v H K. assert (K2 : nth_error (B.code_consts (code (B.set_rest m r))) (N.to_nat k) = Some v) by exact K.
 unfold TS, B.next. rewrite H. cbv beta iota zeta. rewrite K2. reflexivity.
Qed.
Lemma n_move : forall m d s0 r v, B.m_rest m = B.IMove d s0 :: r -> slotv (st m) (fp m + s0) = Some v -> TS m (wr m r d v).
Proof.
 intros m d s0 r v H K. assert (K2 : B.sread (B.set_rest m r) s0 = Some v) by exact K.
 unfold TS, B.next. rewrite H. cbv beta iota zeta. rewrite K2. reflexivity.
Qed.
Lemma n_jump : forall m e r r1, B.m_rest m = B.IJump e :: r -> lbl (code m) e = Some r1 -> TS m (B.set_rest m r1).
Proof.
 intros m e r r1 H K. assert (K2 : B.find_label e (B.code_ins (code (B.set_rest m r))) = Some r1) by exact K.
 unfold TS, B.next. rewrite H. cbv beta iota zeta. rewrite K2. reflexivity.
Qed.
Lemma n_label : forall m l r, B.m_rest m = B.ILabel l :: r -> TS m (B.set_rest m r).
Proof. intros m l r H. unfold TS, B.next. rewrite H. reflexivity. Qed.
Lemma n_prim : forall m d q ops r args, B.m_rest m = B.IPrim d q ops :: r ->
 B.all_some (map (B.read_op (B.set_rest m r)) ops) = Some args ->
 B.next E pt m = if (B.allocates q && B.e_oom E (B.m_allocs m))%bool then B.raise_s (B.set_rest m r) "out of memory"
   else B.prim_step E pt (B.set_rest m r) d q args.
Proof. intros m d q ops r args H K. unfold B.next. rewrite H. cbv beta iota zeta. rewrite K. reflexivity. Qed.
Lemma n_ret : forall m o r v, B.m_rest m = B.IReturn o :: r -> read_o (code m) (fp m) (st m) o = Some v ->
 B.next E pt m = B.do_return (B.set_rest m r) v.
Proof.
 intros m o r v H K. assert (K2 : B.read_op (B.set_rest m r) o = Some v) by (rewrite read_eq; exact K).
 unfold B.next. rewrite H. cbv beta iota zeta. rewrite K2. reflexivity.
Qed.
Lemma n_jif : forall m o l r v, B.m_rest m = B.IJumpIfFalse o l :: r -> read_o (code m) (fp m) (st m) o = Some v ->
 B.next E pt m = match v with
   | B.VBool true => B.MTau (B.set_rest m r)
   | B.VBool false => match B.find_label l (B.code_ins (code m)) with
     | Some r' => B.MTau (B.set_rest (B.set_rest m r) r') | None => B.MStuck B.RBadLabel end
   | _ => B.raise_v (B.set_rest m r) "~S is not a boolean" v end.
Proof.
 intros m o l r v H K. assert (K2 : B.read_op (B.set_rest m r) o = Some v) by (rewrite read_eq; exact K).
 unfold B.next. rewrite H. cbv beta iota zeta. rewrite K2. destruct v; reflexivity.
Qed.

Lemma Com_rest : forall s m r, Com s m -> Com s (B.set_rest m r).
Proof. intros. eapply Com_same; eauto. Qed.
Lemma notrap_kc : forall c f s0 ks w d r k, KC c f s0 ks w d r k -> notrap k.
Proof. intros; eapply (proj1 (proj2 (proj2 K_notrap))); eauto. Qed.
Lemma notrap_kd : forall c f s0 ks w o r k, KD c f s0 ks w o r k -> notrap k.
Proof. intros; eapply (proj1 K_notrap); eauto. Qed.
Lemma notrap_tk : forall c f s0 ks w gd l r k, TK c f s0 ks w gd l r k -> notrap k.
Proof. intros; eapply (proj1 (proj2 K_notrap)); eauto. Qed.

Ltac msr_dec := unfold msr; cbn -[esize]; cbn [esize]; lia.

(* ---------- tests ---------- *)
Lemma tk_label : forall c f s0 ks w gd l r k, TK c f s0 ks w gd l r k -> exists re, lbl c l = Some re.
Proof. intros; induction H; eauto. Qed.

Lemma tk_true : forall c f s0 ks w gd l r k, TK c f s0 ks w gd l r k -> forall s m,
 Com s m -> code m = c -> fp m = f -> st m = s0 -> cs m = ks -> B.m_rest m = r -> Out s (Cfg (Ret (VBool true)) k s) m.
Proof.
 intros c f s0 ks w gd l r k H. induction H; intros s m Cm Hc Hf Hs Hk Hr; subst.
 - eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_eval; eassumption.
 - eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_eval; eassumption.
 - eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_test; try eassumption. eapply TK_andr; [intros a A; exact A|eassumption].
 - eapply Out_s; [reflexivity|msr_dec|]. eapply IHTK; eauto.
 - eapply Out_s; [reflexivity|msr_dec|]. eapply IHTK2; eauto.
 - eapply Out_s; [reflexivity|msr_dec|]. eapply IHTK; eauto.
 - eapply Out_t; [eapply n_jump; eauto|]. eapply IHTK; [apply Com_rest; auto|reflexivity..].
 - eapply Out_t; [eapply n_label; eauto|]. eapply IHTK; [apply Com_rest; auto|reflexivity..].
 - eapply O_step; [apply SS_refl|left; exists (wr m r2 d (B.VBool true)); split; [eapply n_const; eauto|constructor]|].
   eapply ms_write; [eauto|eapply KC_slot; eassumption|constructor].
Qed.

Lemma tk_false : forall c f s0 ks w gd l r k, TK c f s0 ks w gd l r k -> forall s m re,
 Com s m -> code m = c -> fp m = f -> st m = s0 -> cs m = ks -> lbl c l = Some re -> B.m_rest m = re ->
 Out s (Cfg (Ret (VBool false)) k s) m.
Proof.
 intros c f s0 ks w gd l r k H. induction H; intros s m re Cm Hc Hf Hs Hk Hl Hr; subst.
 - assert (Hr : B.m_rest m = r3) by congruence.
   eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_eval; try eassumption. rewrite Hr; eassumption.
 - assert (Hr : B.m_rest m = r3) by congruence.
   eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_eval; try eassumption. rewrite Hr; eassumption.
 - eapply Out_s; [reflexivity|msr_dec|]. eapply IHTK; eauto.
 - eapply Out_s; [reflexivity|msr_dec|]. eapply IHTK; eauto.
 - assert (Hr : B.m_rest m = r2) by congruence.
   eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_test; try eassumption.
   + rewrite Hr; eassumption.
   + eapply TK_orr; [intros a A; exact A|eassumption].
 - eapply Out_s; [reflexivity|msr_dec|]. eapply IHTK; eauto.
 - eapply IHTK; eauto.
 - eapply IHTK; eauto.
 - assert (Hr : B.m_rest m = B.IConst d kf :: r4) by congruence.
   eapply O_step; [apply SS_refl|left; exists (wr m r4 d (B.VBool false)); split; [eapply n_const; eauto|constructor]|].
   eapply ms_write; [eauto|eapply KC_slot; eassumption|constructor].
Qed.

Lemma tk_nb : forall c f s0 ks w gd l r k, TK c f s0 ks w gd l r k -> gd = true -> forall s v, (forall b, v <> VBool b) ->
 exists k', Sstar (Cfg (Ret v) k s) (Cfg (Throw XNotBoolean) k' s) /\ notrap k'.
Proof.
 intros c f s0 ks w gd l r k H. induction H; intros G s v Nb; try discriminate; try (apply IHTK; auto; fail);
 (exists k1; split;
   [eapply S1'; destruct v; try (exfalso; eapply Nb; reflexivity); reflexivity
   |first [eapply notrap_kc; eassumption | eapply notrap_tk; eassumption]]).
Qed.

(* ---------- primitives ---------- *)
Lemma all_some_app : forall {X Y} (g : X -> option Y) a b xa xb,
 B.all_some (map g a) = Some xa -> B.all_some (map g b) = Some xb -> B.all_some (map g (a ++ b)) = Some (xa ++ xb).
Proof.
 intros X Y g a. induction a as [|x a IH]; intros b xa xb A B0.
 - cbn in A. inversion A; subst. exact B0.
 - cbn in A |- *. destruct (g x) as [y|]; [|discriminate].
   destruct (B.all_some (map g a)) as [ys|] eqn:Y0; cbn in A; [|discriminate]. inversion A; subst.
   rewrite (IH b ys xb eq_refl B0). reflexivity.
Qed.
Lemma done_all : forall c f s0 vals dops, DoneR c f s0 vals dops -> forall m, code m = c -> fp m = f -> st m = s0 ->
 exists xs, B.all_some (map (B.read_op m) (rev dops)) = Some xs /\ Forall2 VR (rev vals) xs.
Proof.
 intros c f s0 vals dops D. induction D; intros m Hc Hf Hs.
 - exists []. split; [reflexivity|constructor].
 - destruct (IHD m Hc Hf Hs) as [xs [A B0]]. exists (xs ++ [v']). split.
   + cbn [rev]. eapply all_some_app; [exact A|]. cbn. rewrite read_eq. subst. rewrite H. reflexivity.
   + cbn [rev]. apply Forall2_app; auto.
Qed.

Lemma prim_call : forall s f p args k o, lookup f (gfuns s) = Some (FPrim p) -> List.length args = prim_arity p ->
 prim_rule_r (jit_rules sealed) jit_profile p args s = PDone o ->
 call_named_r (jit_rules sealed) jit_profile f args k s = MTau (pout_config jit_profile o [] k s).
Proof.
 intros s f p args k o L A H. unfold call_named_r. rewrite L. unfold arity_mismatch.
 cbn [arity_errors jit_rules andb]. rewrite A, Nat.eqb_refl. cbn [negb]. rewrite Nat.ltb_irrefl.
 rewrite (firstn_len args _ A), (skipn_len args _ A). unfold prim_move_r. rewrite H. reflexivity.
Qed.

Lemma below_safe : forall f top l, Forall (o_below top) l -> Forall (o_safe f (w_top f top)) l.
Proof.
 intros f top l H. eapply Forall_impl; [|exact H]. intros [s0|k]; cbn; [unfold w_top; lia|auto].
Qed.
Lemma below_mono : forall a b l, a <= b -> Forall (o_below a) l -> Forall (o_below b) l.
Proof. intros a b l L H. eapply Forall_impl; [|exact H]. intros [s0|k]; cbn; [lia|auto]. Qed.
Lemma o_below_mono : forall a b o, a <= b -> o_below a o -> o_below b o.
Proof. intros a b [s0|k] L H; cbn in *; [lia|auto]. Qed.

(* ---------- an argument arrives ---------- *)
Lemma Ops_nil : forall c g top ops r r', CompOps c g top [] ops r r' -> ops = [] /\ r = r'.
Proof. intros. inversion H; subst; auto. Qed.
Lemma Ops_cons : forall c g top e es ops r r', CompOps c g top (e :: es) ops r r' ->
 exists o os top2 r1, ops = o :: os /\ CompOp c g top e o top2 r r1 /\ CompOps c g top2 es os r1 r'.
Proof. intros. inversion H; subst; do 4 eexists; eauto. Qed.
Lemma W_nil_inv : forall c g s0 r r', CompW c g s0 [] r r' -> r = r'.
Proof. intros. inversion H; subst; auto. Qed.
Lemma W_cons_inv : forall c g s0 e es r r', CompW c g s0 (e :: es) r r' ->
 exists r1, Comp c g (s0 + 1) e (DSlot s0) r r1 /\ CompW c g (s0 + 1) es r1 r'.
Proof. intros. inversion H; subst; eauto. Qed.
Lemma TA_nil_inv : forall c g s0 t ms r r', CompTA c g s0 t [] ms r r' -> r = map (fun x => B.IMove (fst x) (snd x)) ms ++ r'.
Proof. intros. inversion H; subst; auto. Qed.

(* The constant pguard asks for is among the values read. *)
Lemma guard_read : forall m q os ys, B.all_some (map (B.read_op m) os) = Some ys ->
 pguard (code m) q os = true -> vguard q ys = true.
Proof.
 intros m q os ys A G. destruct q; try reflexivity. cbn in G |- *.
 revert ys A. induction os as [|o os IH]; intros ys A; [discriminate|].
 cbn in A. destruct (B.read_op m o) as [y|] eqn:Ro; [|discriminate].
 destruct (B.all_some (map (B.read_op m) os)) as [ys'|]; cbn in A; [|discriminate]. injection A as <-.
 cbn in G |- *. apply orb_true_iff in G as [G|G].
 - destruct o as [s0|k]; [discriminate|]. cbn in Ro. unfold eq_safe_op, konst in G. rewrite Ro in G. rewrite G. reflexivity.
 - rewrite (IH G ys' eq_refl). apply orb_true_r.
Qed.

Lemma ret_prim : forall s v v' m o f p q vals es rho k1 g top ops dops d r1 w w1,
 Com s m -> read_o (code m) (fp m) (st m) o = Some v' -> VR v v' ->
 prim_of_name f = Some p -> pmap p = Some q ->
 (List.length vals + 1 + List.length es)%nat = prim_arity p ->
 MEnv (fp m) (st m) g rho -> Prot g (fp m) w -> EnvBelow g top ->
 CompOps (code m) g top es ops (B.m_rest m) (B.IPrim d q (rev dops ++ o :: ops) :: r1) ->
 pguard (code m) q (rev dops ++ o :: ops) = true ->
 DoneR (code m) (fp m) (st m) vals dops -> Forall (o_safe (fp m) w) dops ->
 Forall (o_below top) dops -> o_below top o ->
 Sub w w1 -> Above (fp m) top w1 -> w1 (fp m + d) -> KD (code m) (fp m) (st m) (cs m) w1 (B.OSlot d) r1 k1 ->
 Out s (Cfg (Ret v) (KCallArgs f vals es rho :: k1) s) m.
Proof.
 intros s v v' m o f p q vals es rho k1 g top ops dops d r1 w w1 Cm Rd Vr Pn Pm Ln Me Pr Eb Co Pg Dr Fs Fb Ob Sb Ab Wd Kd.
 assert (Nk1 : notrap k1) by (eapply notrap_kd; eauto).
 destruct es as [|a es].
 - destruct (Ops_nil _ _ _ _ _ _ Co) as [-> Hr]. clear Co.
   destruct (done_all _ _ _ _ _ Dr (B.set_rest m r1) eq_refl eq_refl eq_refl) as [xs [A1 A2]].
   assert (All : B.all_some (map (B.read_op (B.set_rest m r1)) (rev dops ++ [o])) = Some (xs ++ [v'])).
   { eapply all_some_app; [exact A1|]. cbn [map]. cbn [B.all_some]. rewrite read_eq. change (read_o (code m) (fp m) (st m) o) with (read_o (code (B.set_rest m r1)) (fp (B.set_rest m r1)) (st (B.set_rest m r1)) o) in Rd. rewrite Rd. reflexivity. }
   assert (Fr : Forall2 VR (rev (v :: vals)) (xs ++ [v'])) by (cbn [rev]; apply Forall2_app; auto).
   assert (Len : List.length (rev (v :: vals)) = prim_arity p) by (rewrite rev_length; cbn [List.length] in *; lia).
   assert (Lk : lookup f (gfuns s) = Some (FPrim p)) by (destruct Cm as [_ Fn]; apply (fr_name s m Fn); auto).
   assert (Nm := n_prim m d q _ r1 _ Hr All).
   assert (Nc : next_r (jit_rules sealed) jit_profile (Cfg (Ret v) (KCallArgs f vals [] rho :: k1) s) =
     call_named_r (jit_rules sealed) jit_profile f (rev (v :: vals)) k1 s) by reflexivity.
   assert (Hh : B.m_handlers (B.set_rest m r1) = []) by (destruct Cm; auto).
   destruct (B.allocates q && B.e_oom E (B.m_allocs m))%bool eqn:Oo.
   + eapply finish_raise with (m1 := B.set_rest m r1) (x := XUser (of_string "out of memory")) (k := KCallArgs f vals [] rho :: k1);
       [exact Hh|exact Nm| |constructor; [exact I|exact Nk1]|reflexivity].
     eapply SS_step; [eapply step_r_resource with (r := RHeap); reflexivity|apply SS_refl].
   + assert (Gv : vguard q (xs ++ [v']) = true) by (eapply guard_read; [exact All|exact Pg]).
     destruct (prim_agree sealed E pt (B.set_rest m r1) d p q _ _ s Pm Fr Len Gv) as [v0 v0' Hs Ht Hv|x msg tv Hs Ht Hx].
     * eapply O_step with (c' := Cfg (Ret v0) k1 s) (m' := wr m r1 d v0').
       -- eapply S1'. rewrite Nc. rewrite (prim_call s f p _ k1 _ Lk Len Hs). reflexivity.
       -- left. exists (wr m r1 d v0'). split; [unfold TS; rewrite Nm, Ht; reflexivity|apply TS_refl].
       -- eapply ms_write; [exact Cm|apply KC_slot; [exact Wd|exact Kd]|exact Hv].
     * eapply finish_raise with (m1 := B.set_rest m r1) (x := x) (k := k1); [exact Hh|rewrite Nm; exact Ht| |exact Nk1|exact Hx].
       eapply S1'. rewrite Nc. rewrite (prim_call s f p _ k1 _ Lk Len Hs). reflexivity.
 - destruct (Ops_cons _ _ _ _ _ _ _ _ Co) as (o2 & os & top2 & r2 & -> & Co1 & Co2).
   destruct (CompOp_mono _ _ _ _ _ _ _ _ Co1) as [L1 L2].
   eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_op with (w := w_top (fp m) top); [exact Cm|exact Co1|exact Me|exact Eb|intros q0 X; exact X|].
   eapply KD_prim with (g := g) (top := top2) (ops := os) (dops := o :: dops) (d := d) (r1 := r1) (w1 := w1) (p := p) (q := q).
   + exact Pn.
   + exact Pm.
   + cbn [List.length] in *. lia.
   + exact Me.
   + apply Prot_below; auto.
   + eapply EnvBelow_mono; eauto.
   + cbn [rev]. rewrite <- app_assoc. exact Co2.
   + cbn [rev]. rewrite <- app_assoc. exact Pg.
   + econstructor; eauto.
   + constructor; [destruct o; cbn in *; [unfold w_top; lia|auto]|apply below_safe; auto].
   + constructor; [eapply o_below_mono; eauto|eapply below_mono; eauto].
   + exact L2.
   + intros q0 X; apply Ab. unfold w_top in X. exact X.
   + intros q0 X; apply Ab. lia.
   + exact Wd.
   + exact Kd.
Qed.

Lemma ret_call : forall s v v' m f vals es rho k1 g a s0 d n i r1 w1,
 Com s m -> slotv (st m) (fp m + s0) = Some v' -> VR v v' ->
 not_prim_name f -> s0 = a + 2 + N.of_nat (List.length vals) ->
 n = N.of_nat (List.length vals + 1 + List.length es) ->
 MEnv (fp m) (st m) g rho -> EnvBelow g (s0 + 1) ->
 CompW (code m) g (s0 + 1) es (B.m_rest m) (i :: r1) -> call_instr i d a (B.sym_of_text f) n ->
 ArgsAt (st m) (fp m + a + 2) (rev vals) ->
 Above (fp m) a w1 -> w1 (fp m + d) -> KD (code m) (fp m) (st m) (cs m) w1 (B.OSlot d) r1 k1 ->
 Out s (Cfg (Ret v) (KCallArgs f vals es rho :: k1) s) m.
Proof.
 intros s v v' m f vals es rho k1 g a s0 d n i r1 w1 Cm Rd Vr Np Hs Hn Me Eb Cw Ci Aa Ab Wd Kd.
 assert (Nk1 : notrap k1) by (eapply notrap_kd; eauto).
 assert (Aa2 : ArgsAt (st m) (fp m + a + 2) (rev (v :: vals))).
 { cbn [rev]. eapply ArgsAt_snoc; [exact Aa| |exact Vr]. rewrite <- Rd. f_equal. rewrite rev_length. subst. lia. }
 destruct es as [|e es].
 - assert (Hr := W_nil_inv _ _ _ _ _ Cw). clear Cw.
   eapply named_call with (i := i) (d := d) (a := a) (n := n) (r1 := r1) (w1 := w1) (k0 := KCallArgs f vals [] rho :: k1);
     [exact Cm|reflexivity|reflexivity|reflexivity|reflexivity|constructor; [exact I|exact Nk1]|exact Np|exact Hr|exact Ci|
      rewrite rev_length; subst n; f_equal; cbn [List.length]; lia|exact Aa2|exact Ab|exact Wd|exact Kd].
 - destruct (W_cons_inv _ _ _ _ _ _ _ Cw) as (r2 & C1 & C2). subst s0.
   eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_eval with (w := w_top (fp m) (a + 2 + N.of_nat (List.length vals) + 1)) (dst := DSlot (a + 2 + N.of_nat (List.length vals) + 1));
     [exact Cm|exact C1|exact Me|eapply EnvBelow_mono; [exact Eb|lia]|intros q0 X; unfold w_top; lia|].
   apply KC_slot; [unfold w_top; lia|].
   eapply KD_call with (g := g) (a := a) (s := a + 2 + N.of_nat (List.length vals) + 1) (i := i) (d := d) (n := n) (r1 := r1) (w1 := w1).
   + exact Np.
   + cbn [List.length]. lia.
   + rewrite Hn. cbn [List.length]. f_equal. lia.
   + exact Me.
   + apply Prot_below; auto.
   + eapply EnvBelow_mono; [exact Eb|lia].
   + exact C2.
   + exact Ci.
   + exact Aa2.
   + intros q0 X; exact X.
   + intros q0 X. apply Ab. unfold w_top in X. lia.
   + exact Ab.
   + exact Wd.
   + exact Kd.
Qed.

Lemma ret_tail : forall s v v' m f vals es rho k1 g s0 t ms n i r1,
 Com s m -> slotv (st m) (fp m + loc ms s0) = Some v' -> VR v v' ->
 not_prim_name f -> s0 = 2 + N.of_nat (List.length vals) ->
 n = N.of_nat (List.length vals + 1 + List.length es) -> n + 2 <= t ->
 MEnv (fp m) (st m) g rho -> EnvBelow g t ->
 CompTA (code m) g (s0 + 1) t es ms (B.m_rest m) (i :: r1) -> tail_instr i 0 (B.sym_of_text f) n ->
 Forall (fun x => 2 <= fst x < s0 + 1 /\ n + 2 <= snd x < t) ms -> NoDup (map fst ms) ->
 ParamAt (fp m) (st m) ms 2 (rev vals) -> RK (fp m) (st m) (cs m) k1 ->
 Out s (Cfg (Ret v) (KCallArgs f vals es rho :: k1) s) m.
Proof.
 intros s v v' m f vals es rho k1 g s0 t ms n i r1 Cm Rd Vr Np Hs Hn Ht Me Eb Ct Ti F D Pa Rk.
 assert (Nk1 : notrap k1) by (eapply (proj2 (proj2 (proj2 K_notrap))); eauto).
 assert (Pa2 : ParamAt (fp m) (st m) ms 2 (rev (v :: vals))).
 { cbn [rev]. eapply ParamAt_snoc; [exact Pa| |exact Vr]. rewrite rev_length. rewrite <- Rd. subst s0. reflexivity. }
 destruct es as [|e es].
 - assert (Hr := TA_nil_inv _ _ _ _ _ _ _ Ct). clear Ct.
   eapply tail_fire with (ms := ms) (i := i) (n := n) (r1 := r1) (lim := n + 2) (k0 := KCallArgs f vals [] rho :: k1);
     [exact Cm|reflexivity|reflexivity|reflexivity|reflexivity|constructor; [exact I|exact Nk1]|exact Np|exact Hr|exact Ti|
      rewrite rev_length; rewrite Hn; cbn [List.length]; f_equal; lia|reflexivity| |exact D|exact Pa2|exact Rk].
   eapply Forall_impl; [|exact F]. intros [u x]; cbn [fst snd]. rewrite Hn, Hs. cbn [List.length] in *. lia.
 - eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply ta_start with (g := g) (s0 := s0 + 1) (t := t) (ms := ms) (i := i) (r1 := r1) (n := n); try reflexivity.
   + exact Cm.
   + exact Ct.
   + exact Me.
   + exact Eb.
   + exact Np.
   + subst. cbn [List.length]. lia.
   + subst. cbn [List.length]. f_equal. lia.
   + exact Ht.
   + exact Ti.
   + exact F.
   + exact D.
   + exact Pa2.
   + exact Rk.
Qed.

(* ---------- a value arrives ---------- *)
Lemma RK_inv : forall f s0 ks k, RK f s0 ks k -> (ks = [] /\ k = []) \/
 exists c r d a cs w, ks = B.Cont c r d a :: cs /\ a <= f /\ Above (f - a) a w /\
   KD c (f - a) s0 cs w (B.OSlot d) r k /\ w (f - a + d).
Proof. intros f s0 ks k H. inversion H; subst; [left; auto|right; do 6 eexists; eauto]. Qed.

Lemma step_ret : forall c f s0 ks w o r k, KD c f s0 ks w o r k -> forall s v v' m,
 Com s m -> code m = c -> fp m = f -> st m = s0 -> cs m = ks -> B.m_rest m = r ->
 read_o c f s0 o = Some v' -> VR v v' -> Out s (Cfg (Ret v) k s) m.
Proof.
 intros c f s0 ks w o r k H. induction H; intros s0' v v' m Cm Hc Hf Hs Hk Hr Rd Vr; subst.
 - (* return *)
   destruct (RK_inv _ _ _ _ H0) as [[Hc0 ->]|(c1 & r1 & d & a & cs1 & w1 & Hc0 & La & Ab & Kd & Wd)].
   + eapply O_ok; [apply SS_refl|apply TS_refl|rewrite (n_ret m o r v' Hr Rd); unfold B.do_return; cbn [B.m_conts B.set_rest]; rewrite Hc0; reflexivity|exact Vr].
   + pose (m1 := B.set_ctl (B.set_rest m r) (B.tset (B.skey (fp m - a + d)) v' (st m)) (fp m - a) c1 r1 cs1).
     eapply O_step with (c' := Cfg (Ret v) k s0') (m' := m1); [apply SS_refl| |].
     * left. exists m1. split; [|apply TS_refl]. unfold TS. rewrite (n_ret m o r v' Hr Rd). unfold B.do_return. cbn [B.m_conts B.set_rest]. rewrite Hc0. reflexivity.
     * eapply MS_ret with (o := B.OSlot d) (w := w1).
       -- eapply Com_same; eauto.
       -- apply slotv_same.
       -- exact Vr.
       -- eapply KD_stable; [exact Kd|]. intros a0 N0. symmetry. apply slotv_other. intro; subst; contradiction.
 - eapply Out_t; [eapply n_jump; eauto|]. eapply IHKD; [apply Com_rest; auto|reflexivity..|exact Rd|exact Vr].
 - eapply Out_t; [eapply n_label; eauto|]. eapply IHKD; [apply Com_rest; auto|reflexivity..|exact Rd|exact Vr].
 - (* let *)
   eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_eval with (w := w1); try eassumption.
   + eapply MEnv_cons; eauto.
   + apply EnvBelow_cons; auto.
 - eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_test with (w := w1); try eassumption.
   + eapply MEnv_cons; eauto.
   + apply EnvBelow_cons; auto.
 - (* jump-if-false *)
   assert (Nj := n_jif m o l r v' Hr Rd).
   destruct v' as [| | |[|]| | | | | | | | | |];
   try (assert (Nb : forall bb, v <> VBool bb) by (intros bb Eb; subst v; inversion Vr);
     destruct (tk_nb _ _ _ _ _ _ _ _ _ H eq_refl s0' v Nb) as (k' & Ss & Nk);
     eapply finish_raise with (m1 := B.set_rest m r); [destruct Cm; auto|exact Nj|exact Ss|exact Nk|exact I]; fail).
   + inversion Vr; subst. eapply Out_t; [exact Nj|]. eapply tk_true; [exact H|apply Com_rest; auto|reflexivity..].
   + inversion Vr; subst.
     destruct (tk_label _ _ _ _ _ _ _ _ _ H) as [re Rl].
     assert (Nj2 : TS m (B.set_rest (B.set_rest m r) re)).
     { unfold TS. rewrite Nj. change (B.find_label l (B.code_ins (code m))) with (lbl (code m) l). rewrite Rl. reflexivity. }
     eapply Out_t; [exact Nj2|]. eapply tk_false; [exact H|apply Com_rest, Com_rest; auto|reflexivity..|exact Rl|reflexivity].
 - (* a primitive's argument *)
   eapply ret_prim; eassumption.
 - (* a call's argument *)
   eapply ret_call; [exact Cm|exact Rd|exact Vr|eassumption|reflexivity|reflexivity|eassumption..].
 - (* a tail call's argument *)
   eapply ret_tail with (t := t); [exact Cm|exact Rd|exact Vr|eassumption|reflexivity|reflexivity|lia|eassumption..].
Qed.

(* ---------- an expression starts ---------- *)
Definition OpStep (s : store) (m : B.machine) : Prop :=
 forall g top e o top2 r2 rho k w, CompOp (code m) g top e o top2 (B.m_rest m) r2 ->
   MEnv (fp m) (st m) g rho -> EnvBelow g top -> Above (fp m) top w ->
   KD (code m) (fp m) (st m) (cs m) w o r2 k -> Out s (Cfg (Eval rho e) k s) m.

Lemma KD_of_KC : forall c f s0 ks w d r k, KC c f s0 ks w (DSlot d) r k -> w (f + d) /\ KD c f s0 ks w (B.OSlot d) r k.
Proof. intros. inversion H; subst; auto. Qed.
Lemma RK_of_KC : forall c f s0 ks w r k, KC c f s0 ks w DRet r k -> Sub w (fun a => f <= a) /\ RK f s0 ks k.
Proof. intros. inversion H; subst; auto. Qed.

Lemma step_eval0 : forall s m e g top dst r2 rho k w,
 (dst = DRet -> OpStep s m) -> Com s m -> Comp (code m) g top e dst (B.m_rest m) r2 ->
 MEnv (fp m) (st m) g rho -> EnvBelow g top -> Above (fp m) top w ->
 KC (code m) (fp m) (st m) (cs m) w dst r2 k -> Out s (Cfg (Eval rho e) k s) m.
Proof.
 intros s m e g top dst r2 rho k w OP Cm Cc Me Eb Ab Kc.
 remember (B.m_rest m) as r0 eqn:Hr. symmetry in Hr.
 assert (Nt : notrap k) by (eapply notrap_kc; eauto).
 assert (Wtop : Above (fp m) top (w_top (fp m) top)) by (intros q0 X; exact X).
 assert (Ptop : Prot g (fp m) (w_top (fp m) top)) by (apply Prot_below; auto).
 assert (Stop : Sub (w_top (fp m) top) w) by (intros q0 X; apply Ab; exact X).
 assert (Keep : B.m_rest m = r0 /\ True) by auto. clear Hr.
 inversion Cc; subst; destruct Keep as [Hr _].
 - (* literal *)
   destruct (KD_of_KC _ _ _ _ _ _ _ _ Kc) as [Wd Kd].
   eapply O_step with (c' := Cfg (Ret v) k s) (m' := wr m r2 d v').
   + eapply S1'. eapply lit_step; eauto.
   + left. exists (wr m r2 d v'). split; [eapply n_const; eauto|apply TS_refl].
   + eapply ms_write; eauto.
 - (* variable into another slot *)
   destruct (Me _ _ H) as (v & v' & L & Sl & Vr).
   eapply O_step with (c' := Cfg (Ret v) k s) (m' := wr m r2 d v').
   + eapply S1'. cbn. rewrite L. reflexivity.
   + left. exists (wr m r2 d v'). split; [eapply n_move; eauto|apply TS_refl].
   + eapply ms_write; eauto.
 - (* variable already there *)
   destruct (Me _ _ H) as (v & v' & L & Sl & Vr).
   destruct (KD_of_KC _ _ _ _ _ _ _ _ Kc) as [Wd Kd].
   eapply O_step with (c' := Cfg (Ret v) k s) (m' := m).
   + eapply S1'. cbn. rewrite L. reflexivity.
   + right. split; [reflexivity|msr_dec].
   + eapply MS_ret with (o := B.OSlot d); [exact Cm|exact Sl|exact Vr|rewrite Hr; exact Kd].
 - (* primitive: its first argument *)
   destruct (KD_of_KC _ _ _ _ _ _ _ _ Kc) as [Wd Kd].
   destruct args as [|a es]; [contradiction|].
   destruct (Ops_cons _ _ _ _ _ _ _ _ H3) as (o & os & top2 & r1 & -> & Co1 & Co2).
   destruct (CompOp_mono _ _ _ _ _ _ _ _ Co1) as [L1 L2].
   eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_op with (w := w_top (fp m) top); [exact Cm|rewrite Hr; exact Co1|exact Me|exact Eb|exact Wtop|].
   eapply KD_prim with (g := g) (top := top2) (ops := os) (dops := []) (d := d) (r1 := r2) (w1 := w) (p := p) (q := q).
   + exact H.
   + exact H0.
   + cbn [List.length] in *. lia.
   + exact Me.
   + exact Ptop.
   + eapply EnvBelow_mono; eauto.
   + exact Co2.
   + exact H4.
   + constructor.
   + constructor.
   + constructor.
   + exact L2.
   + exact Stop.
   + intros q0 X. apply Ab. lia.
   + exact Wd.
   + exact Kd.
 - (* let *)
   eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_eval with (w := w_top (fp m) top) (dst := DSlot top) (top := top + 1);
     [exact Cm|rewrite Hr; eassumption|exact Me|eapply EnvBelow_mono; [exact Eb|lia]|intros q0 X; unfold w_top; lia|].
   apply KC_slot; [unfold w_top; lia|].
   eapply KD_let with (g := g) (top := top + 1) (w1 := w); try eassumption.
   + eapply EnvBelow_mono; [exact Eb|lia].
   + lia.
   + intros q0 X. apply Ab. lia.
 - (* let of a variable: the same slot *)
   assert (Ls := Eb _ _ H).
   eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_op with (w := w_top (fp m) top) (o := B.OSlot s0) (top := top) (top2 := top);
     [exact Cm|rewrite Hr; eapply O_var; eauto|exact Me|exact Eb|exact Wtop|].
   eapply KD_let with (g := g) (top := top) (w1 := w); try eassumption.
 - (* if, for a slot *)
   destruct (KD_of_KC _ _ _ _ _ _ _ _ Kc) as [Wd Kd].
   eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_test with (w := w_top (fp m) top); [exact Cm|rewrite Hr; eassumption|exact Me|exact Eb|exact Wtop|].
   eapply TK_if with (g := g) (top := top) (dst := DSlot d) (w1 := w); try eassumption.
   + apply KC_slot; [exact Wd|]. eapply KD_jump; eauto.
   + apply KC_slot; [exact Wd|]. eapply KD_label; eauto.
 - (* if, in tail position *)
   destruct (RK_of_KC _ _ _ _ _ _ _ Kc) as [Sw Rk].
   eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_test with (w := w_top (fp m) top); [exact Cm|rewrite Hr; eassumption|exact Me|exact Eb|exact Wtop|].
   eapply TK_if with (g := g) (top := top) (dst := DRet) (w1 := w); try eassumption; apply KC_ret; auto.
 - (* cond with no clause left *)
   assert (Nx : B.next E pt m = B.raise_s (B.set_rest m r2) "cond: no clause applies").
   { rewrite (n_prim m d B.PRaiseCond [] r2 [] Hr eq_refl). reflexivity. }
   eapply finish_raise with (m1 := B.set_rest m r2) (x := XCondFail) (k := k);
     [destruct Cm; auto|exact Nx|eapply S1'; reflexivity|exact Nt|exact I].
 - (* a clause whose test is true *)
   eapply O_step with (c' := Cfg (Eval rho x) k s) (m' := m).
   + eapply S1; [reflexivity|]. eapply S1; [reflexivity|]. eapply S1'. reflexivity.
   + right. split; [reflexivity|msr_dec].
   + eapply MS_eval with (w := w); [exact Cm|rewrite Hr; eassumption|exact Me|exact Eb|exact Ab|exact Kc].
 - (* cond, for a slot *)
   destruct (KD_of_KC _ _ _ _ _ _ _ _ Kc) as [Wd Kd].
   eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_test with (w := w_top (fp m) top); [exact Cm|rewrite Hr; eassumption|exact Me|exact Eb|exact Wtop|].
   eapply TK_cond with (g := g) (top := top) (dst := DSlot d) (w1 := w); try eassumption.
   + apply KC_slot; [exact Wd|]. eapply KD_jump; eauto.
   + apply KC_slot; [exact Wd|]. eapply KD_label; eauto.
 - (* cond, in tail position *)
   destruct (RK_of_KC _ _ _ _ _ _ _ Kc) as [Sw Rk].
   eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_test with (w := w_top (fp m) top); [exact Cm|rewrite Hr; eassumption|exact Me|exact Eb|exact Wtop|].
   eapply TK_cond with (g := g) (top := top) (dst := DRet) (w1 := w); try eassumption; apply KC_ret; auto.
 - (* type *)
   eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_eval with (w := w); [exact Cm|rewrite Hr; eassumption|exact Me|exact Eb|exact Ab|exact Kc].
 - (* and, as a value *)
   destruct (KD_of_KC _ _ _ _ _ _ _ _ Kc) as [Wd Kd].
   eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_test with (w := w_top (fp m) top); [exact Cm|rewrite Hr; eassumption|exact Me|exact Eb|exact Wtop|].
   eapply TK_and with (g := g) (top := top) (w1 := w) (gd := false); try eassumption.
   eapply TK_value with (w1 := w); try eassumption.
   + intros q0 X; exact X.
   + eapply KD_jump; eauto.
   + eapply KD_label; eauto.
 - (* or, as a value *)
   destruct (KD_of_KC _ _ _ _ _ _ _ _ Kc) as [Wd Kd].
   assert (Tv : TK (code m) (fp m) (st m) (cs m) w false l (B.IConst d kt :: B.IJump e0 :: B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r2) k).
   { eapply TK_value with (w1 := w); try eassumption.
     + intros q0 X; exact X.
     + eapply KD_jump; eauto.
     + eapply KD_label; eauto. }
   eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_test with (w := w_top (fp m) top); [exact Cm|rewrite Hr; eassumption|exact Me|exact Eb|exact Wtop|].
   eapply TK_or with (g := g) (top := top) (w1 := w) (gd := false) (l := l); try eassumption.
   + eapply TK_label. exact Tv.
   + eapply TK_jump; [eassumption|exact Tv].
 - (* returned *)
   destruct (RK_of_KC _ _ _ _ _ _ _ Kc) as [Sw Rk].
   eapply (OP eq_refl); [rewrite Hr; eassumption|exact Me|exact Eb|exact Ab|].
   eapply KD_ret; eauto.
 - (* named call *)
   destruct (KD_of_KC _ _ _ _ _ _ _ _ Kc) as [Wd Kd].
   destruct args as [|a es].
   + assert (Hr2 := W_nil_inv _ _ _ _ _ H1). rewrite <- Hr in Hr2.
     eapply named_call with (i := i) (d := d) (a := top) (n := N.of_nat 0) (r1 := r2) (w1 := w) (k0 := k);
       [exact Cm|reflexivity|reflexivity|reflexivity|reflexivity|exact Nt|exact H|exact Hr2|exact H2|reflexivity|constructor|exact Ab|exact Wd|exact Kd].
   + destruct (W_cons_inv _ _ _ _ _ _ _ H1) as (r1 & C1 & C2).
     eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
     eapply MS_eval with (w := w_top (fp m) (top + 2)) (dst := DSlot (top + 2)) (top := top + 2 + 1);
       [exact Cm|rewrite Hr; exact C1|exact Me|eapply EnvBelow_mono; [exact Eb|lia]|intros q0 X; unfold w_top; lia|].
     apply KC_slot; [unfold w_top; lia|].
     eapply KD_call with (g := g) (a := top) (s := top + 2) (i := i) (d := d) (n := N.of_nat (List.length (a :: es))) (r1 := r2) (w1 := w).
     * exact H.
     * cbn [List.length]. lia.
     * cbn [List.length]. f_equal; try lia.
     * exact Me.
     * apply Prot_below; eapply EnvBelow_mono; [exact Eb|lia].
     * eapply EnvBelow_mono; [exact Eb|lia].
     * exact C2.
     * exact H2.
     * constructor.
     * intros q0 X; exact X.
     * intros q0 X. apply Ab. unfold w_top in X. lia.
     * exact Ab.
     * exact Wd.
     * exact Kd.
 - (* named tail call *)
   destruct (RK_of_KC _ _ _ _ _ _ _ Kc) as [Sw Rk].
   destruct args as [|a es].
   + assert (Hr2 := TA_nil_inv _ _ _ _ _ _ _ H3). rewrite <- Hr in Hr2.
     eapply tail_fire with (ms := []) (i := i) (n := N.of_nat 0) (r1 := r2) (lim := N.of_nat 0 + 2) (k0 := k);
       [exact Cm|reflexivity|reflexivity|reflexivity|reflexivity|exact Nt|exact H|exact Hr2|exact H4|reflexivity|reflexivity|constructor|constructor|constructor|exact Rk].
   + eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
     eapply ta_start with (g := g) (s0 := 2) (t := t) (ms := []) (i := i) (r1 := r2) (n := N.of_nat (List.length (a :: es))).
     * exact Cm.
     * reflexivity.
     * rewrite Hr. exact H3.
     * exact Me.
     * eapply EnvBelow_mono; [exact Eb|exact H2].
     * exact H.
     * reflexivity.
     * cbn [List.length]. f_equal.
     * exact H1.
     * exact H4.
     * constructor.
     * constructor.
     * constructor.
     * exact Rk.
 - (* a cons chain: the source takes the constant head, then runs the tail into d with the cons
      pending; the frame binds nothing, so it is safe whatever d held *)
   destruct (KD_of_KC _ _ _ _ _ _ _ _ Kc) as [Wd Kd].
   eapply O_step with (c' := Cfg (Eval rho e0) (KCallArgs f [v] [] rho :: k) s) (m' := m).
   + eapply S1; [reflexivity|]. eapply S1; [eapply lit_step; eauto|]. eapply S1'; reflexivity.
   + right. split; [reflexivity|]. pose proof (esize_pos a). msr_dec.
   + eapply MS_eval with (g := g) (top := top) (dst := DSlot d) (w := w); [exact Cm|rewrite Hr; eassumption|exact Me|exact Eb|exact Ab|].
     apply KC_slot; [exact Wd|].
     eapply KD_prim with (g := []) (top := top + d + 1) (es := []) (ops := []) (dops := [B.OConst k0])
       (vals := [v]) (d := d) (r1 := r2) (w1 := w) (p := PCons) (q := B.PCons) (rho := rho).
     * exact H.
     * reflexivity.
     * reflexivity.
     * intros x0 s0 L0. discriminate L0.
     * intros x0 s0 L0. discriminate L0.
     * intros x0 s0 L0. discriminate L0.
     * constructor.
     * reflexivity.
     * econstructor; [exact H1|exact H2|constructor].
     * constructor; [exact I|constructor].
     * constructor; [exact I|constructor].
     * cbn. lia.
     * intros q0 X; exact X.
     * intros q0 X. apply Ab. lia.
     * exact Wd.
     * exact Kd.
Qed.

Lemma step_op : forall s m, Com s m -> OpStep s m.
Proof.
 intros s m Cm g top e o top2 r2 rho k w Co Me Eb Ab Kd.
 remember (B.m_rest m) as r0 eqn:Hr. symmetry in Hr.
 assert (Keep : B.m_rest m = r0 /\ True) by auto. clear Hr.
 inversion Co; subst; destruct Keep as [Hr _].
 - destruct (Me _ _ H) as (v & v' & L & Sl & Vr).
   eapply O_step with (c' := Cfg (Ret v) k s) (m' := m).
   + eapply S1'. cbn. rewrite L. reflexivity.
   + right. split; [reflexivity|msr_dec].
   + eapply MS_ret with (o := B.OSlot s0); [exact Cm|exact Sl|exact Vr|rewrite Hr; exact Kd].
 - eapply O_step with (c' := Cfg (Ret v) k s) (m' := m).
   + eapply S1'. eapply lit_step; eauto.
   + right. split; [reflexivity|unfold msr; cbn -[esize]; pose proof (esize_pos e); lia].
   + eapply MS_ret with (o := B.OConst k0); [exact Cm|exact H0|exact H1|rewrite Hr; exact Kd].
 - eapply step_eval0 with (dst := DSlot top) (top := top + 1) (w := w); [discriminate|exact Cm|rewrite Hr; eassumption|exact Me|
     eapply EnvBelow_mono; [exact Eb|lia]|intros q0 X; apply Ab; lia|].
   apply KC_slot; [apply Ab; lia|exact Kd].
 - eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_op with (w := w); [exact Cm|rewrite Hr; eassumption|exact Me|exact Eb|exact Ab|exact Kd].
Qed.

Lemma step_eval : forall s m e g top dst r2 rho k w,
 Com s m -> Comp (code m) g top e dst (B.m_rest m) r2 ->
 MEnv (fp m) (st m) g rho -> EnvBelow g top -> Above (fp m) top w ->
 KC (code m) (fp m) (st m) (cs m) w dst r2 k -> Out s (Cfg (Eval rho e) k s) m.
Proof. intros. eapply step_eval0; eauto. intros _; apply step_op; auto. Qed.

Lemma step_test : forall s m e g top l r2 rho k w,
 Com s m -> CompT (code m) g top e l (B.m_rest m) r2 ->
 MEnv (fp m) (st m) g rho -> EnvBelow g top -> Above (fp m) top w ->
 TK (code m) (fp m) (st m) (cs m) w true l r2 k -> Out s (Cfg (Eval rho e) k s) m.
Proof.
 intros s m e g top l r2 rho k w Cm Ct Me Eb Ab Tk.
 remember (B.m_rest m) as r0 eqn:Hr. symmetry in Hr.
 assert (Wtop : Above (fp m) top (w_top (fp m) top)) by (intros q0 X; exact X).
 assert (Ptop : Prot g (fp m) (w_top (fp m) top)) by (apply Prot_below; auto).
 assert (Stop : Sub (w_top (fp m) top) w) by (intros q0 X; apply Ab; exact X).
 assert (Keep : B.m_rest m = r0 /\ True) by auto. clear Hr.
 inversion Ct; subst; destruct Keep as [Hr _].
 - eapply step_op; [exact Cm|rewrite Hr; eassumption|exact Me|exact Eb|exact Ab|]. eapply KD_test; exact Tk.
 - eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_test with (w := w_top (fp m) top); [exact Cm|rewrite Hr; eassumption|exact Me|exact Eb|exact Wtop|].
   eapply TK_and with (g := g) (top := top) (w1 := w) (gd := true); eassumption.
 - eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_test with (w := w_top (fp m) top); [exact Cm|rewrite Hr; eassumption|exact Me|exact Eb|exact Wtop|].
   eapply TK_or with (g := g) (top := top) (w1 := w) (gd := true) (l := l); try eassumption.
   + eapply TK_label; exact Tk.
   + eapply TK_jump; [eassumption|exact Tk].
 - eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_eval with (w := w_top (fp m) top) (dst := DSlot top) (top := top + 1);
     [exact Cm|rewrite Hr; eassumption|exact Me|eapply EnvBelow_mono; [exact Eb|lia]|intros q0 X; unfold w_top; lia|].
   apply KC_slot; [unfold w_top; lia|].
   eapply KD_lett with (g := g) (top := top + 1) (w1 := w); try eassumption.
   + eapply EnvBelow_mono; [exact Eb|lia].
   + lia.
   + intros q0 X. apply Ab. lia.
 - assert (Ls := Eb _ _ H).
   eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_op with (w := w_top (fp m) top) (o := B.OSlot s0) (top := top) (top2 := top);
     [exact Cm|rewrite Hr; eapply O_var; eauto|exact Me|exact Eb|exact Wtop|].
   eapply KD_lett with (g := g) (top := top) (w1 := w); try eassumption.
 - eapply O_step; [eapply S1'; reflexivity|right; split; [reflexivity|msr_dec]|].
   eapply MS_test with (w := w); [exact Cm|rewrite Hr; eassumption|exact Me|exact Eb|exact Ab|exact Tk].
Qed.

(* One step of the simulation. *)
Theorem sim : forall s c m, MS s c m -> Out s c m.
Proof.
 intros s c m H. inversion H; subst.
 - eapply step_eval; eauto.
 - eapply step_test; eauto.
 - eapply step_op; [auto|eauto..].
 - eapply step_ret; eauto.
Qed.
End Sim.
End JitLowerStep.
