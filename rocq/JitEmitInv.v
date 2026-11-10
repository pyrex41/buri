(* Shen/JIT Phase 2, emit-spec: the generalized invariant of the back end, and the statements the
   emission families (emit-sim) and checkers (emit-check) must prove. Statements only, each a
   `Definition ... : Prop` with a "Does NOT say" note; NOTHING here is assumed or Admitted.
   Proved here (closed): VR_VRh (JitLowerRel's VR is VRh under every partial bijection and heap),
   VRh_no_partial, Ends'_final (Ends' names the machine that finishes), the embedding of the old
   invariant at mu = [] (kont_embed, sm_embed, ms_embed), and the three *_old_of_new implications.

   What the old invariant (JitLowerStep.MS, JitLowerThm) fixes, and what this one lets evolve:
   - mu, a partial bijection between KLambda heap locations (nat) and bytecode heap keys
     (positive), NoDup on both sides: vectors through mu, and a closure's identity cell (KLPort's
     closure_id, the cell every lambda and freeze allocates under jit_rules) to the key of its
     OClo object. A cell outside mu is one only one side made. mu grows (mext) along a run.
   - VRh mu h: JitLowerRel.VR, plus vectors through mu, lambda and freeze closures (code object
     nc with CloOK, captures related to the closure's environment, identity through mu), VExn to
     OExn (message as exn_ok asks), and streams by handle. It relates NO partial application.
   - SM mu s k m: gvals through VRh (an unbound global is unbound or VCleared in the machine),
     heap cells through mu, FunRel restated over JitEmitRel (FunRel'), the kernel's do, and the
     machine's handlers against the KTrap frames of k, in order (HK; the code each handler runs
     is related by the KD'_trap frame of JitEmitKont).
   - the KLambda store evolves: MS' reads it from the configuration (mem c), where MS fixed it.
   - IO: both sides' traces, equal as lists of Observation events (target events through ev_of).
   - Out' has a generic raising case O'_raise, and an IO case O'_io.

   New statement                          generalizes (old, proved)
   ------------------------------------   ---------------------------------------------------
   VRh / SMs / SM / MS'                   JitLowerRel.VR / JitLowerStep.Com / Com / MS
   Out'                                   JitLowerStep.Out
   SimC / SimT / SimO                     the cases of JitLowerStep.step_eval0/step_test/step_op
   sim_<X>_statement (X = Eq, Store,      JitLowerStep.sim, per family: the C_X, T_X and O_X
     Prim, DoFold, Clo, App, Trap)          hooks of JitEmitRel, given the nested IH
   sim'_statement                         JitLowerStep.sim
   Ends'                                  JitLowerThm.Ends
   preservation'_statement                JitLowerThm.preservation
   call_preservation'_statement           JitLowerThm.call_preservation
   EndsSrc'                               JitKRef.EndsSrc
   call_preservation_src'_statement       JitKRef.call_preservation_src_statement
   preservation_old_statement             JitLowerThm.preservation's premises (MS), new conclusion
   call_preservation_old_statement        JitLowerThm.call_preservation's premises, new conclusion
   call_preservation_src_old_statement    JitKRef.call_preservation_src_statement's premises, new
                                            conclusion
   ms_embed, sm_embed, kont_embed         MS, Com, KD/TK/KC/RK are MS', SM, KD'/... at mu = []
   The old fragment: empty mu, no handlers, no capture, what MS, Com and JitLowerRel.CompFn
   describe. Each *_old_statement is proved from its new statement, by the *_old_of_new theorems (closed). *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitProfile
 JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef
 JitEmitRuleEq JitEmitRuleStore JitEmitRulePrim JitEmitRuleDoFold JitEmitRuleClo JitEmitRuleApp JitEmitRuleTrap
 JitEmitRel JitEmitKont.
Import ListNotations.
Module JitEmitInv.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitLowerKont.JitLowerKont JitLowerPrim.JitLowerPrim
 JitLowerStep.JitLowerStep JitLowerThm.JitLowerThm JitEmitRel.JitEmitRel JitEmitKont.JitEmitKont.
Module B := JitBytecode.JitBytecode.
Local Open Scope N_scope.

(* ---------- the partial bijection ---------- *)
Definition kmap := list (nat * positive).
Definition pbij (mu : kmap) : Prop := NoDup (map fst mu) /\ NoDup (map snd mu).
Definition mext (mu mu' : kmap) : Prop := incl mu mu' /\ pbij mu'.

(* ---------- values ---------- *)
(* Does NOT say: anything about a closure with a multi-argument entry (CloOK excludes it), a
   closure whose environment has no identity cell (none under jit_rules), a partial application
   (related to nothing, so no theorem here speaks of one), or an exception's value beyond its
   message (the bytecode keeps one for some errors; the source's exn has no room for it). *)
Inductive VRh (mu : kmap) (h : B.tree B.obj) : value -> B.val -> Prop :=
 | VRh_int z : VRh mu h (VNum (NInt z)) (B.VFix z)
 | VRh_real b : VRh mu h (VNum (NFloat b)) (B.VReal b)
 | VRh_sym s : VRh mu h (VSym s) (B.VSym (B.sym_of_text s))
 | VRh_bool b : VRh mu h (VBool b) (B.VBool b)
 | VRh_str t : VRh mu h (VStr t) (B.VStr t)
 | VRh_nil : VRh mu h VNil B.VNil
 | VRh_cons a a' d d' : VRh mu h a a' -> VRh mu h d d' -> VRh mu h (VCons a d) (B.VPair a' d')
 | VRh_vec l p cells : In (l, p) mu -> B.tget p h = Some (B.OVec cells) -> VRh mu h (VVec l) (B.VVec p)
 | VRh_lam x b rho p nc caps cv l0 : B.tget p h = Some (B.OClo nc caps) -> CloOK nc cv [x] b ->
     closure_id rho = Some l0 -> In (l0, p) mu -> List.length cv = List.length caps ->
     (forall i y, nth_error cv i = Some y -> lookup y (bind [x] 2) = None ->
        exists v v', lookup y rho = Some v /\ nth_error caps i = Some v' /\ VRh mu h v v') ->
     VRh mu h (VLam x b rho) (B.VClo p)
 | VRh_frozen b rho p nc caps cv l0 : B.tget p h = Some (B.OClo nc caps) -> CloOK nc cv [] b ->
     closure_id rho = Some l0 -> In (l0, p) mu -> List.length cv = List.length caps ->
     (forall i y, nth_error cv i = Some y ->
        exists v v', lookup y rho = Some v /\ nth_error caps i = Some v' /\ VRh mu h v v') ->
     VRh mu h (VFrozen b rho) (B.VClo p)
 | VRh_exn x p msg tv : B.tget p h = Some (B.OExn msg tv) -> exn_ok x msg -> VRh mu h (VExn x) (B.VExn p)
 | VRh_stream hd p d o : B.tget p h = Some (B.OStream hd d o) -> VRh mu h (VStream hd) (B.VStream p).

(* JitLowerRel's VR is VRh, under every mu and heap. *)
Theorem VR_VRh : forall mu h v v', VR v v' -> VRh mu h v v'.
Proof. intros mu h v v' H; induction H; constructor; assumption. Qed.

(* No partial application is related to anything, a closure in particular. *)
Theorem VRh_no_partial : forall mu h f args v', ~ VRh mu h (VPartial f args) v'.
Proof. intros mu h f args v' H; inversion H. Qed.

Definition HeapClo (h : B.tree B.obj) (p : positive) (c : B.code) (caps : list B.val) : Prop :=
 B.tget p h = Some (B.OClo c caps).

(* ---------- the store and the machine ---------- *)
(* The function table: JitLowerStep.FunRel with JitEmitRel's CompFn'. *)
Record FunRel' (s : store) (m : B.machine) : Prop := {
 fr'_user : forall f ps b, lookup f (gfuns s) = Some (FUser ps b) -> exists l c caps,
   B.tget (B.sym_of_text f) (B.m_gfun m) = Some (B.VClo l) /\
   B.tget l (B.m_heap m) = Some (B.OClo c caps) /\
   B.code_arity c = N.of_nat (List.length ps) /\ B.code_entry c = None /\ CompFn' c ps b;
 fr'_none : forall f, lookup f (gfuns s) = None -> forall l, B.tget (B.sym_of_text f) (B.m_gfun m) <> Some (B.VClo l);
 fr'_prim : forall f p, lookup f (gfuns s) = Some (FPrim p) -> prim_of_name f = Some p;
 fr'_name : forall f p, prim_of_name f = Some p -> lookup f (gfuns s) = Some (FPrim p) }.

(* The kernel's do: (defun do (X Y) Y). JitEmitKont's do frames rely on it. *)
Definition DoOK (s : store) : Prop :=
 exists x y, x <> y /\ lookup do_name (gfuns s) = Some (FUser [x; y] (EVar y)).

(* Globals: a bound one holds a related value; an unbound one is unbound or cleared. *)
Definition GvalsRel (mu : kmap) (s : store) (m : B.machine) : Prop :=
 (forall x v, lookup x (gvals s) = Some v -> exists v',
    B.tget (B.sym_of_text x) (B.m_gval m) = Some v' /\ v' <> B.VCleared /\ VRh mu (B.m_heap m) v v') /\
 (forall x, lookup x (gvals s) = None -> forall v', B.tget (B.sym_of_text x) (B.m_gval m) = Some v' -> v' = B.VCleared).

(* Store against machine, without the continuation.
   Does NOT say: anything about cells outside mu, gfun entries of names the store does not
   define beyond fr'_none, the sealed table, or the allocation counter. *)
Record SMs (mu : kmap) (s : store) (m : B.machine) : Prop := {
 sm_bij : pbij mu;
 sm_heap : forall l p, In (l, p) mu ->
   (exists cells cells', nth_error (heap s) l = Some cells /\ B.tget p (B.m_heap m) = Some (B.OVec cells') /\
      Forall2 (VRh mu (B.m_heap m)) cells cells') \/
   (nth_error (heap s) l = Some [] /\ exists nc caps, B.tget p (B.m_heap m) = Some (B.OClo nc caps));
 sm_gvals : GvalsRel mu s m;
 sm_fun : FunRel' s m;
 sm_do : DoOK s }.

(* The source's KTrap frames, innermost first. *)
Fixpoint trap_frames (k : list frame) : list (expr * lenv) := match k with
 | [] => [] | KTrap h rho :: k => (h, rho) :: trap_frames k | _ :: k => trap_frames k end.
(* One handler per KTrap frame, in order, each with its label in its code. *)
Definition HK (hs : list B.handler) (k : list frame) : Prop :=
 Forall2 (fun hd _ => exists r, B.find_label (B.h_label hd) (B.code_ins (B.h_code hd)) = Some r) hs (trap_frames k).

Definition SM (mu : kmap) (s : store) (k : list frame) (m : B.machine) : Prop :=
 SMs mu s m /\ HK (B.m_handlers m) k.

Notation fp m := (B.m_fp m).
Notation st m := (B.m_stack m).
Notation code m := (B.m_code m).
Notation cs m := (B.m_conts m).
Notation hs m := (B.m_handlers m).
Notation V mu m := (VRh mu (B.m_heap m)).
Notation HC m := (HeapClo (B.m_heap m)).

(* What a code position needs besides its own derivation: the store, the environment (slots and
   captures), the writable addresses (never the closure in slot 1 of a code that captures), and the
   continuation. *)
Definition EvalCtx (mu : kmap) (cv : list name) (caps : list B.val) (g : env) (top : N) (dst : dest)
    (r2 : list B.instr) (rho : lenv) (k : list frame) (s : store) (w : N -> Prop) (m : B.machine) : Prop :=
 SM mu s k m /\ MEnv' (V mu m) (fp m) (st m) cv caps g rho /\ EnvBelow g top /\ Above (fp m) top w /\
 CCtx (HC m) (code m) cv caps (fp m) (st m) /\ (cv = [] \/ ~ w (fp m + 1)) /\
 KC' (V mu m) (HC m) (code m) cv caps (fp m) (st m) (cs m) (hs m) w dst r2 k.
Definition TestCtx (mu : kmap) (cv : list name) (caps : list B.val) (g : env) (top : N) (l : N)
    (r2 : list B.instr) (rho : lenv) (k : list frame) (s : store) (w : N -> Prop) (m : B.machine) : Prop :=
 SM mu s k m /\ MEnv' (V mu m) (fp m) (st m) cv caps g rho /\ EnvBelow g top /\ Above (fp m) top w /\
 CCtx (HC m) (code m) cv caps (fp m) (st m) /\ (cv = [] \/ ~ w (fp m + 1)) /\
 TK' (V mu m) (HC m) (code m) cv caps (fp m) (st m) (cs m) (hs m) w true l r2 k.
Definition OpCtx (mu : kmap) (cv : list name) (caps : list B.val) (g : env) (top : N) (o : B.operand)
    (r2 : list B.instr) (rho : lenv) (k : list frame) (s : store) (w : N -> Prop) (m : B.machine) : Prop :=
 SM mu s k m /\ MEnv' (V mu m) (fp m) (st m) cv caps g rho /\ EnvBelow g top /\ Above (fp m) top w /\
 CCtx (HC m) (code m) cv caps (fp m) (st m) /\ (cv = [] \/ ~ w (fp m + 1)) /\
 KD' (V mu m) (HC m) (code m) cv caps (fp m) (st m) (cs m) (hs m) w o r2 k.

(* The relation between a source configuration (with its own, evolving store) and a machine.
   Does NOT say: anything about a configuration at Throw, Fail or Wrong; a raise is handled inside
   one simulation step (Out' O'_raise). *)
Inductive MS' (mu : kmap) : config -> B.machine -> Prop :=
 | MS'_eval cv caps g top e dst r2 rho k s w m :
     Comp (code m) cv g top e dst (B.m_rest m) r2 -> EvalCtx mu cv caps g top dst r2 rho k s w m ->
     MS' mu (Cfg (Eval rho e) k s) m
 | MS'_test cv caps g top e l r2 rho k s w m :
     CompT (code m) cv g top e l (B.m_rest m) r2 -> TestCtx mu cv caps g top l r2 rho k s w m ->
     MS' mu (Cfg (Eval rho e) k s) m
 | MS'_op cv caps g top e o top2 r2 rho k s w m :
     CompOp (code m) cv g top e o top2 (B.m_rest m) r2 -> OpCtx mu cv caps g top o r2 rho k s w m ->
     MS' mu (Cfg (Eval rho e) k s) m
 | MS'_ret cv caps v v' o k s w m :
     SM mu s k m -> read_o (code m) (fp m) (st m) o = Some v' -> VRh mu (B.m_heap m) v v' ->
     CCtx (HC m) (code m) cv caps (fp m) (st m) -> (cv = [] \/ ~ w (fp m + 1)) ->
     KD' (V mu m) (HC m) (code m) cv caps (fp m) (st m) (cs m) (hs m) w o (B.m_rest m) k ->
     MS' mu (Cfg (Ret v) k s) m.


(* ---------- the old invariant embeds (mu = [], no handler, no capture) ---------- *)
Lemma menv_embed : forall h fp st g rho, MEnv fp st g rho -> MEnv' (VRh [] h) fp st [] [] g rho.
Proof.
 intros h fp st g rho M. split.
 - intros x s L. destruct (M x s L) as (v & v' & A & B0 & C). exists v, v'. repeat split; auto. apply VR_VRh; auto.
 - intros i x N. destruct i; discriminate.
Qed.
Lemma doner_embed : forall h c fp st vals dops, DoneR c fp st vals dops -> DoneR' (VRh [] h) c fp st vals dops.
Proof. intros h c fp st vals dops H; induction H; econstructor; eauto using VR_VRh. Qed.
Lemma argsat_embed : forall h st a vals, ArgsAt st a vals -> ArgsAt' (VRh [] h) st a vals.
Proof. intros h st a vals H; induction H; econstructor; eauto using VR_VRh. Qed.
Lemma paramat_embed : forall h fp st ms i vals, ParamAt fp st ms i vals -> ParamAt' (VRh [] h) fp st ms i vals.
Proof. intros h fp st ms i vals H; induction H; econstructor; eauto using VR_VRh. Qed.
Lemma ce_C : forall c g top e d r r', JitLowerRel.Comp c g top e d r r' -> Comp c [] g top e d r r'.
Proof. intros. apply (proj1 (comp_embed c)); auto. Qed.
Lemma ce_T : forall c g top e l r r', JitLowerRel.CompT c g top e l r r' -> CompT c [] g top e l r r'.
Proof. intros. apply (proj1 (proj2 (comp_embed c))); auto. Qed.
Lemma ce_S : forall c g top es os r r', JitLowerRel.CompOps c g top es os r r' -> CompOps c [] g top es os r r'.
Proof. intros. apply (proj1 (proj2 (proj2 (proj2 (comp_embed c))))); auto. Qed.
Lemma ce_W : forall c g s es r r', JitLowerRel.CompW c g s es r r' -> CompW c [] g s es r r'.
Proof. intros. apply (proj1 (proj2 (proj2 (proj2 (proj2 (comp_embed c)))))); auto. Qed.
Lemma ce_A : forall c g s t es ms r r', JitLowerRel.CompTA c g s t es ms r r' -> CompTA c [] g s t es ms r r'.
Proof. intros. apply (proj2 (proj2 (proj2 (proj2 (proj2 (comp_embed c)))))); auto. Qed.
Create HintDb emb.
Local Hint Resolve menv_embed doner_embed argsat_embed paramat_embed ce_C ce_T ce_S ce_W ce_A pmapx_pmap : emb.

(* JitLowerKont's frames are JitEmitKont's, with no capture and no handler, under VRh [] h. *)
Theorem kont_embed : forall h (HC : positive -> B.code -> list B.val -> Prop),
 (forall c fp st cs w o r k, KD c fp st cs w o r k -> KD' (VRh [] h) HC c [] [] fp st cs [] w o r k) /\
 (forall c fp st cs w gd l r k, TK c fp st cs w gd l r k -> TK' (VRh [] h) HC c [] [] fp st cs [] w gd l r k) /\
 (forall c fp st cs w dst r k, KC c fp st cs w dst r k -> KC' (VRh [] h) HC c [] [] fp st cs [] w dst r k) /\
 (forall fp st cs k, RK fp st cs k -> RK' (VRh [] h) HC fp st cs [] k).
Proof.
 intros h HC. apply K_mut; intros;
  [ eapply KD'_ret | eapply KD'_jump | eapply KD'_label | eapply KD'_let | eapply KD'_lett | eapply KD'_test
  | eapply KD'_prim | eapply KD'_call | eapply KD'_tail
  | eapply TK'_if | eapply TK'_cond | eapply TK'_and | eapply TK'_andr | eapply TK'_or | eapply TK'_orr
  | eapply TK'_jump | eapply TK'_label | eapply TK'_value
  | eapply KC'_ret | eapply KC'_slot | eapply RK'_top | eapply RK'_call ];
  eauto with emb; left; reflexivity.
Qed.

Lemma funrel_embed : forall s m, FunRel s m -> FunRel' s m.
Proof.
 intros s m [A1 A2 A3 A4]. constructor; auto.
 intros f ps b L. destruct (A1 f ps b L) as (l & c & caps & G & H & Ar & En & Cf).
 exists l, c, caps. repeat split; auto. apply comp_embed_fn; exact Cf.
Qed.

Lemma notrap_frames : forall k, notrap k -> trap_frames k = [].
Proof. intros k N; induction N as [|f k F N IH]; [reflexivity|destruct f; cbn; auto; contradiction]. Qed.

Lemma pbij_nil : pbij [].
Proof. split; apply NoDup_nil. Qed.

Lemma sm_embed : forall s k m, Com s m -> notrap k -> GvalsRel [] s m -> DoOK s -> SM [] s k m.
Proof.
 intros s k m [Hh Fr] Nt G Dk. split.
 - constructor; auto.
   + exact pbij_nil.
   + intros l p I; destruct I.
   + apply funrel_embed; auto.
 - unfold HK. rewrite Hh, (notrap_frames k Nt). constructor.
Qed.

(* JitLowerStep's MS is MS' at mu = [], given the two facts the old invariant does not carry. *)
Theorem ms_embed : forall s c m, MS s c m -> GvalsRel [] s m -> DoOK s -> MS' [] c m.
Proof.
 intros s c m H G Dk. destruct (kont_embed (B.m_heap m) (HeapClo (B.m_heap m))) as (EKD & ETK & EKC & ERK).
 destruct H as [g top e dst r2 rho k w m Cm Cc Me Eb Ab Kc|g top e l r2 rho k w m Cm Ct Me Eb Ab Tk
   |g top e o top2 r2 rho k w m Cm Co Me Eb Ab Kd|v v' o k w m Cm Ro Vr Kd];
   pose proof Cm as [Hh _].
 - eapply MS'_eval with (cv := []) (caps := []) (w := w); [apply ce_C; exact Cc|].
   unfold EvalCtx. split; [apply sm_embed; auto; eapply notrap_kc; exact Kc|].
   split; [apply menv_embed; auto|]. split; [auto|]. split; [auto|].
   split; [left; reflexivity|]. split; [left; reflexivity|]. rewrite Hh. apply EKC; auto.
 - eapply MS'_test with (cv := []) (caps := []) (w := w); [apply ce_T; exact Ct|].
   unfold TestCtx. split; [apply sm_embed; auto; eapply notrap_tk; exact Tk|].
   split; [apply menv_embed; auto|]. split; [auto|]. split; [auto|].
   split; [left; reflexivity|]. split; [left; reflexivity|]. rewrite Hh. apply ETK; auto.
 - eapply MS'_op with (cv := []) (caps := []) (w := w); [apply (proj1 (proj2 (proj2 (comp_embed _)))); exact Co|].
   unfold OpCtx. split; [apply sm_embed; auto; eapply notrap_kd; exact Kd|].
   split; [apply menv_embed; auto|]. split; [auto|]. split; [auto|].
   split; [left; reflexivity|]. split; [left; reflexivity|]. rewrite Hh. apply EKD; auto.
 - eapply MS'_ret with (cv := []) (caps := []) (o := o) (v' := v') (w := w).
   + apply sm_embed; auto. eapply notrap_kd; exact Kd.
   + exact Ro.
   + apply VR_VRh; auto.
   + left; reflexivity.
   + left; reflexivity.
   + rewrite Hh. apply EKD; auto.
Qed.

Section Inv.
Variables (E : B.env) (pt : B.tree (B.prim * nat)) (sealed : list name).
Notation R := (jit_rules sealed).
Notation P := jit_profile.
Notation Sstar := (Sstar sealed).
Notation TStar := (TStar E pt).
Notation TPlus := (TPlus E pt).

(* ---------- runs with traces ---------- *)
(* The source, with the IO events it performs (JitKRef.srun). *)
Definition Srun (c : config) (t : trace) (c' : config) : Prop := star (step_r R P) c t c'.

(* A bytecode IO event as a source event. The two sides are compared as equal lists.
   Does NOT say: anything about runs whose IO this does not translate. JTime (the clock arrives
   as binary64 bits, the source's as an integer), JReadFile and JWrites (no single source
   request) are None, so a trace containing one equals no source trace. open's path is the
   bytecode's, which prefixes *home-directory*: it equals the source's only when that is empty.
   A failure the bytecode reports without a cause is the source's RFailed (EOther 0). *)
Definition dir_of (d : B.stream_dir) : direction := match d with B.SIn => DIn | B.SOut => DOut end.
Definition ev_of (q : B.jreq) (r : B.jres) : option event := match q, r with
 | B.JOpen p d, B.JOpened h => Some (EvIO (QOpen p (dir_of d)) (ROpened h))
 | B.JOpen p d, B.JFailed => Some (EvIO (QOpen p (dir_of d)) (RFailed (EOther 0)))
 | B.JClose h, B.JDone => Some (EvIO (QClose h) RClosed)
 | B.JClose h, B.JFailed => Some (EvIO (QClose h) (RFailed (EOther 0)))
 | B.JRead h, B.JByte b => Some (EvIO (QRead h 1) (RRead [b]))
 | B.JRead h, B.JEof => Some (EvIO (QRead h 1) REof)
 | B.JRead h, B.JReadFailed => Some (EvIO (QRead h 1) (RFailed (EOther 0)))
 | B.JWrite h b, B.JDone => Some (EvIO (QWrite h [b]) (RWrote 1))
 | B.JWrite h b, B.JFailed => Some (EvIO (QWrite h [b]) (RFailed (EOther 0)))
 | _, _ => None end.

(* Exactly n bytecode steps, the environment answering the i-th IO request with rs i: the run is
   the machine's only one under that environment. Quantifying over rs covers every environment. *)
Inductive TRun : (nat -> B.jres) -> nat -> B.machine -> list (option event) -> B.machine -> Prop :=
 | TR_0 rs m : TRun rs 0 m [] m
 | TR_tau rs n m m1 t m2 : B.next E pt m = B.MTau m1 -> TRun rs n m1 t m2 -> TRun rs (S n) m t m2
 | TR_io rs n m q kk t m2 : B.next E pt m = B.MIO q kk ->
     TRun (fun i => rs (S i)) n (kk (rs O)) t m2 -> TRun rs (S n) m (ev_of q (rs O) :: t) m2.

(* ---------- one step ---------- *)
(* The bytecode makes progress (or the source's measure falls), keeping MS'; or performs IO, which
   the source matches with the same event under EVERY response; or both finish; or the bytecode
   raises where the source throws, with the continuations related (O'_raise: what happens next,
   a handler or the end, is the generic raising lemma's business, not each family's).
   Does NOT say: that the source does not take the resource exits step_r_resource permits. *)
Inductive Out' (mu : kmap) (c : config) (m : B.machine) : Prop :=
 | O'_step c' m' mu' : Sstar c c' -> (TPlus m m' \/ (m' = m /\ (msr c' < msr c)%nat)) ->
     mext mu mu' -> MS' mu' c' m' -> Out' mu c m
 | O'_io m1 q kk : TStar m m1 -> B.next E pt m1 = B.MIO q kk ->
     (forall r, exists c' e mu', ev_of q r = Some e /\ Srun c [e] c' /\ mext mu mu' /\ MS' mu' c' (kk r)) ->
     Out' mu c m
 | O'_ok v v' s' m1 m2 mu' : Sstar c (Cfg (Ret v) [] s') -> TStar m m1 ->
     B.next E pt m1 = B.MFinal (B.FReturn v') m2 -> mext mu mu' -> VRh mu' (B.m_heap m2) v v' ->
     SMs mu' s' m2 -> Out' mu c m
 | O'_err x l msg tv s' m1 m2 mu' : Sstar c (Cfg (Throw x) [] s') -> TStar m m1 ->
     B.next E pt m1 = B.MFinal (B.FError (B.VExn l)) m2 -> B.tget l (B.m_heap m2) = Some (B.OExn msg tv) ->
     exn_ok x msg -> mext mu mu' -> SMs mu' s' m2 -> Out' mu c m
 | O'_raise x k s' m1 m2 msg tv mu' cv caps w : Sstar c (Cfg (Throw x) k s') -> TStar m m1 ->
     B.next E pt m1 = B.raise m2 msg tv -> exn_ok x msg -> mext mu mu' -> SM mu' s' k m2 ->
     CCtx (HC m2) (code m2) cv caps (fp m2) (st m2) ->
     ((exists o r, KD' (V mu' m2) (HC m2) (code m2) cv caps (fp m2) (st m2) (cs m2) (hs m2) w o r k) \/
      (exists l r, TK' (V mu' m2) (HC m2) (code m2) cv caps (fp m2) (st m2) (cs m2) (hs m2) w true l r k) \/
      (exists dst r, KC' (V mu' m2) (HC m2) (code m2) cv caps (fp m2) (st m2) (cs m2) (hs m2) w dst r k)) ->
     Out' mu c m.

(* ---------- the simulation IH, per judgement ---------- *)
(* SimC c cv g top e dst r r2: from every machine at code c, position r, in an EvalCtx for this
   derivation's indices, the source evaluating e makes an Out' step. *)
Definition SimC (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (dst : dest) (r r2 : list B.instr) : Prop :=
 forall mu caps rho k s w m, code m = c -> B.m_rest m = r -> EvalCtx mu cv caps g top dst r2 rho k s w m ->
  Out' mu (Cfg (Eval rho e) k s) m.
Definition SimT (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (l : N) (r r2 : list B.instr) : Prop :=
 forall mu caps rho k s w m, code m = c -> B.m_rest m = r -> TestCtx mu cv caps g top l r2 rho k s w m ->
  Out' mu (Cfg (Eval rho e) k s) m.
Definition SimO (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (o : B.operand) (top2 : N) (r r2 : list B.instr) : Prop :=
 forall mu caps rho k s w m, code m = c -> B.m_rest m = r -> OpCtx mu cv caps g top o r2 rho k s w m ->
  Out' mu (Cfg (Eval rho e) k s) m.
(* The list judgements: the IH of each element, along the same chain as CompOps/CompW/CompTA. *)
Inductive SimS : B.code -> list name -> env -> N -> list expr -> list B.operand -> list B.instr -> list B.instr -> Prop :=
 | SS_nil c cv g top r : SimS c cv g top [] [] r r
 | SS_cons c cv g top e es o os top2 r r1 r' : SimO c cv g top e o top2 r r1 -> SimS c cv g top2 es os r1 r' ->
     SimS c cv g top (e :: es) (o :: os) r r'.
Inductive SimW : B.code -> list name -> env -> N -> list expr -> list B.instr -> list B.instr -> Prop :=
 | SW_nil c cv g s r : SimW c cv g s [] r r
 | SW_cons c cv g s e es r r1 r' : SimC c cv g (s + 1) e (DSlot s) r r1 -> SimW c cv g (s + 1) es r1 r' ->
     SimW c cv g s (e :: es) r r'.
Inductive SimA : B.code -> list name -> env -> N -> N -> list expr -> list (N * N) -> list B.instr -> list B.instr -> Prop :=
 | SA_nil c cv g s t ms r' : SimA c cv g s t [] ms (map (fun m => B.IMove (fst m) (snd m)) ms ++ r') r'
 | SA_same c cv g s t x es ms r r' : lookup x g = Some s -> SimA c cv g (s + 1) t es ms r r' ->
     SimA c cv g s t (EVar x :: es) ms r r'
 | SA_temp c cv g s t e es ms r r1 r' : SimC c cv g (t + 1) e (DSlot t) r r1 ->
     SimA c cv g (s + 1) (t + 1) es ((s, t) :: ms) r1 r' -> SimA c cv g s t (e :: es) ms r r'
 | SA_direct c cv g s t e es ms r r1 r' : SimC c cv g t e (DSlot s) r r1 ->
     SimA c cv (kill s g) (s + 1) t es ms r1 r' -> SimA c cv g s t (e :: es) ms r r'.

(* ---------- per family ---------- *)
(* sim_X_statement: each of family X's three hooks simulates, given the simulation IH for every
   nested sub-derivation of the rule, as Rule_X_All over (Comp, SimC), (CompT, SimT), (CompOp,
   SimO), (CompOps, SimS), (CompW, SimW), (CompTA, SimA). With every family's statement proved,
   Comp_ind' gives sim'_statement.
   Does NOT say: anything about another family's hooks, or that lower.shen produces the family's
   shapes (emit-check). At emit-spec every rule is empty and each statement holds vacuously; it
   says something once the family adds constructors. *)
(* sim_Eq_statement: = on any operands: it needs the = budget (OB-JIT-EQ-BUDGET-CORE) and mu for vectors and closure identities. Does NOT say: anything about two NaNs (RIdentity, OB-JIT-NAN-IDENTITY) unless the family's rule excludes them. *)
Definition sim_Eq_statement : Prop :=
 (forall c cv g top e d r r', JitEmitRuleEq.Rule_Eq Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' ->
   JitEmitRuleEq.Rule_Eq_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e d r r' ->
   SimC c cv g top e d r r') /\
 (forall c cv g top e l r r', JitEmitRuleEq.RuleT_Eq Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' ->
   JitEmitRuleEq.RuleT_Eq_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e l r r' ->
   SimT c cv g top e l r r') /\
 (forall c cv g top e o top2 r r', JitEmitRuleEq.RuleO_Eq Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' ->
   JitEmitRuleEq.RuleO_Eq_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e o top2 r r' ->
   SimO c cv g top e o top2 r r').
(* sim_Store_statement: value/set and the vector primitives: gvals and heap cells through mu, absvector allocation extending mu. Does NOT say: anything about globals the source binds in another namespace (gfuns), or about the sealed table. *)
Definition sim_Store_statement : Prop :=
 (forall c cv g top e d r r', JitEmitRuleStore.Rule_Store Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' ->
   JitEmitRuleStore.Rule_Store_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e d r r' ->
   SimC c cv g top e d r r') /\
 (forall c cv g top e l r r', JitEmitRuleStore.RuleT_Store Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' ->
   JitEmitRuleStore.RuleT_Store_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e l r r' ->
   SimT c cv g top e l r r') /\
 (forall c cv g top e o top2 r r', JitEmitRuleStore.RuleO_Store Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' ->
   JitEmitRuleStore.RuleO_Store_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e o top2 r r' ->
   SimO c cv g top e o top2 r r').
(* sim_Prim_statement: the remaining primitives, IO included. Does NOT say: anything about an IO event ev_of does not translate (O'_io needs Some), or about a port primitive outside pmapx. *)
Definition sim_Prim_statement : Prop :=
 (forall c cv g top e d r r', JitEmitRulePrim.Rule_Prim Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' ->
   JitEmitRulePrim.Rule_Prim_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e d r r' ->
   SimC c cv g top e d r r') /\
 (forall c cv g top e l r r', JitEmitRulePrim.RuleT_Prim Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' ->
   JitEmitRulePrim.RuleT_Prim_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e l r r' ->
   SimT c cv g top e l r r') /\
 (forall c cv g top e o top2 r r', JitEmitRulePrim.RuleO_Prim Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' ->
   JitEmitRulePrim.RuleO_Prim_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e o top2 r r' ->
   SimO c cv g top e o top2 r r').
(* sim_DoFold_statement: do and folded constant lists. Does NOT say: anything when the store's do is not the kernel's (SMs.sm_do asks it). *)
Definition sim_DoFold_statement : Prop :=
 (forall c cv g top e d r r', JitEmitRuleDoFold.Rule_DoFold Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' ->
   JitEmitRuleDoFold.Rule_DoFold_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e d r r' ->
   SimC c cv g top e d r r') /\
 (forall c cv g top e l r r', JitEmitRuleDoFold.RuleT_DoFold Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' ->
   JitEmitRuleDoFold.RuleT_DoFold_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e l r r' ->
   SimT c cv g top e l r r') /\
 (forall c cv g top e o top2 r r', JitEmitRuleDoFold.RuleO_DoFold Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' ->
   JitEmitRuleDoFold.RuleO_DoFold_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e o top2 r r' ->
   SimO c cv g top e o top2 r r').
(* sim_Clo_statement: lambda and freeze closures, captures, nested code. Does NOT say: anything about a closure with an entry (CloOK excludes it). *)
Definition sim_Clo_statement : Prop :=
 (forall c cv g top e d r r', JitEmitRuleClo.Rule_Clo Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' ->
   JitEmitRuleClo.Rule_Clo_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e d r r' ->
   SimC c cv g top e d r r') /\
 (forall c cv g top e l r r', JitEmitRuleClo.RuleT_Clo Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' ->
   JitEmitRuleClo.RuleT_Clo_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e l r r' ->
   SimT c cv g top e l r r') /\
 (forall c cv g top e o top2 r r', JitEmitRuleClo.RuleO_Clo Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' ->
   JitEmitRuleClo.RuleO_Clo_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e o top2 r r' ->
   SimO c cv g top e o top2 r r').
(* sim_App_statement: dynamic application. Does NOT say: anything about over-application (no KApply frame is related) or partial application (VRh relates none). *)
Definition sim_App_statement : Prop :=
 (forall c cv g top e d r r', JitEmitRuleApp.Rule_App Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' ->
   JitEmitRuleApp.Rule_App_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e d r r' ->
   SimC c cv g top e d r r') /\
 (forall c cv g top e l r r', JitEmitRuleApp.RuleT_App Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' ->
   JitEmitRuleApp.RuleT_App_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e l r r' ->
   SimT c cv g top e l r r') /\
 (forall c cv g top e o top2 r r', JitEmitRuleApp.RuleO_App Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' ->
   JitEmitRuleApp.RuleO_App_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e o top2 r r' ->
   SimO c cv g top e o top2 r r').
(* sim_Trap_statement: trap-error. Does NOT say: what happens after a raise; that is O'_raise and the generic raising lemma, not this family's case. *)
Definition sim_Trap_statement : Prop :=
 (forall c cv g top e d r r', JitEmitRuleTrap.Rule_Trap Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' ->
   JitEmitRuleTrap.Rule_Trap_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e d r r' ->
   SimC c cv g top e d r r') /\
 (forall c cv g top e l r r', JitEmitRuleTrap.RuleT_Trap Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' ->
   JitEmitRuleTrap.RuleT_Trap_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e l r r' ->
   SimT c cv g top e l r r') /\
 (forall c cv g top e o top2 r r', JitEmitRuleTrap.RuleO_Trap Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' ->
   JitEmitRuleTrap.RuleO_Trap_All Comp SimC CompT SimT CompOp SimO CompOps SimS CompW SimW CompTA SimA c cv g top e o top2 r r' ->
   SimO c cv g top e o top2 r r').

(* The whole step: JitLowerStep.sim over MS'.
   Does NOT say: that the raise in O'_raise is resolved (preservation'_statement needs that). *)
Definition sim'_statement : Prop := forall mu c m, MS' mu c m -> Out' mu c m.

(* ---------- many steps ---------- *)
(* The bytecode machine m1 finishes as c does, after the source performs t: a related value, or an
   error c also throws, each with the final stores related. As in Ends, m1 is a parameter, so a
   theorem below names the machine that finishes (Ends'_final).
   Does NOT say: anything about cells outside mu' in the final stores, or which machine m2 is beyond
   its heap; the source's final store is related, not equal, to anything. *)
Inductive Ends' (mu : kmap) (c : config) (m1 : B.machine) (t : trace) : Prop :=
 | E'_ok v v' s' m2 mu' : Srun c t (Cfg (Ret v) [] s') -> B.next E pt m1 = B.MFinal (B.FReturn v') m2 ->
     mext mu mu' -> VRh mu' (B.m_heap m2) v v' -> SMs mu' s' m2 -> Ends' mu c m1 t
 | E'_err x l msg tv s' m2 mu' : Srun c t (Cfg (Throw x) [] s') -> B.next E pt m1 = B.MFinal (B.FError (B.VExn l)) m2 ->
     B.tget l (B.m_heap m2) = Some (B.OExn msg tv) -> exn_ok x msg -> mext mu mu' -> SMs mu' s' m2 -> Ends' mu c m1 t.

Lemma Ends'_final : forall mu c m1 t, Ends' mu c m1 t -> exists o m2, B.next E pt m1 = B.MFinal o m2.
Proof. intros mu c m1 t H; destruct H; eauto. Qed.

(* After n bytecode steps under any environment rs: still related (with the same IO trace on both
   sides), or the run has ended as the source's does, after the same trace.
   Does NOT say: that the source diverges when the bytecode does other than through MS' at every n
   (as preservation); anything about a run with an IO event ev_of does not translate (no source
   trace equals it); that the source does not take step_r_resource's exits. *)
Definition preservation'_statement : Prop := forall n mu c m (rs : nat -> B.jres), MS' mu c m ->
 (exists c' m' k tS tT mu', Srun c tS c' /\ TRun rs k m tT m' /\ (n <= k)%nat /\ map Some tS = tT /\
    mext mu mu' /\ MS' mu' c' m') \/
 (exists m1 k tS tT, Ends' mu c m1 tS /\ TRun rs k m tT m1 /\ map Some tS = tT).

(* The machine entering code c with these values in slots 2 up, nothing pending, no handler. *)
Definition entered' (mu : kmap) (m : B.machine) (c : B.code) (args : list value) : Prop :=
 code m = c /\ B.m_rest m = B.code_ins c /\ cs m = [] /\ hs m = [] /\
 ArgsAt' (V mu m) (st m) (fp m + 2) args.

(* Does NOT say: anything about a call with a handler already installed (entered' asks for none),
   or about the store's functions beyond FunRel' (each is accepted code, as in call_preservation). *)
Definition call_preservation'_statement : Prop := forall mu s m c ps b args n (rs : nat -> B.jres),
 SM mu s [] m -> CompFn' c ps b -> List.length ps = List.length args -> entered' mu m c args ->
 let c0 := Cfg (Eval (combine ps args) b) [] s in
 (exists c' m' k tS tT mu', Srun c0 tS c' /\ TRun rs k m tT m' /\ (n <= k)%nat /\ map Some tS = tT /\
    mext mu mu' /\ MS' mu' c' m') \/
 (exists m1 k tS tT, Ends' mu c0 m1 tS /\ TRun rs k m tT m1 /\ map Some tS = tT).

(* ---------- the front end composed ---------- *)
Section Src.
Variable D : list (name * fundef).

(* JitKRef.EndsSrc for any trace t and an evolving store: the source c0 (b0's run) ends after t,
   GVal/GStore-related under a world w extending the identity on s to the final value and store of
   the emitted body's run, which VRh/SMs relate to the machine.
   Does NOT say: that b0's final store equals the emitted body's; anything about cells outside w. *)
Inductive EndsSrc' (mu : kmap) (s : store) (c0 : config) (m1 : B.machine) (t : trace) : Prop :=
 | ES'_ok v0 v v' s0 s' w m2 mu' : Srun c0 t (Cfg (Ret v0) [] s0) ->
     JitKRef.JitKRef.wext (JitKRef.JitKRef.id_world s) w -> JitKRef.JitKRef.GVal w v0 v ->
     JitKRef.JitKRef.GStore w s0 s' ->
     B.next E pt m1 = B.MFinal (B.FReturn v') m2 -> mext mu mu' -> VRh mu' (B.m_heap m2) v v' ->
     SMs mu' s' m2 -> EndsSrc' mu s c0 m1 t
 | ES'_err x l msg tv s0 s' w m2 mu' : Srun c0 t (Cfg (Throw x) [] s0) ->
     JitKRef.JitKRef.wext (JitKRef.JitKRef.id_world s) w -> JitKRef.JitKRef.GStore w s0 s' ->
     B.next E pt m1 = B.MFinal (B.FError (B.VExn l)) m2 -> B.tget l (B.m_heap m2) = Some (B.OExn msg tv) ->
     exn_ok x msg -> mext mu mu' -> SMs mu' s' m2 -> EndsSrc' mu s c0 m1 t.

(* call_preservation' with the source body b0 where it had the emitted e, for any trace: JitKRef's
   premises (D_wf, the two KRef links, StoreHas, store_ok) added to call_preservation''s.
   Does NOT say: that b0 diverges when the bytecode does (KRef is partial correctness,
   OB-JIT-LOWER-TERM); anything about b0 against the kernel's source definitions of its callees
   (FunRel' binds the store's functions to accepted, i.e. lowered, code). *)
Definition call_preservation_src'_statement : Prop := forall mu s m c ps b0 b1 e args n (rs : nat -> B.jres),
 JitKRef.JitKRef.D_wf sealed D -> JitKRef.JitKRef.KRef sealed D ps b0 b1 -> JitKRef.JitKRef.KRef sealed D ps b1 e ->
 JitKRef.JitKRef.StoreHas D s -> store_ok s ->
 SM mu s [] m -> CompFn' c ps e -> List.length ps = List.length args -> entered' mu m c args ->
 let c0 := Cfg (Eval (combine ps args) b0) [] s in
 let ce := Cfg (Eval (combine ps args) e) [] s in
 (exists c' m' k tS tT mu', Srun ce tS c' /\ TRun rs k m tT m' /\ (n <= k)%nat /\ map Some tS = tT /\
    mext mu mu' /\ MS' mu' c' m') \/
 (exists m1 k tS tT, EndsSrc' mu s c0 m1 tS /\ TRun rs k m tT m1 /\ map Some tS = tT).

(* ---------- the old fragment ---------- *)
(* The new statements specialize to the old fragment: from the old invariant's states (MS; Com,
   JitLowerRel.CompFn and entered for a call) they conclude the new conclusion at mu = [], through
   ms_embed and sm_embed. Two hypotheses the old invariant does not carry, because the old fragment
   never reads them: the globals are related (GvalsRel [] s m) and the store has the kernel's do
   (DoOK s). preservation_old_of_new, call_preservation_old_of_new and
   call_preservation_src_old_of_new prove each from the new statement (closed).
   Does NOT say: that the new conclusion, on the old fragment, gives back the old one (MS at the
   end, a constant store, no IO); the old theorems stay proved on their own (JitLowerThm,
   JitKRefCompose). *)
Definition preservation_old_statement : Prop := forall n s c m (rs : nat -> B.jres),
 MS s c m -> GvalsRel [] s m -> DoOK s ->
 (exists c' m' k tS tT mu', Srun c tS c' /\ TRun rs k m tT m' /\ (n <= k)%nat /\ map Some tS = tT /\
    mext [] mu' /\ MS' mu' c' m') \/
 (exists m1 k tS tT, Ends' [] c m1 tS /\ TRun rs k m tT m1 /\ map Some tS = tT).

Definition call_preservation_old_statement : Prop := forall s m c ps b args n (rs : nat -> B.jres),
 Com s m -> JitLowerRel.CompFn c ps b -> List.length ps = List.length args -> entered m c args ->
 GvalsRel [] s m -> DoOK s ->
 let c0 := Cfg (Eval (combine ps args) b) [] s in
 (exists c' m' k tS tT mu', Srun c0 tS c' /\ TRun rs k m tT m' /\ (n <= k)%nat /\ map Some tS = tT /\
    mext [] mu' /\ MS' mu' c' m') \/
 (exists m1 k tS tT, Ends' [] c0 m1 tS /\ TRun rs k m tT m1 /\ map Some tS = tT).

Definition call_preservation_src_old_statement : Prop := forall s m c ps b0 b1 e args n (rs : nat -> B.jres),
 JitKRef.JitKRef.D_wf sealed D -> JitKRef.JitKRef.KRef sealed D ps b0 b1 -> JitKRef.JitKRef.KRef sealed D ps b1 e ->
 JitKRef.JitKRef.StoreHas D s -> store_ok s ->
 Com s m -> JitLowerRel.CompFn c ps e -> List.length ps = List.length args -> entered m c args ->
 GvalsRel [] s m -> DoOK s ->
 let c0 := Cfg (Eval (combine ps args) b0) [] s in
 let ce := Cfg (Eval (combine ps args) e) [] s in
 (exists c' m' k tS tT mu', Srun ce tS c' /\ TRun rs k m tT m' /\ (n <= k)%nat /\ map Some tS = tT /\
    mext [] mu' /\ MS' mu' c' m') \/
 (exists m1 k tS tT, EndsSrc' [] s c0 m1 tS /\ TRun rs k m tT m1 /\ map Some tS = tT).

Lemma entered_embed : forall s m c args, Com s m -> entered m c args -> entered' [] m c args.
Proof.
 intros s m c args [Hh _] (Hc & Hr & Hk & Aa). repeat split; auto. apply argsat_embed; exact Aa.
Qed.

Theorem preservation_old_of_new : preservation'_statement -> preservation_old_statement.
Proof. intros Pr n s c m rs H G Dk. apply Pr. eapply ms_embed; eauto. Qed.

Theorem call_preservation_old_of_new : call_preservation'_statement -> call_preservation_old_statement.
Proof.
 intros Cp s m c ps b args n rs Cm Cf L En G Dk c0. apply (Cp [] s m c ps b args n rs).
 - apply sm_embed; auto. constructor.
 - apply comp_embed_fn; exact Cf.
 - exact L.
 - eapply entered_embed; eauto.
Qed.

Theorem call_preservation_src_old_of_new : call_preservation_src'_statement -> call_preservation_src_old_statement.
Proof.
 intros Cp s m c ps b0 b1 e args n rs Dw K1 K2 Sh So Cm Cf L En G Dk c0 ce. apply (Cp [] s m c ps b0 b1 e args n rs); auto.
 - apply sm_embed; auto. constructor.
 - apply comp_embed_fn; exact Cf.
 - eapply entered_embed; eauto.
Qed.
End Src.
End Inv.
End JitEmitInv.
