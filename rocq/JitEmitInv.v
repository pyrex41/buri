(* Shen/JIT Phase 2, emit-spec: the generalized invariant of the back end, and the statements the
   emission families (emit-sim) and checkers (emit-check) must prove. Statements only, each a
   `Definition ... : Prop` with a "Does NOT say" note; NOTHING here is assumed or Admitted.
   Proved here (closed): VR_VRh, VRh_no_partial, HK_length, do_body_second, the embedding of the
   old invariant at any mu that relates the store's cells and globals (kont_embed, sm_embed,
   ms_embed), env_ok_inhabited, TRun_0, Out'_not_stuck, value_bound/value_unbound,
   SimC/T/O/S/W/A_of_sim', Ends'_final, EndsSrc'_final, the old-fragment bridges (srun_nil_sstar,
   trun_nil_tn, tn_tstar, ms_entered, entered_embed) and the three *_old_of_new corollaries.

   What the old invariant (JitLowerStep.MS, JitLowerThm) fixes, and what this one lets evolve:
   - mu, a partial bijection between KLambda heap locations (nat) and bytecode heap keys
     (positive), NoDup on both sides: vectors through mu, and a closure's identity cell (KLPort's
     closure_id, the cell every lambda and freeze allocates under jit_rules) to the key of its
     OClo object. A cell outside mu is one only one side made. mu grows (mext) along a run.
   - VRh mu h: JitLowerRel.VR, plus vectors through mu, lambda and freeze closures (code object
     nc with CloOK, captures related to the closure's environment, identity through mu), VExn to
     OExn (message as exn_ok asks), and streams by handle. It relates NO partial application.
   - SM mu s k m: gvals through VRh (an unbound global is unbound or VCleared in the machine),
     heap cells through mu, FunRel restated over JitEmitRel (FunRel'; a source function is not a
     value, see there), and the machine's handlers against the KTrap frames of k, in order, with
     their labels and quiet flags (HK; the code each handler runs is related by the KD'_trap frame
     of JitEmitKont). The kernel's do is asked by the do frames only (DoK := DoOK s).
   - the KLambda store evolves: MS' reads it from the configuration (mem c), where MS fixed it.
   - IO: both sides' traces, equal as lists of Observation events (target events through ev_of),
     under environments env_ok admits (well-formed answers, no IO failure; open in OB-JIT-LOWER-FRAGMENT).
   - Out' has a generic raising case O'_raise, and an IO case O'_io.
   Which primitives have a frame (JitEmitKont.frame_prim) is part of these statements: a frame for
   absvector, error-to-string, open, close, read-byte or write-byte, = without a constant operand,
   or a dynamic call of two or more arguments would make sim'_statement false (counterexamples
   there; open in OB-JIT-LOWER-FRAGMENT).

   New statement                          the old one it generalizes (proved)
   ------------------------------------   ---------------------------------------------------
   VRh                                    JitLowerRel.VR (VR_VRh)
   SMs / SM                               JitLowerStep.Com, which SM extends with the globals,
                                            mu's cells, handlers (sm_embed, given StoreRel)
   MS'                                    JitLowerStep.MS (ms_embed, given StoreRel)
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
   preservation_old_statement             JitLowerThm.preservation, verbatim conclusion, at
   call_preservation_old_statement          mu = [] with GvalsRel [] s m added. Each follows
   call_preservation_src_old_statement      (closed, *_old_of_new) from its new statement plus
                                            the reflection obligation below; the old theorems'
                                            proofs are not used. (JitKRef.call_preservation_src_
                                            statement for the src one.)
   old_reflect_statement,                 no old counterpart: the missing piece, MS'/Ends' at
   old_reflect_src_statement                mu = [] on an IO-free old-fragment run read back as
                                            MS/Ends/EndsSrc. Stated, NOT proved; truth UNKNOWN.
   The old fragment: no handler, no capture, no do frame, what MS, Com and JitLowerRel.CompFn
   describe; the embedding (ms_embed) holds at any mu StoreRel admits, the corollaries are at mu = []. *)
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
(* The function table: JitLowerStep.FunRel with JitEmitRel's CompFn'. It does not mention VRh,
   and needs not: a source function (FUser ps b in gfuns) is not a value, so there is nothing for
   VRh to relate it to; what relates it is the code (CompFn', at cv = [], so the closure's
   captures are never read). A function used as a value is a symbol (VRh_sym).
   Does NOT say: anything about the gfun closure's captures. *)
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

(* What the do frames use: the call of do returns its second argument. *)
Lemma do_body_second : forall s, DoOK s -> exists x y, lookup do_name (gfuns s) = Some (FUser [x; y] (EVar y)) /\
 forall a b : value, lookup y (combine [x; y] [a; b]) = Some b.
Proof.
 intros s (x & y & Nxy & L). exists x, y. split; [exact L|]. intros a b. cbn.
 destruct (text_eqb y x) eqn:E; [apply text_eqb_eq in E; congruence|]. rewrite text_eqb_refl. reflexivity.
Qed.

(* Globals: a bound one holds a related value; an unbound one is unbound or cleared. *)
Definition GvalsRel (mu : kmap) (s : store) (m : B.machine) : Prop :=
 (forall x v, lookup x (gvals s) = Some v -> exists v',
    B.tget (B.sym_of_text x) (B.m_gval m) = Some v' /\ v' <> B.VCleared /\ VRh mu (B.m_heap m) v v') /\
 (forall x, lookup x (gvals s) = None -> forall v', B.tget (B.sym_of_text x) (B.m_gval m) = Some v' -> v' = B.VCleared).

(* Heap cells through mu: a vector's cells related, or a closure's identity cell. *)
Definition HeapRel (mu : kmap) (s : store) (m : B.machine) : Prop :=
 forall l p, In (l, p) mu ->
   (exists cells cells', nth_error (heap s) l = Some cells /\ B.tget p (B.m_heap m) = Some (B.OVec cells') /\
      Forall2 (VRh mu (B.m_heap m)) cells cells') \/
   (nth_error (heap s) l = Some [] /\ exists nc caps, B.tget p (B.m_heap m) = Some (B.OClo nc caps)).

(* Store against machine, without the continuation.
   Does NOT say: anything about cells outside mu, gfun entries of names the store does not
   define beyond fr'_none, the sealed table, or the allocation counter. The kernel's do is not
   here: the do frames ask it (JitEmitKont's DoK, instantiated with DoOK of the current store). *)
Record SMs (mu : kmap) (s : store) (m : B.machine) : Prop := {
 sm_bij : pbij mu;
 sm_heap : HeapRel mu s m;
 sm_gvals : GvalsRel mu s m;
 sm_fun : FunRel' s m }.

(* The source's KTrap frames, innermost first. *)
Fixpoint trap_frames (k : list frame) : list (expr * lenv) := match k with
 | [] => [] | KTrap h rho :: k => (h, rho) :: trap_frames k | _ :: k => trap_frames k end.
(* One handler per KTrap frame, in order, each with its label in its code and its quiet flag
   read off that code (JitBytecode's push-handler). What the handler's code at that label does,
   its frame pointer and its saved continuations are related by the KD'_trap frame that consumes
   it (JitEmitKont): that needs the frame's environment, variables and code derivations, which a
   store-level relation does not have.
   Does NOT say: which KTrap frame's code a handler runs (KD'_trap says it). *)
Definition HK (hs : list B.handler) (k : list frame) : Prop :=
 Forall2 (fun hd _ => exists r, B.find_label (B.h_label hd) (B.code_ins (B.h_code hd)) = Some r /\
   B.h_quiet hd = quiet_of r) hs (trap_frames k).

Lemma HK_length : forall hs k, HK hs k -> List.length hs = List.length (trap_frames k).
Proof. intros hs k H; exact (Forall2_length H). Qed.

Definition SM (mu : kmap) (s : store) (k : list frame) (m : B.machine) : Prop :=
 SMs mu s m /\ HK (B.m_handlers m) k.

Notation fp m := (B.m_fp m).
Notation st m := (B.m_stack m).
Notation code m := (B.m_code m).
Notation cs m := (B.m_conts m).
Notation hs m := (B.m_handlers m).
Notation V mu m := (VRh mu (B.m_heap m)).
Notation HC m := (HeapClo (B.m_heap m)).
Notation DK s := (DoOK s).

(* What a code position needs besides its own derivation: the store, the environment (slots and
   captures), the writable addresses (never the closure in slot 1 of a code that captures), and the
   continuation. *)
Definition EvalCtx (mu : kmap) (cv : list name) (caps : list B.val) (g : env) (top : N) (dst : dest)
    (r2 : list B.instr) (rho : lenv) (k : list frame) (s : store) (w : N -> Prop) (m : B.machine) : Prop :=
 SM mu s k m /\ MEnv' (V mu m) (fp m) (st m) cv caps g rho /\ EnvBelow g top /\ Above (fp m) top w /\
 CCtx (HC m) (code m) cv caps (fp m) (st m) /\ (cv = [] \/ ~ w (fp m + 1)) /\
 KC' (V mu m) (HC m) (DK s) (code m) cv caps (fp m) (st m) (cs m) (hs m) w dst r2 k.
Definition TestCtx (mu : kmap) (cv : list name) (caps : list B.val) (g : env) (top : N) (l : N)
    (r2 : list B.instr) (rho : lenv) (k : list frame) (s : store) (w : N -> Prop) (m : B.machine) : Prop :=
 SM mu s k m /\ MEnv' (V mu m) (fp m) (st m) cv caps g rho /\ EnvBelow g top /\ Above (fp m) top w /\
 CCtx (HC m) (code m) cv caps (fp m) (st m) /\ (cv = [] \/ ~ w (fp m + 1)) /\
 TK' (V mu m) (HC m) (DK s) (code m) cv caps (fp m) (st m) (cs m) (hs m) w true l r2 k.
Definition OpCtx (mu : kmap) (cv : list name) (caps : list B.val) (g : env) (top : N) (o : B.operand)
    (r2 : list B.instr) (rho : lenv) (k : list frame) (s : store) (w : N -> Prop) (m : B.machine) : Prop :=
 SM mu s k m /\ MEnv' (V mu m) (fp m) (st m) cv caps g rho /\ EnvBelow g top /\ Above (fp m) top w /\
 CCtx (HC m) (code m) cv caps (fp m) (st m) /\ (cv = [] \/ ~ w (fp m + 1)) /\
 KD' (V mu m) (HC m) (DK s) (code m) cv caps (fp m) (st m) (cs m) (hs m) w o r2 k.

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
     KD' (V mu m) (HC m) (DK s) (code m) cv caps (fp m) (st m) (cs m) (hs m) w o (B.m_rest m) k ->
     MS' mu (Cfg (Ret v) k s) m.


(* ---------- the old invariant embeds (any mu, no handler, no capture, no do frame) ---------- *)
Lemma menv_embed : forall mu h fp st g rho, MEnv fp st g rho -> MEnv' (VRh mu h) fp st [] [] g rho.
Proof.
 intros mu h fp st g rho M. split.
 - intros x s L. destruct (M x s L) as (v & v' & A & B0 & C). exists v, v'. repeat split; auto. apply VR_VRh; auto.
 - intros i x N. destruct i; discriminate.
Qed.
Lemma doner_embed : forall mu h c fp st vals dops, DoneR c fp st vals dops -> DoneR' (VRh mu h) c fp st vals dops.
Proof. intros mu h c fp st vals dops H; induction H; econstructor; eauto using VR_VRh. Qed.
Lemma argsat_embed : forall mu h st a vals, ArgsAt st a vals -> ArgsAt' (VRh mu h) st a vals.
Proof. intros mu h st a vals H; induction H; econstructor; eauto using VR_VRh. Qed.
Lemma paramat_embed : forall mu h fp st ms i vals, ParamAt fp st ms i vals -> ParamAt' (VRh mu h) fp st ms i vals.
Proof. intros mu h fp st ms i vals H; induction H; econstructor; eauto using VR_VRh. Qed.
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
Lemma fp_embed : forall c p q ops, pmap p = Some q -> pguard c q ops = true -> frame_prim c q ops = true.
Proof. intros c p q ops H G. rewrite (frame_prim_pmap c p q ops H). exact G. Qed.
Create HintDb emb.
Local Hint Resolve menv_embed doner_embed argsat_embed paramat_embed ce_C ce_T ce_S ce_W ce_A pmapx_pmap fp_embed : emb.

(* JitLowerKont's frames are JitEmitKont's, with no capture and no handler, under VRh mu h for any
   mu, and any DoK (no old frame is a do frame). *)
Theorem kont_embed : forall mu h (HC : positive -> B.code -> list B.val -> Prop) (DK : Prop),
 (forall c fp st cs w o r k, KD c fp st cs w o r k -> KD' (VRh mu h) HC DK c [] [] fp st cs [] w o r k) /\
 (forall c fp st cs w gd l r k, TK c fp st cs w gd l r k -> TK' (VRh mu h) HC DK c [] [] fp st cs [] w gd l r k) /\
 (forall c fp st cs w dst r k, KC c fp st cs w dst r k -> KC' (VRh mu h) HC DK c [] [] fp st cs [] w dst r k) /\
 (forall fp st cs k, RK fp st cs k -> RK' (VRh mu h) HC DK fp st cs [] k).
Proof.
 intros mu h HC DK. apply K_mut; intros;
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

(* The part of SMs the old invariant does not carry, because the old fragment never reads it:
   the cells mu tracks, and the globals. *)
Definition StoreRel (mu : kmap) (s : store) (m : B.machine) : Prop :=
 pbij mu /\ HeapRel mu s m /\ GvalsRel mu s m.

Lemma storerel_nil : forall s m, GvalsRel [] s m -> StoreRel [] s m.
Proof. intros s m G. split; [exact pbij_nil|split; [intros l p I; destruct I|exact G]]. Qed.

Lemma sm_embed : forall mu s k m, Com s m -> notrap k -> StoreRel mu s m -> SM mu s k m.
Proof.
 intros mu s k m [Hh Fr] Nt (Pb & Hr & G). split.
 - constructor; auto. apply funrel_embed; auto.
 - unfold HK. rewrite Hh, (notrap_frames k Nt). constructor.
Qed.

(* JitLowerStep's MS is MS' at any mu that relates the store's cells and globals (StoreRel). *)
Theorem ms_embed : forall mu s c m, MS s c m -> StoreRel mu s m -> MS' mu c m.
Proof.
 intros mu s c m H G. destruct H as [g top e dst r2 rho k w m Cm Cc Me Eb Ab Kc|g top e l r2 rho k w m Cm Ct Me Eb Ab Tk
   |g top e o top2 r2 rho k w m Cm Co Me Eb Ab Kd|v v' o k w m Cm Ro Vr Kd];
   pose proof Cm as [Hh _];
   destruct (kont_embed mu (B.m_heap m) (HeapClo (B.m_heap m)) (DoOK s)) as (EKD & ETK & EKC & ERK).
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
   Does NOT say: anything about runs whose IO this does not translate. JReadFile and JWrites (no
   single source request) are None, so a trace containing one equals no source trace; no frame or
   rule at emit-spec emits either. open's path is the bytecode's, which prefixes
   *home-directory*: it equals the source's only when that is empty (open has no frame,
   JitEmitKont.frame_prim). The clock answers binary64 bits b, which jit_profile's time_value
   reads from RTime as the same bits, for b below 2^64. A failure the bytecode reports without a
   cause is the source's RFailed (EOther 0). *)
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
 | B.JTime run, B.JTimeIs b =>
   if (b <? 18446744073709551616)%N
   then Some (EvIO (QTime (of_string (if run then "run"%string else "unix"%string))) (RTime (Z.of_N b)))
   else None
 | _, _ => None end.

(* The environments considered: each request answered with a response of its kind that the
   binary's runtime can give, and no failure. A clock reading is 64 bits; a byte is below 256.
   Does NOT say: anything about an environment that reports an IO failure, or answers with a
   response of another kind. For those JitBytecode's continuation either resumes the machine
   where it was (a failed request with no handler: `raise` gives a final, which a continuation
   jres -> machine cannot return), or leaves it at a handler while the source throws; neither is
   related by MS' (open in OB-JIT-LOWER-FRAGMENT). Every request has a response here (env_ok_inhabited). *)
Definition resp_ok (q : B.jreq) (r : B.jres) : Prop := match q, r with
 | B.JOpen _ _, B.JOpened _ => True
 | B.JClose _, B.JDone => True
 | B.JRead _, B.JByte b => (b < 256)%N
 | B.JRead _, B.JEof => True
 | B.JWrite _ _, B.JDone => True
 | B.JTime _, B.JTimeIs b => (b < 18446744073709551616)%N
 | B.JReadFile _, B.JFile _ => True
 | B.JWrites _ _, B.JDone => True
 | _, _ => False end.
Definition env_ok (rs : nat -> B.jreq -> B.jres) : Prop := forall i q, resp_ok q (rs i q).

(* Every clock answer resp_ok admits is translated, so a get-time frame meets O'_io's ev_of. *)
Lemma ev_of_time : forall run r, resp_ok (B.JTime run) r -> exists e, ev_of (B.JTime run) r = Some e.
Proof.
 intros run r H. destruct r; cbn in H |- *; try contradiction.
 all: apply N.ltb_lt in H; rewrite H; eauto.
Qed.

Lemma env_ok_inhabited : exists rs, env_ok rs.
Proof.
 exists (fun _ q => match q with
   | B.JOpen _ _ => B.JOpened 0 | B.JClose _ => B.JDone | B.JRead _ => B.JEof | B.JWrite _ _ => B.JDone
   | B.JTime _ => B.JTimeIs 0 | B.JReadFile _ => B.JFile [] | B.JWrites _ _ => B.JDone end).
 intros i q. destruct q; cbn; auto. reflexivity.
Qed.

(* Exactly n bytecode steps, the environment answering the i-th IO request q with rs i q: the run
   is the machine's only one under that environment. Quantifying over rs covers every
   environment. *)
Inductive TRun : (nat -> B.jreq -> B.jres) -> nat -> B.machine -> list (option event) -> B.machine -> Prop :=
 | TR_0 rs m : TRun rs 0 m [] m
 | TR_tau rs n m m1 t m2 : B.next E pt m = B.MTau m1 -> TRun rs n m1 t m2 -> TRun rs (S n) m t m2
 | TR_io rs n m q kk t m2 : B.next E pt m = B.MIO q kk ->
     TRun (fun i => rs (S i)) n (kk (rs O q)) t m2 -> TRun rs (S n) m (ev_of q (rs O q) :: t) m2.

Lemma TRun_0 : forall rs m t m', TRun rs 0 m t m' -> t = [] /\ m' = m.
Proof. intros rs m t m' H. inversion H; auto. Qed.

(* ---------- one step ---------- *)
(* The bytecode makes progress (or the source's measure falls), keeping MS'; or performs IO, which
   the source matches with the same event under every response resp_ok admits; or both finish; or the bytecode
   raises where the source throws, with the continuations related (O'_raise: what happens next,
   a handler or the end, is the generic raising lemma's business, not each family's).
   Does NOT say: that the source does not take the resource exits step_r_resource permits; anything
   about an IO response resp_ok excludes. *)
Inductive Out' (mu : kmap) (c : config) (m : B.machine) : Prop :=
 | O'_step c' m' mu' : Sstar c c' -> (TPlus m m' \/ (m' = m /\ (msr c' < msr c)%nat)) ->
     mext mu mu' -> MS' mu' c' m' -> Out' mu c m
 | O'_io m1 q kk : TStar m m1 -> B.next E pt m1 = B.MIO q kk ->
     (forall r, resp_ok q r -> exists c' e mu', ev_of q r = Some e /\ Srun c [e] c' /\ mext mu mu' /\ MS' mu' c' (kk r)) ->
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
     ((exists o r, KD' (V mu' m2) (HC m2) (DK s') (code m2) cv caps (fp m2) (st m2) (cs m2) (hs m2) w o r k) \/
      (exists l r, TK' (V mu' m2) (HC m2) (DK s') (code m2) cv caps (fp m2) (st m2) (cs m2) (hs m2) w true l r k) \/
      (exists dst r, KC' (V mu' m2) (HC m2) (DK s') (code m2) cv caps (fp m2) (st m2) (cs m2) (hs m2) w dst r k)) ->
     Out' mu c m.

(* An outcome never leaves the machine stuck: it steps, asks for IO, finishes, or raises to a
   handler whose label is in its code (SM's HK), unless the source's measure falls instead. *)
Lemma Out'_not_stuck : forall mu c m, Out' mu c m ->
 (exists c' mu', Sstar c c' /\ (msr c' < msr c)%nat /\ MS' mu' c' m) \/
 (exists m1, TStar m m1 /\ forall w, B.next E pt m1 <> B.MStuck w).
Proof.
 intros mu c m H. destruct H as [c' m' mu' Ss [(m1 & T1 & _)|(-> & Lt)] Mx Ms|m1 q kk Ts N _|v v' s' m1 m2 mu' _ Ts N _ _ _
   |x l msg tv s' m1 m2 mu' _ Ts N _ _ _ _|x k s' m1 m2 msg tv mu' cv caps w _ Ts N _ _ (_ & Hk) _ _].
 - right. exists m. split; [constructor|]. unfold TS in T1. rewrite T1. discriminate.
 - left. exists c', mu'. auto.
 - right. exists m1. split; auto. rewrite N. discriminate.
 - right. exists m1. split; auto. rewrite N. discriminate.
 - right. exists m1. split; auto. rewrite N. discriminate.
 - right. exists m1. split; auto. rewrite N. unfold B.raise. unfold HK in Hk.
   destruct (B.m_handlers m2) as [|h hs0] eqn:Eh.
   + destruct (B.alloc m2 (B.OExn msg tv)). discriminate.
   + inversion Hk as [|h0 f0 hs1 fs1 (r & Fr & Qr) _ E1 E2]; subst.
     rewrite Fr. destruct (B.h_quiet h); [discriminate|]. destruct (B.alloc m2 (B.OExn msg tv)). discriminate.
Qed.

(* What the globals give the value primitive: a bound global's machine value is related and not
   cleared, so value returns it; an unbound one raises on both sides. *)
Lemma value_bound : forall mu s m d x v, GvalsRel mu s m -> lookup x (gvals s) = Some v -> exists v',
 B.prim_step E pt m d B.PValue [B.VSym (B.sym_of_text x)] = B.ret_to m d v' /\ VRh mu (B.m_heap m) v v'.
Proof.
 intros mu s m d x v [G1 _] L. destruct (G1 x v L) as (v' & T & Nc & Vr). exists v'. split; [|exact Vr].
 cbn. rewrite T. destruct v'; try reflexivity. contradiction.
Qed.
Lemma value_unbound : forall mu s m d x, GvalsRel mu s m -> lookup x (gvals s) = None -> exists msg tv,
 B.prim_step E pt m d B.PValue [B.VSym (B.sym_of_text x)] = B.raise m msg tv.
Proof.
 intros mu s m d x [_ G2] L. cbn. destruct (B.tget (B.sym_of_text x) (B.m_gval m)) as [v'|] eqn:T.
 - rewrite (G2 x L v' T). eexists _, _; reflexivity.
 - eexists _, _; reflexivity.
Qed.

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
(* sim_Eq_statement: =, needing the = budget (OB-JIT-EQ-BUDGET-CORE) and mu for vectors and closure identities. Does NOT say: anything about = without a constant operand pguard admits: its pending-argument frame keeps pguard (JitEmitKont.frame_prim), since two NaNs or a cycle leave the bytecode stuck (OB-JIT-NAN-IDENTITY, OB-JIT-EQ-CYCLE); = on two variables needs a frame from emit-spec. *)
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
(* sim_Store_statement: value/set and the vector primitives <-address, address-> and absvector?: gvals and heap cells through mu. Does NOT say: anything about absvector, which has no frame (JitEmitKont.frame_prim: a counterexample at length 2^48), about globals the source binds in another namespace (gfuns), or about the sealed table. *)
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
(* sim_Prim_statement: the remaining primitives frame_prim admits; of IO, get-time only. Does NOT say: anything about open, close, read-byte, write-byte or error-to-string, which have no frame (counterexamples at JitEmitKont.frame_prim), about an IO response resp_ok excludes, or about a port primitive outside pmapx. *)
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
(* sim_DoFold_statement: do and folded constant lists. Does NOT say: anything when the store's do is not the kernel's (the do frames ask DoOK of the current store). *)
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
(* sim_App_statement: dynamic application of at most one argument (the window frames' bound). Does NOT say: anything about over-application (no KApply frame is related, and a window of two or more arguments has no frame) or partial application (VRh relates none). *)
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

(* The per-judgement IH is what sim' gives at an evaluation state: SimC/SimT/SimO hold of every
   derivation, and SimS/SimW/SimA along every list derivation. *)
Lemma SimC_of_sim' : sim'_statement -> forall c cv g top e dst r r2, Comp c cv g top e dst r r2 -> SimC c cv g top e dst r r2.
Proof.
 intros Hs c cv g top e dst r r2 H mu caps rho k s w m Hc Hr X. apply Hs.
 eapply MS'_eval; [rewrite Hc, Hr; exact H|exact X].
Qed.
Lemma SimT_of_sim' : sim'_statement -> forall c cv g top e l r r2, CompT c cv g top e l r r2 -> SimT c cv g top e l r r2.
Proof.
 intros Hs c cv g top e l r r2 H mu caps rho k s w m Hc Hr X. apply Hs.
 eapply MS'_test; [rewrite Hc, Hr; exact H|exact X].
Qed.
Lemma SimO_of_sim' : sim'_statement -> forall c cv g top e o top2 r r2, CompOp c cv g top e o top2 r r2 ->
 SimO c cv g top e o top2 r r2.
Proof.
 intros Hs c cv g top e o top2 r r2 H mu caps rho k s w m Hc Hr X. apply Hs.
 eapply MS'_op; [rewrite Hc, Hr; exact H|exact X].
Qed.
Lemma SimS_of_sim' : sim'_statement -> forall c cv g top es os r r2, CompOps c cv g top es os r r2 -> SimS c cv g top es os r r2.
Proof.
 intros Hs. fix IH 9. intros c cv g top es os r r2 H. destruct H as [|c cv g top e es o os top2 r r1 r' H0 H1].
 - constructor.
 - eapply SS_cons; [eapply SimO_of_sim'; eauto|exact (IH _ _ _ _ _ _ _ _ H1)].
Qed.
Lemma SimW_of_sim' : sim'_statement -> forall c cv g s es r r2, CompW c cv g s es r r2 -> SimW c cv g s es r r2.
Proof.
 intros Hs. fix IH 8. intros c cv g s es r r2 H. destruct H as [|c cv g s e es r r1 r' H0 H1].
 - constructor.
 - eapply SW_cons; [eapply SimC_of_sim'; eauto|exact (IH _ _ _ _ _ _ _ H1)].
Qed.
Lemma SimA_of_sim' : sim'_statement -> forall c cv g s t es ms r r2, CompTA c cv g s t es ms r r2 -> SimA c cv g s t es ms r r2.
Proof.
 intros Hs. fix IH 10. intros c cv g s t es ms r r2 H.
 destruct H as [c cv g s t ms r'|c cv g s t x es ms r r' L H1|c cv g s t e es ms r r1 r' H0 H1|c cv g s t e es ms r r1 r' H0 H1].
 - constructor.
 - eapply SA_same; [exact L|exact (IH _ _ _ _ _ _ _ _ _ H1)].
 - eapply SA_temp; [eapply SimC_of_sim'; eauto|exact (IH _ _ _ _ _ _ _ _ _ H1)].
 - eapply SA_direct; [eapply SimC_of_sim'; eauto|exact (IH _ _ _ _ _ _ _ _ _ H1)].
Qed.

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
   (as preservation); anything about an environment env_ok excludes (an IO failure, a response
   of another kind; open in OB-JIT-LOWER-FRAGMENT) or a run with an IO event ev_of does not translate (no
   source trace equals it); that the source does not take step_r_resource's exits. *)
Definition preservation'_statement : Prop := forall n mu c m (rs : nat -> B.jreq -> B.jres), env_ok rs -> MS' mu c m ->
 (exists c' m' k tS tT mu', Srun c tS c' /\ TRun rs k m tT m' /\ (n <= k)%nat /\ map Some tS = tT /\
    mext mu mu' /\ MS' mu' c' m') \/
 (exists m1 k tS tT, Ends' mu c m1 tS /\ TRun rs k m tT m1 /\ map Some tS = tT).

(* The machine entering code c with these values in slots 2 up, nothing pending, no handler. *)
Definition entered' (mu : kmap) (m : B.machine) (c : B.code) (args : list value) : Prop :=
 code m = c /\ B.m_rest m = B.code_ins c /\ cs m = [] /\ hs m = [] /\
 ArgsAt' (V mu m) (st m) (fp m + 2) args.

(* Does NOT say: anything about a call with a handler already installed (entered' asks for none),
   or about the store's functions beyond FunRel' (each is accepted code, as in call_preservation);
   anything about an environment env_ok excludes. *)
Definition call_preservation'_statement : Prop := forall mu s m c ps b args n (rs : nat -> B.jreq -> B.jres),
 env_ok rs -> SM mu s [] m -> CompFn' c ps b -> List.length ps = List.length args -> entered' mu m c args ->
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

(* As Ends', EndsSrc' names the machine that finishes. *)
Lemma EndsSrc'_final : forall mu s c0 m1 t, EndsSrc' mu s c0 m1 t -> exists o m2, B.next E pt m1 = B.MFinal o m2.
Proof. intros mu s c0 m1 t H; destruct H; eauto. Qed.

(* call_preservation' with the source body b0 where it had the emitted e, for any trace: JitKRef's
   premises (D_wf, the two KRef links, StoreHas, store_ok) added to call_preservation''s.
   Does NOT say: that b0 diverges when the bytecode does (KRef is partial correctness,
   OB-JIT-LOWER-TERM); anything about b0 against the kernel's source definitions of its callees
   (FunRel' binds the store's functions to accepted, i.e. lowered, code); anything about an
   environment env_ok excludes. *)
Definition call_preservation_src'_statement : Prop := forall mu s m c ps b0 b1 e args n (rs : nat -> B.jreq -> B.jres),
 env_ok rs -> JitKRef.JitKRef.D_wf sealed D -> JitKRef.JitKRef.KRef sealed D ps b0 b1 -> JitKRef.JitKRef.KRef sealed D ps b1 e ->
 JitKRef.JitKRef.StoreHas D s -> store_ok s ->
 SM mu s [] m -> CompFn' c ps e -> List.length ps = List.length args -> entered' mu m c args ->
 let c0 := Cfg (Eval (combine ps args) b0) [] s in
 let ce := Cfg (Eval (combine ps args) e) [] s in
 (exists c' m' k tS tT mu', Srun ce tS c' /\ TRun rs k m tT m' /\ (n <= k)%nat /\ map Some tS = tT /\
    mext mu mu' /\ MS' mu' c' m') \/
 (exists m1 k tS tT, EndsSrc' mu s c0 m1 tS /\ TRun rs k m tT m1 /\ map Some tS = tT).

(* ---------- the old fragment ---------- *)
(* The old theorems, restated at the old fragment as corollaries of the new statements: empty mu,
   no handler (Com), the store constant, and the OLD conclusions verbatim (Sstar, TN, MS s, and
   JitLowerThm.Ends / JitKRef.EndsSrc with the store s). Each *_old_statement takes the old
   theorem's premises plus GvalsRel [] s m, and *_old_of_new proves it (closed) from its new
   statement and one reflection obligation (old_reflect_statement, old_reflect_src_statement),
   through ms_embed/sm_embed at mu = [] and the bridges below, never through JitLowerThm's or
   JitKRefCompose's proofs.
   GvalsRel [] s m is needed: MS and Com leave the machine's globals unconstrained, and on a state
   whose globals are unrelated to the store's the new invariant says nothing (the value primitive
   would read them). At mu = [] it asks every bound global to hold a value VR relates (no vector,
   closure, exception or stream).
   The reflection is the missing piece. The new conclusions forget what the old ones keep: MS'
   picks SOME JitEmitRel derivation, SOME mu' extending [] and SOME trace, and nothing in the new
   statements keeps a run that starts in the old fragment inside it (the conclusion's derivation
   may come from a family rule, values may be related through mu'). So the old conclusion does not
   follow from the new statements alone, and the reflection is stated, not proved. Reflecting
   JitEmitRel derivations would invert the Rule_X outside their own files, which the design
   forbids; a family whose rule overlaps the old fragment (Eq's = beside C_prim with pguard) is
   where the reflection is at risk, and whether such a family must re-prove it, beside its map and
   all lemmas, is a review decision (OB-JIT-LOWER-FRAGMENT). *)

(* An IO-free source run is a silent one. *)
Lemma srun_nil_sstar : forall c c', Srun c [] c' -> Sstar c c'.
Proof.
 intros c c' H. unfold Srun in H. remember (@nil event) as t eqn:Et.
 induction H as [c0|c0 l c1 t c2 St Hs IH]; [constructor|].
 destruct l as [|ev]; cbn in Et; [|discriminate]. econstructor; [exact St|auto].
Qed.

(* A bytecode run with no IO event is a run of silent steps. *)
Lemma trun_nil_tn : forall rs k m m', TRun rs k m [] m' -> JitLowerThm.TN E pt k m m'.
Proof.
 intros rs k m m' H. remember (@nil (option event)) as t eqn:Et.
 induction H as [rs m|rs n m m1 t m2 N H IH|rs n m q kk t m2 N H IH]; [constructor| |discriminate].
 econstructor; [exact N|auto].
Qed.

Lemma tn_tstar : forall k m m', JitLowerThm.TN E pt k m m' -> TStar m m'.
Proof. intros k m m' H; induction H; [constructor|econstructor; eauto]. Qed.

(* The configuration a call enters is related by MS (JitLowerThm.call_preservation's first step,
   restated here: a state, not the theorem's conclusion). *)
Lemma ms_entered : forall s m c ps b args, Com s m -> JitLowerRel.CompFn c ps b -> List.length ps = List.length args ->
 entered m c args -> MS s (Cfg (Eval (combine ps args) b) [] s) m.
Proof.
 intros s m c ps b args Cm [r' Cf] L [Hc [Hr [Hk Aa]]].
 eapply MS_eval with (g := bind ps 2) (top := (2 + N.of_nat (List.length ps))%N) (dst := DRet) (r2 := r')
   (w := fun a => (B.m_fp m + (2 + N.of_nat (List.length ps)) <= a)%N).
 - exact Cm.
 - rewrite Hc, Hr. exact Cf.
 - apply MEnv_bind; [exact L|exact Aa].
 - apply bind_below.
 - intros a A; exact A.
 - rewrite Hk. apply KC_ret; [intros a A; lia|constructor].
Qed.

Lemma entered_embed : forall mu s m c args, Com s m -> entered m c args -> entered' mu m c args.
Proof.
 intros mu s m c args [Hh _] (Hc & Hr & Hk & Aa). repeat split; auto. apply argsat_embed; exact Aa.
Qed.

(* The reflection obligation (NOT proved; its truth is UNKNOWN). From a state MS relates, with
   globals VR relates, an IO-free bytecode run under an environment env_ok admits: a related
   state the new invariant reaches is MS-related with the same store and after no source IO, and
   an end the new invariant reaches is JitLowerThm.Ends with the same store.
   Does NOT say: anything about a state outside the old fragment, or a run with IO; that MS' and
   MS relate the same pairs in general (a family rule can relate old syntax to code JitLowerRel
   does not, and mu' can relate values VR does not); that it survives a family rule overlapping
   the old fragment without that family re-proving it. *)
Definition old_reflect_statement : Prop := forall s c m (rs : nat -> B.jreq -> B.jres) k tS tT m1,
 env_ok rs -> MS s c m -> GvalsRel [] s m -> TRun rs k m tT m1 -> map Some tS = tT ->
 (forall c' mu', Srun c tS c' -> mext [] mu' -> MS' mu' c' m1 -> tS = [] /\ MS s c' m1) /\
 (Ends' [] c m1 tS -> tS = [] /\ JitLowerThm.Ends E pt sealed s c m1).

(* The same for the composed front end's end: EndsSrc' at mu = [] read back as JitKRef.EndsSrc
   (the emitted body's final store s, the value VR-related). NOT proved; truth UNKNOWN.
   Does NOT say: anything when the emitted body e is outside the old fragment; anything about b0
   beyond what EndsSrc' gives (KRef's GVal/GStore at a world extending the identity on s). *)
Definition old_reflect_src_statement : Prop := forall s m c ps b0 b1 e args (rs : nat -> B.jreq -> B.jres) k tS tT m1,
 env_ok rs -> JitKRef.JitKRef.D_wf sealed D -> JitKRef.JitKRef.KRef sealed D ps b0 b1 -> JitKRef.JitKRef.KRef sealed D ps b1 e ->
 JitKRef.JitKRef.StoreHas D s -> store_ok s ->
 Com s m -> JitLowerRel.CompFn c ps e -> List.length ps = List.length args -> entered m c args -> GvalsRel [] s m ->
 TRun rs k m tT m1 -> map Some tS = tT ->
 EndsSrc' [] s (Cfg (Eval (combine ps args) b0) [] s) m1 tS ->
 tS = [] /\ JitKRef.JitKRef.EndsSrc sealed E pt s (Cfg (Eval (combine ps args) b0) [] s) m1.

(* JitLowerThm.preservation at the old fragment, with GvalsRel [] s m added.
   Does NOT say: anything at a state whose globals VR does not relate (the old theorem does). *)
Definition preservation_old_statement : Prop := forall n s c m, MS s c m -> GvalsRel [] s m ->
 (exists c' m' k, Sstar c c' /\ JitLowerThm.TN E pt k m m' /\ (n <= k)%nat /\ MS s c' m') \/
 (exists m1, JitLowerThm.Ends E pt sealed s c m1 /\ TStar m m1).

(* JitLowerThm.call_preservation at the old fragment, with GvalsRel [] s m added.
   Does NOT say: anything at a state whose globals VR does not relate. *)
Definition call_preservation_old_statement : Prop := forall s m c ps b args n,
 Com s m -> JitLowerRel.CompFn c ps b -> List.length ps = List.length args -> entered m c args -> GvalsRel [] s m ->
 let c0 := Cfg (Eval (combine ps args) b) [] s in
 (exists c' m' k, Sstar c0 c' /\ JitLowerThm.TN E pt k m m' /\ (n <= k)%nat /\ MS s c' m') \/
 (exists m1, JitLowerThm.Ends E pt sealed s c0 m1 /\ TStar m m1).

(* JitKRef.call_preservation_src_statement at the old fragment, with GvalsRel [] s m added.
   Does NOT say: anything at a state whose globals VR does not relate; anything more about b0
   than the old statement (its Does NOT say carries over). *)
Definition call_preservation_src_old_statement : Prop := forall s m c ps b0 b1 e args n,
 JitKRef.JitKRef.D_wf sealed D -> JitKRef.JitKRef.KRef sealed D ps b0 b1 -> JitKRef.JitKRef.KRef sealed D ps b1 e ->
 JitKRef.JitKRef.StoreHas D s -> store_ok s ->
 Com s m -> JitLowerRel.CompFn c ps e -> List.length ps = List.length args -> entered m c args -> GvalsRel [] s m ->
 let c0 := Cfg (Eval (combine ps args) b0) [] s in
 let ce := Cfg (Eval (combine ps args) e) [] s in
 (exists c' m' k, Sstar ce c' /\ JitLowerThm.TN E pt k m m' /\ (n <= k)%nat /\ MS s c' m') \/
 (exists m1, JitKRef.JitKRef.EndsSrc sealed E pt s c0 m1 /\ TStar m m1).

Theorem preservation_old_of_new : preservation'_statement -> old_reflect_statement -> preservation_old_statement.
Proof.
 intros Pr Rf n s c m H G. destruct env_ok_inhabited as [rs Eo].
 destruct (Pr n [] c m rs Eo (ms_embed [] s c m H (storerel_nil s m G)))
   as [(c' & m' & k & tS & tT & mu' & Ss & Tr & Le & Mp & Mx & Ms)|(m1 & k & tS & tT & En & Tr & Mp)].
 - destruct (proj1 (Rf s c m rs k tS tT m' Eo H G Tr Mp) c' mu' Ss Mx Ms) as [E0 Ms0]. subst tS; cbn in Mp; subst tT.
   left. exists c', m', k. repeat split; auto; [apply srun_nil_sstar; exact Ss|eapply trun_nil_tn; exact Tr].
 - destruct (proj2 (Rf s c m rs k tS tT m1 Eo H G Tr Mp) En) as [E0 En0]. subst tS; cbn in Mp; subst tT.
   right. exists m1. split; [exact En0|]. eapply tn_tstar. eapply trun_nil_tn; exact Tr.
Qed.

Theorem call_preservation_old_of_new : call_preservation'_statement -> old_reflect_statement -> call_preservation_old_statement.
Proof.
 intros Cp Rf s m c ps b args n Cm Cf L En G c0. destruct env_ok_inhabited as [rs Eo].
 pose proof (ms_entered s m c ps b args Cm Cf L En) as H0.
 destruct (Cp [] s m c ps b args n rs Eo (sm_embed [] s [] m Cm (Forall_nil _) (storerel_nil s m G))
   (comp_embed_fn _ _ _ Cf) L (entered_embed [] s m c args Cm En))
   as [(c' & m' & k & tS & tT & mu' & Ss & Tr & Le & Mp & Mx & Ms)|(m1 & k & tS & tT & En1 & Tr & Mp)].
 - destruct (proj1 (Rf s c0 m rs k tS tT m' Eo H0 G Tr Mp) c' mu' Ss Mx Ms) as [E0 Ms0]. subst tS; cbn in Mp; subst tT.
   left. exists c', m', k. repeat split; auto; [apply srun_nil_sstar; exact Ss|eapply trun_nil_tn; exact Tr].
 - destruct (proj2 (Rf s c0 m rs k tS tT m1 Eo H0 G Tr Mp) En1) as [E0 En0]. subst tS; cbn in Mp; subst tT.
   right. exists m1. split; [exact En0|]. eapply tn_tstar. eapply trun_nil_tn; exact Tr.
Qed.

Theorem call_preservation_src_old_of_new : call_preservation_src'_statement -> old_reflect_statement ->
 old_reflect_src_statement -> call_preservation_src_old_statement.
Proof.
 intros Cp Rf Rs s m c ps b0 b1 e args n Dw K1 K2 Sh So Cm Cf L En G c0 ce. destruct env_ok_inhabited as [rs Eo].
 pose proof (ms_entered s m c ps e args Cm Cf L En) as H0.
 destruct (Cp [] s m c ps b0 b1 e args n rs Eo Dw K1 K2 Sh So (sm_embed [] s [] m Cm (Forall_nil _) (storerel_nil s m G))
   (comp_embed_fn _ _ _ Cf) L (entered_embed [] s m c args Cm En))
   as [(c' & m' & k & tS & tT & mu' & Ss & Tr & Le & Mp & Mx & Ms)|(m1 & k & tS & tT & En1 & Tr & Mp)].
 - destruct (proj1 (Rf s ce m rs k tS tT m' Eo H0 G Tr Mp) c' mu' Ss Mx Ms) as [E0 Ms0]. subst tS; cbn in Mp; subst tT.
   left. exists c', m', k. repeat split; auto; [apply srun_nil_sstar; exact Ss|eapply trun_nil_tn; exact Tr].
 - destruct (Rs s m c ps b0 b1 e args rs k tS tT m1 Eo Dw K1 K2 Sh So Cm Cf L En G Tr Mp En1) as [E0 En0].
   subst tS; cbn in Mp; subst tT.
   right. exists m1. split; [exact En0|]. eapply tn_tstar. eapply trun_nil_tn; exact Tr.
Qed.
End Src.
End Inv.
End JitEmitInv.
