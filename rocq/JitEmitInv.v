(* Shen/JIT Phase 2, emit-spec: the generalized invariant of the back end, and the statements the
   emission families (emit-sim) and checkers (emit-check) must prove. Statements only, each a
   `Definition ... : Prop` with a "Does NOT say" note; NOTHING here is assumed or Admitted.
   Proved here (closed): VR_VRh, VRh_no_partial, HK_length, do_body_second, the embedding of the
   old invariant at any mu that relates the store's cells and globals (kont_embed, sm_embed,
   ms_embed), env_ok_inhabited, TRun_0, Out'_not_stuck, value_bound/value_unbound,
   SimC/T/O/S/W/A_of_sim', Ends'_final, EndsSrc'_final, the old-fragment bridges (srun_nil_sstar,
   trun_nil_tn, tn_tstar, ms_entered, entered_embed) and the three *_old_of_new corollaries
   (vacuous: their hypothesis old_reflect_statement is FALSE, old_reflect_false below);
   get_time_agree (get-time's request, answer and result agree on related arguments);
   old_reflect_false, a counterexample to old_reflect_statement through JitEmitKont's do frames;
   the three *_old_of_new' corollaries from old_reflect'_statement (the reflection with source
   catch-up; NOT proved), and cx_catch_up (old_reflect_false's counterexample is not one to it);
   gvals_needed and the dv_* Examples, the divergences behind each narrowing (frame_prim's
   exclusions, the window bound, env_ok, GvalsRel), checked at the primitive level.
   Fix round 3 (closed, from run determinism and the PROVED old theorems): old_reflect'_silent,
   old_reflect'_ends (old_reflect''s end conjunct), old_reflect'_iff_core (old_reflect' is exactly
   old_reflect_core_statement, NOT proved), old_reflect_src_of_fundamental (a reduction to the
   fundamental property), and the *_old_statement targets from the old
   theorems (preservation_old_holds, call_preservation_old_holds,
   call_preservation_src_old_of_fundamental; a sanity check, nothing about the new statements).
   r21-sms-fresh-fix (closed): Fresh (no heap key at or above m_next in use) and SMs's sm_fresh;
   fresh_empty, fresh_used_lt, fresh_alloc, fresh_set_used, vrh_fresh_ext, sms_alloc (an
   allocation keeps SMs) and sms_raise_final (a raise with no handler ends in an SMs-related
   machine holding the exception); the relation before the fix kept as SMs_v1, SM_v1,
   EvalCtx_v1, TestCtx_v1, OpCtx_v1, MS'_v1, Ends'_v1, EndsSrc'_v1 and the refuted
   preservation'_statement_v1, call_preservation'_statement_v1, call_preservation_src'_statement_v1
   (refutations in JitEmitSim); sm_embed and ms_embed take Fresh m; the *_old_fresh statements
   (each *_old statement with Fresh m added), the targets the *_old_of_new corollaries now reach,
   and *_old_fresh_of_old; cx_fresh.
   Fix round 4 (closed): old_reflect_src (old_reflect_src_statement, PROVED from
   JitKRefFund.fundamental), call_preservation_src_old_holds, call_preservation_src_old_of_new'';
   env_ok_needed and resp_ok_bound_needed (preservation'_statement without env_ok is FALSE, so the
   premise is necessary), with preservation'_of_noenv, noenv_false_at and gt_sm/gt_ms/gt_next/gt_trun_none.

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
                                            MS/Ends/EndsSrc. old_reflect_statement is FALSE
                                            (old_reflect_false: the do frames); the src one is
                                            stated, NOT proved, truth UNKNOWN.
   old_reflect'_statement                   old_reflect_statement with source catch-up (some c''
                                            the source reaches silently from c' is MS-related);
                                            NOT proved, truth UNKNOWN. *_old_of_new' derive the
                                            old conclusions from it and the new statements.
   The old fragment: no handler, no capture, no do frame, what MS, Com and JitLowerRel.CompFn
   describe; the embedding (ms_embed) holds at any mu StoreRel admits, the corollaries are at mu = []. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation JitEmitKont KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitMeta JitProfile
 JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef JitKRefCompose JitKRefFund
 JitEmitRuleEq JitEmitRuleStore JitEmitRulePrim JitEmitRuleDoFold JitEmitRuleClo JitEmitRuleApp JitEmitRuleTrap
 JitEmitRel.
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

(* The allocation pointer is fresh: no heap key at or above m_next is in use (r21-sms-fresh-fix).
   JitBytecode.alloc writes at m_next without looking and moves to its successor, so without this
   a related machine may overwrite a live object on its next allocation (JitEmitSim.fx_next: an
   exception over do's closure, after which FunRel' holds for no store). Every key a related
   value, a mu cell or a gfun closure names is in use (each asks tget p (m_heap m) = Some _), so it
   lies below m_next. Kept by an allocation (fresh_alloc) and by a heap write at a key in use
   (fresh_set_used); the loader's empty machine has it (fresh_empty).
   Does NOT say: anything about keys below m_next (in use or not), about m_allocs, or that a
   machine whose m_next is stale behaves differently on every run (fx_m does on its first step). *)
Definition Fresh (m : B.machine) : Prop :=
 forall p, (B.m_next m <= p)%positive -> B.tget p (B.m_heap m) = None.

(* Store against machine, without the continuation.
   Does NOT say: anything about cells outside mu, gfun entries of names the store does not
   define beyond fr'_none, the sealed table, or the allocation counter beyond Fresh. The kernel's
   do is not here: the do frames ask it (JitEmitKont's DoK, instantiated with DoOK of the current
   store). Before r21-sms-fresh-fix it had no sm_fresh; that text is SMs_v1 below, and the
   statements over it are refuted (JitEmitSim.*_false). *)
Record SMs (mu : kmap) (s : store) (m : B.machine) : Prop := {
 sm_bij : pbij mu;
 sm_heap : HeapRel mu s m;
 sm_gvals : GvalsRel mu s m;
 sm_fun : FunRel' s m;
 sm_fresh : Fresh m }.

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

(* ---------- the relation before r21-sms-fresh-fix (v1, kept for the refutations) ----------
   SMs without sm_fresh, and SM, the three contexts and MS' over it, each a copy of the text before
   r21-sms-fresh-fix with _v1 added to its name and to its fields and constructors (nothing else
   changed). The *_v1 statements below are the text r22-emit-sim refuted (JitEmitSim.*_false);
   they are kept so that each refutation stays about the text it refutes. No other statement uses
   these. Does NOT say: anything the statements over SMs (with sm_fresh) do not. *)
Record SMs_v1 (mu : kmap) (s : store) (m : B.machine) : Prop := {
 sm_bij_v1 : pbij mu;
 sm_heap_v1 : HeapRel mu s m;
 sm_gvals_v1 : GvalsRel mu s m;
 sm_fun_v1 : FunRel' s m }.

Definition SM_v1 (mu : kmap) (s : store) (k : list frame) (m : B.machine) : Prop :=
 SMs_v1 mu s m /\ HK (B.m_handlers m) k.

Definition EvalCtx_v1 (mu : kmap) (cv : list name) (caps : list B.val) (g : env) (top : N) (dst : dest)
    (r2 : list B.instr) (rho : lenv) (k : list frame) (s : store) (w : N -> Prop) (m : B.machine) : Prop :=
 SM_v1 mu s k m /\ MEnv' (V mu m) (fp m) (st m) cv caps g rho /\ EnvBelow g top /\ Above (fp m) top w /\
 CCtx (HC m) (code m) cv caps (fp m) (st m) /\ (cv = [] \/ ~ w (fp m + 1)) /\
 KC' (V mu m) (HC m) (DK s) (code m) cv caps (fp m) (st m) (cs m) (hs m) w dst r2 k.
Definition TestCtx_v1 (mu : kmap) (cv : list name) (caps : list B.val) (g : env) (top : N) (l : N)
    (r2 : list B.instr) (rho : lenv) (k : list frame) (s : store) (w : N -> Prop) (m : B.machine) : Prop :=
 SM_v1 mu s k m /\ MEnv' (V mu m) (fp m) (st m) cv caps g rho /\ EnvBelow g top /\ Above (fp m) top w /\
 CCtx (HC m) (code m) cv caps (fp m) (st m) /\ (cv = [] \/ ~ w (fp m + 1)) /\
 TK' (V mu m) (HC m) (DK s) (code m) cv caps (fp m) (st m) (cs m) (hs m) w true l r2 k.
Definition OpCtx_v1 (mu : kmap) (cv : list name) (caps : list B.val) (g : env) (top : N) (o : B.operand)
    (r2 : list B.instr) (rho : lenv) (k : list frame) (s : store) (w : N -> Prop) (m : B.machine) : Prop :=
 SM_v1 mu s k m /\ MEnv' (V mu m) (fp m) (st m) cv caps g rho /\ EnvBelow g top /\ Above (fp m) top w /\
 CCtx (HC m) (code m) cv caps (fp m) (st m) /\ (cv = [] \/ ~ w (fp m + 1)) /\
 KD' (V mu m) (HC m) (DK s) (code m) cv caps (fp m) (st m) (cs m) (hs m) w o r2 k.

Inductive MS'_v1 (mu : kmap) : config -> B.machine -> Prop :=
 | MS'_eval_v1 cv caps g top e dst r2 rho k s w m :
     Comp (code m) cv g top e dst (B.m_rest m) r2 -> EvalCtx_v1 mu cv caps g top dst r2 rho k s w m ->
     MS'_v1 mu (Cfg (Eval rho e) k s) m
 | MS'_test_v1 cv caps g top e l r2 rho k s w m :
     CompT (code m) cv g top e l (B.m_rest m) r2 -> TestCtx_v1 mu cv caps g top l r2 rho k s w m ->
     MS'_v1 mu (Cfg (Eval rho e) k s) m
 | MS'_op_v1 cv caps g top e o top2 r2 rho k s w m :
     CompOp (code m) cv g top e o top2 (B.m_rest m) r2 -> OpCtx_v1 mu cv caps g top o r2 rho k s w m ->
     MS'_v1 mu (Cfg (Eval rho e) k s) m
 | MS'_ret_v1 cv caps v v' o k s w m :
     SM_v1 mu s k m -> read_o (code m) (fp m) (st m) o = Some v' -> VRh mu (B.m_heap m) v v' ->
     CCtx (HC m) (code m) cv caps (fp m) (st m) -> (cv = [] \/ ~ w (fp m + 1)) ->
     KD' (V mu m) (HC m) (DK s) (code m) cv caps (fp m) (st m) (cs m) (hs m) w o (B.m_rest m) k ->
     MS'_v1 mu (Cfg (Ret v) k s) m.

(* ---------- freshness is kept (closed) ---------- *)
Lemma fresh_empty : Fresh B.empty_machine.
Proof. intros p _. apply JitMeta.JitMeta.tget_leaf. Qed.

Lemma fresh_used_lt : forall m p o, Fresh m -> B.tget p (B.m_heap m) = Some o -> (p < B.m_next m)%positive.
Proof.
 intros m p o F T. destruct (Pos.lt_total p (B.m_next m)) as [L|[E|L]]; [exact L| |];
   rewrite (F p) in T by lia; discriminate.
Qed.

(* An allocation keeps Fresh: it writes at m_next and moves past it. *)
Lemma fresh_alloc : forall m o, Fresh m -> Fresh (snd (B.alloc m o)).
Proof.
 intros m o F p L. cbn in L |- *. rewrite JitMeta.JitMeta.tget_tset_other by lia. apply F. lia.
Qed.

(* A heap write at a key in use keeps Fresh (a vector cell update, for one). *)
Lemma fresh_set_used : forall m p o o', Fresh m -> B.tget p (B.m_heap m) = Some o' ->
 Fresh (B.set_heap m (B.tset p o (B.m_heap m))).
Proof.
 intros m p o o' F T q L. cbn in L |- *. pose proof (fresh_used_lt m p o' F T) as Lp.
 rewrite JitMeta.JitMeta.tget_tset_other by lia. apply F. exact L.
Qed.

(* Writing at a key not in use keeps every relation over the heap. *)
Lemma vrh_fresh_ext : forall mu h p o, B.tget p h = None -> forall v v', VRh mu h v v' -> VRh mu (B.tset p o h) v v'.
Proof.
 intros mu h p o Np. assert (K : forall q x, B.tget q h = Some x -> B.tget q (B.tset p o h) = Some x).
 { intros q x T. rewrite JitMeta.JitMeta.tget_tset_other; [exact T|]. intros ->. congruence. }
 fix IH 3. intros v v' H. destruct H as [z|b|x|b|t| |a a' d d' Ha Hd|l q cells Il Tq
   |x b rho q nc caps cv l0 Tq Ck Ci Il Lc Hc|b rho q nc caps cv l0 Tq Ck Ci Il Lc Hc|x q msg tv Tq Xo|hd q d0 o0 Tq].
 - constructor.
 - constructor.
 - constructor.
 - constructor.
 - constructor.
 - constructor.
 - constructor; [exact (IH _ _ Ha)|exact (IH _ _ Hd)].
 - eapply VRh_vec; [exact Il|exact (K _ _ Tq)].
 - eapply VRh_lam; [exact (K _ _ Tq)|exact Ck|exact Ci|exact Il|exact Lc|].
   intros i y Ni Ly. destruct (Hc i y Ni Ly) as (u & u' & Lu & Nu & Vu). exists u, u'. split; [exact Lu|split; [exact Nu|exact (IH _ _ Vu)]].
 - eapply VRh_frozen; [exact (K _ _ Tq)|exact Ck|exact Ci|exact Il|exact Lc|].
   intros i y Ni. destruct (Hc i y Ni) as (u & u' & Lu & Nu & Vu). exists u, u'. split; [exact Lu|split; [exact Nu|exact (IH _ _ Vu)]].
 - eapply VRh_exn; [exact (K _ _ Tq)|exact Xo].
 - eapply VRh_stream; exact (K _ _ Tq).
Qed.

(* An allocation keeps SMs, at the same mu and store: the new object goes to a key no related
   value, cell or gfun closure names. Without sm_fresh this is false (JitEmitSim.fx_next). *)
Theorem sms_alloc : forall mu s m o, SMs mu s m -> SMs mu s (snd (B.alloc m o)).
Proof.
 intros mu s m o [Pb Hr [G1 G2] Fr Fs].
 assert (Np : B.tget (B.m_next m) (B.m_heap m) = None) by (apply Fs; lia).
 assert (K : forall q x, B.tget q (B.m_heap m) = Some x -> B.tget q (B.tset (B.m_next m) o (B.m_heap m)) = Some x).
 { intros q x T. rewrite JitMeta.JitMeta.tget_tset_other; [exact T|]. intros ->. congruence. }
 constructor; cbn.
 - exact Pb.
 - intros l p I. destruct (Hr l p I) as [(c0 & c1 & N0 & T & F2)|(N0 & nc & caps & T)].
   + left. exists c0, c1. split; [exact N0|split; [exact (K _ _ T)|]]. cbn.
     eapply Forall2_impl; [|exact F2]. intros a b0 V0. exact (vrh_fresh_ext _ _ _ _ Np _ _ V0).
   + right. split; [exact N0|]. exists nc, caps. exact (K _ _ T).
 - split.
   + intros x v L. destruct (G1 x v L) as (v' & T & Nc & Vr). exists v'. split; [exact T|split; [exact Nc|]].
     exact (vrh_fresh_ext _ _ _ _ Np _ _ Vr).
   + exact G2.
 - destruct Fr as [U N0 P0 Q0]. constructor; [|exact N0|exact P0|exact Q0].
   intros f ps b L. destruct (U f ps b L) as (l & c & caps & Gl & Hl & R). exists l, c, caps.
   split; [exact Gl|split; [exact (K _ _ Hl)|exact R]].
 - exact (fresh_alloc m o Fs).
Qed.

(* The end of a raise with no handler: the exception is allocated, and SMs still holds of the
   final machine, which holds the exception. (The step r22-emit-sim's counterexample breaks.) *)
Theorem sms_raise_final : forall mu s m msg v o m', SMs mu s m -> B.m_handlers m = [] ->
 B.raise m msg v = B.MFinal o m' -> SMs mu s m' /\
   exists l, o = B.FError (B.VExn l) /\ B.tget l (B.m_heap m') = Some (B.OExn msg v).
Proof.
 intros mu s m msg v o m' S H R. unfold B.raise in R. rewrite H in R. cbn in R. injection R as <- <-.
 split; [exact (sms_alloc mu s m (B.OExn msg v) S)|]. exists (B.m_next m). split; [reflexivity|].
 cbn. apply JitMeta.JitMeta.tget_tset_same.
Qed.


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

(* Fresh is not in StoreRel (the old invariant does not carry it either): each embedding asks it
   separately (r21-sms-fresh-fix). *)
Lemma sm_embed : forall mu s k m, Com s m -> notrap k -> StoreRel mu s m -> Fresh m -> SM mu s k m.
Proof.
 intros mu s k m [Hh Fr] Nt (Pb & Hr & G) Fs. split.
 - constructor; auto. apply funrel_embed; auto.
 - unfold HK. rewrite Hh, (notrap_frames k Nt). constructor.
Qed.

(* JitLowerStep's MS is MS' at any mu that relates the store's cells and globals (StoreRel). *)
Theorem ms_embed : forall mu s c m, MS s c m -> StoreRel mu s m -> Fresh m -> MS' mu c m.
Proof.
 intros mu s c m H G Fs. destruct H as [g top e dst r2 rho k w m Cm Cc Me Eb Ab Kc|g top e l r2 rho k w m Cm Ct Me Eb Ab Tk
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
Lemma S_run_text : B.S_run = B.sym_of_text (of_string "run"). Proof. vm_compute. reflexivity. Qed.
Lemma S_unix_text : B.S_unix = B.sym_of_text (of_string "unix"). Proof. vm_compute. reflexivity. Qed.

(* get-time, the one IO primitive frame_prim admits: on related arguments, the source and the
   bytecode both ask the clock, with the request ev_of translates to the source's, and for every
   answer resp_ok admits the source's result is related to what the bytecode writes; or both
   raise. *)
Theorem get_time_agree : forall mu h m d v v' s, VRh mu h v v' ->
 (exists run q f kk, prim_rule_r (jit_rules sealed) jit_profile PGetTime [v] s = PIO q f /\
   B.prim_step E pt m d B.PGetTime [v'] = B.MIO (B.JTime run) kk /\
   forall r, resp_ok (B.JTime run) r -> exists b, r = B.JTimeIs b /\
     ev_of (B.JTime run) r = Some (EvIO q (RTime (Z.of_N b))) /\
     f (RTime (Z.of_N b)) = ORet (VNum (NFloat b)) s /\
     B.MTau (kk r) = B.ret_to m d (B.VReal b) /\ VRh mu (B.m_heap m) (VNum (NFloat b)) (B.VReal b)) \/
 (exists x msg tv, prim_rule_r (jit_rules sealed) jit_profile PGetTime [v] s = PDone (OThrow x) /\
   B.prim_step E pt m d B.PGetTime [v'] = B.raise m msg tv /\ exn_ok x msg).
Proof.
 intros mu h m d v v' s Hv.
 destruct Hv; try (right; eexists _, _, _; split; [reflexivity|split; [reflexivity|exact I]]).
 (* a symbol *)
 idtac.
 cbn [B.prim_step].
 destruct (Pos.eqb (B.sym_of_text s0) B.S_run) eqn:Er; [|destruct (Pos.eqb (B.sym_of_text s0) B.S_unix) eqn:Eu].
 - rewrite S_run_text, B.sym_of_text_eqb in Er. apply text_eqb_eq in Er. subst s0. left.
   eexists true, _, _, _. split; [reflexivity|]. split; [reflexivity|].
   intros r Hr. destruct r; cbn in Hr; try contradiction. exists bits. split; [reflexivity|].
   assert (Hb : (bits <? 18446744073709551616)%N = true) by (apply N.ltb_lt; exact Hr).
   cbn [ev_of]. rewrite Hb. split; [reflexivity|].
   split; [|split; [reflexivity|constructor]].
   cbn. unfold jit_time. replace ((0 <=? Z.of_N bits)%Z && (Z.of_N bits <? 18446744073709551616)%Z)%bool with true.
   + rewrite N2Z.id. reflexivity.
   + symmetry. apply andb_true_intro. split; [apply Z.leb_le; lia|apply Z.ltb_lt; apply N.ltb_lt in Hb; lia].
 - rewrite S_unix_text, B.sym_of_text_eqb in Eu. apply text_eqb_eq in Eu. subst s0. left.
   eexists false, _, _, _. split; [reflexivity|]. split; [reflexivity|].
   intros r Hr. destruct r; cbn in Hr; try contradiction. exists bits. split; [reflexivity|].
   assert (Hb : (bits <? 18446744073709551616)%N = true) by (apply N.ltb_lt; exact Hr).
   cbn [ev_of]. rewrite Hb. split; [reflexivity|].
   split; [|split; [reflexivity|constructor]].
   cbn. unfold jit_time. replace ((0 <=? Z.of_N bits)%Z && (Z.of_N bits <? 18446744073709551616)%Z)%bool with true.
   + rewrite N2Z.id. reflexivity.
   + symmetry. apply andb_true_intro. split; [apply Z.leb_le; lia|apply Z.ltb_lt; apply N.ltb_lt in Hb; lia].
 - right. rewrite S_run_text, B.sym_of_text_eqb in Er. rewrite S_unix_text, B.sym_of_text_eqb in Eu.
   exists (XPrim PGetTime); eexists _, _. split; [|split; [reflexivity|exact I]].
   assert (Er' : text_eqb s0 (of_string "run") = false) by exact Er.
   assert (Eu' : text_eqb s0 (of_string "unix") = false) by exact Eu.
   unfold prim_rule_r, rule_get_time_r. cbn [time_kind_ok jit_rules]. rewrite Er', Eu'. reflexivity.
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

(* preservation'_statement with its env_ok rs premise dropped, nothing else changed. NOT a
   statement any task proves: it is the text env_ok_needed (end of this file) refutes, which shows
   the env_ok premise is necessary for preservation'_statement as stated (preservation'_of_noenv:
   dropping it only strengthens). *)
Definition preservation_noenv_statement : Prop := forall n mu c m (rs : nat -> B.jreq -> B.jres), MS' mu c m ->
 (exists c' m' k tS tT mu', Srun c tS c' /\ TRun rs k m tT m' /\ (n <= k)%nat /\ map Some tS = tT /\
    mext mu mu' /\ MS' mu' c' m') \/
 (exists m1 k tS tT, Ends' mu c m1 tS /\ TRun rs k m tT m1 /\ map Some tS = tT).
Lemma preservation'_of_noenv : preservation_noenv_statement -> preservation'_statement.
Proof. intros P n mu c m rs _ H. exact (P n mu c m rs H). Qed.

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

(* ---------- the run statements before r21-sms-fresh-fix (v1, refuted) ----------
   preservation'_statement and call_preservation'_statement as they were before
   r21-sms-fresh-fix, over MS'_v1, SM_v1 and Ends'_v1 (SMs_v1: no sm_fresh); the text otherwise
   unchanged. FALSE: JitEmitSim.preservation'_false and call_preservation'_false refute them at
   cx_E, cx_pt, sealed [] (a stale m_next; the first allocation overwrites do's closure).
   The statements above (preservation'_statement, call_preservation'_statement) are the corrected
   ones: the same text over SMs with sm_fresh, and so with MS', SM and Ends' keeping m_next fresh
   at every related state and at every end. Their conclusions keep everything the v1 ones had (the
   same disjuncts, the same observation: traces, final values and exceptions related); only the
   relation they speak of is stronger, in premise and conclusion alike. *)
Inductive Ends'_v1 (mu : kmap) (c : config) (m1 : B.machine) (t : trace) : Prop :=
 | E'_ok_v1 v v' s' m2 mu' : Srun c t (Cfg (Ret v) [] s') -> B.next E pt m1 = B.MFinal (B.FReturn v') m2 ->
     mext mu mu' -> VRh mu' (B.m_heap m2) v v' -> SMs_v1 mu' s' m2 -> Ends'_v1 mu c m1 t
 | E'_err_v1 x l msg tv s' m2 mu' : Srun c t (Cfg (Throw x) [] s') -> B.next E pt m1 = B.MFinal (B.FError (B.VExn l)) m2 ->
     B.tget l (B.m_heap m2) = Some (B.OExn msg tv) -> exn_ok x msg -> mext mu mu' -> SMs_v1 mu' s' m2 -> Ends'_v1 mu c m1 t.

Definition preservation'_statement_v1 : Prop := forall n mu c m (rs : nat -> B.jreq -> B.jres), env_ok rs -> MS'_v1 mu c m ->
 (exists c' m' k tS tT mu', Srun c tS c' /\ TRun rs k m tT m' /\ (n <= k)%nat /\ map Some tS = tT /\
    mext mu mu' /\ MS'_v1 mu' c' m') \/
 (exists m1 k tS tT, Ends'_v1 mu c m1 tS /\ TRun rs k m tT m1 /\ map Some tS = tT).

Definition call_preservation'_statement_v1 : Prop := forall mu s m c ps b args n (rs : nat -> B.jreq -> B.jres),
 env_ok rs -> SM_v1 mu s [] m -> CompFn' c ps b -> List.length ps = List.length args -> entered' mu m c args ->
 let c0 := Cfg (Eval (combine ps args) b) [] s in
 (exists c' m' k tS tT mu', Srun c0 tS c' /\ TRun rs k m tT m' /\ (n <= k)%nat /\ map Some tS = tT /\
    mext mu mu' /\ MS'_v1 mu' c' m') \/
 (exists m1 k tS tT, Ends'_v1 mu c0 m1 tS /\ TRun rs k m tT m1 /\ map Some tS = tT).

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

(* call_preservation_src'_statement as it was before r21-sms-fresh-fix, over SM_v1, MS'_v1 and
   EndsSrc'_v1 (SMs_v1: no sm_fresh); the text otherwise unchanged. FALSE:
   JitEmitSim.call_preservation_src'_false refutes it at cx_E, cx_pt, sealed [], D = []. The
   statement above is the corrected one: the same text over SMs with sm_fresh. *)
Inductive EndsSrc'_v1 (mu : kmap) (s : store) (c0 : config) (m1 : B.machine) (t : trace) : Prop :=
 | ES'_ok_v1 v0 v v' s0 s' w m2 mu' : Srun c0 t (Cfg (Ret v0) [] s0) ->
     JitKRef.JitKRef.wext (JitKRef.JitKRef.id_world s) w -> JitKRef.JitKRef.GVal w v0 v ->
     JitKRef.JitKRef.GStore w s0 s' ->
     B.next E pt m1 = B.MFinal (B.FReturn v') m2 -> mext mu mu' -> VRh mu' (B.m_heap m2) v v' ->
     SMs_v1 mu' s' m2 -> EndsSrc'_v1 mu s c0 m1 t
 | ES'_err_v1 x l msg tv s0 s' w m2 mu' : Srun c0 t (Cfg (Throw x) [] s0) ->
     JitKRef.JitKRef.wext (JitKRef.JitKRef.id_world s) w -> JitKRef.JitKRef.GStore w s0 s' ->
     B.next E pt m1 = B.MFinal (B.FError (B.VExn l)) m2 -> B.tget l (B.m_heap m2) = Some (B.OExn msg tv) ->
     exn_ok x msg -> mext mu mu' -> SMs_v1 mu' s' m2 -> EndsSrc'_v1 mu s c0 m1 t.

Definition call_preservation_src'_statement_v1 : Prop := forall mu s m c ps b0 b1 e args n (rs : nat -> B.jreq -> B.jres),
 env_ok rs -> JitKRef.JitKRef.D_wf sealed D -> JitKRef.JitKRef.KRef sealed D ps b0 b1 -> JitKRef.JitKRef.KRef sealed D ps b1 e ->
 JitKRef.JitKRef.StoreHas D s -> store_ok s ->
 SM_v1 mu s [] m -> CompFn' c ps e -> List.length ps = List.length args -> entered' mu m c args ->
 let c0 := Cfg (Eval (combine ps args) b0) [] s in
 let ce := Cfg (Eval (combine ps args) e) [] s in
 (exists c' m' k tS tT mu', Srun ce tS c' /\ TRun rs k m tT m' /\ (n <= k)%nat /\ map Some tS = tT /\
    mext mu mu' /\ MS'_v1 mu' c' m') \/
 (exists m1 k tS tT, EndsSrc'_v1 mu s c0 m1 tS /\ TRun rs k m tT m1 /\ map Some tS = tT).

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
   follow from the new statements alone. The reflection as stated is FALSE (old_reflect_false at
   the end of this file): JitEmitKont's do frames let MS' relate a source configuration to a
   machine that has already returned from do, which MS does not, so the corollaries below are
   vacuous and recover nothing. Reflecting
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

(* The reflection obligation. FALSE: old_reflect_false (end of this file) refutes its first
   conjunct through the do frame KD'_do2. Kept as stated, so the refutation is about this text.
   From a state MS relates, with
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
   (the emitted body's final store s, the value VR-related). Proved in fix round 4 (old_reflect_src).
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

(* The *_old statements with Fresh m added (r21-sms-fresh-fix): the targets the corollaries below
   reach from the corrected new statements. Fresh m is needed for the same reason GvalsRel [] s m
   is: the old premises (MS, Com) leave the machine's m_next unconstrained, and the corrected
   invariant says nothing of a machine whose m_next is stale (JitEmitSim.fresh_needed: the old
   premises hold at r22-emit-sim's fx_m, and SM at no mu). The *_old statements without it are
   kept and still proved (preservation_old_holds, call_preservation_old_holds,
   call_preservation_src_old_holds), but they no longer follow from the new statements.
   Does NOT say: anything at a machine whose m_next is stale or whose globals VR does not relate. *)
Definition preservation_old_fresh_statement : Prop := forall n s c m, MS s c m -> Fresh m -> GvalsRel [] s m ->
 (exists c' m' k, Sstar c c' /\ JitLowerThm.TN E pt k m m' /\ (n <= k)%nat /\ MS s c' m') \/
 (exists m1, JitLowerThm.Ends E pt sealed s c m1 /\ TStar m m1).

Definition call_preservation_old_fresh_statement : Prop := forall s m c ps b args n,
 Com s m -> JitLowerRel.CompFn c ps b -> List.length ps = List.length args -> entered m c args -> GvalsRel [] s m -> Fresh m ->
 let c0 := Cfg (Eval (combine ps args) b) [] s in
 (exists c' m' k, Sstar c0 c' /\ JitLowerThm.TN E pt k m m' /\ (n <= k)%nat /\ MS s c' m') \/
 (exists m1, JitLowerThm.Ends E pt sealed s c0 m1 /\ TStar m m1).

Definition call_preservation_src_old_fresh_statement : Prop := forall s m c ps b0 b1 e args n,
 JitKRef.JitKRef.D_wf sealed D -> JitKRef.JitKRef.KRef sealed D ps b0 b1 -> JitKRef.JitKRef.KRef sealed D ps b1 e ->
 JitKRef.JitKRef.StoreHas D s -> store_ok s ->
 Com s m -> JitLowerRel.CompFn c ps e -> List.length ps = List.length args -> entered m c args -> GvalsRel [] s m -> Fresh m ->
 let c0 := Cfg (Eval (combine ps args) b0) [] s in
 let ce := Cfg (Eval (combine ps args) e) [] s in
 (exists c' m' k, Sstar ce c' /\ JitLowerThm.TN E pt k m m' /\ (n <= k)%nat /\ MS s c' m') \/
 (exists m1, JitKRef.JitKRef.EndsSrc sealed E pt s c0 m1 /\ TStar m m1).

(* Each *_old_fresh statement is implied by its *_old statement (one more premise, unused). *)
Lemma preservation_old_fresh_of_old : preservation_old_statement -> preservation_old_fresh_statement.
Proof. intros P n s c m H _ G. exact (P n s c m H G). Qed.
Lemma call_preservation_old_fresh_of_old : call_preservation_old_statement -> call_preservation_old_fresh_statement.
Proof. intros P s m c ps b args n Cm Cf L En G _. exact (P s m c ps b args n Cm Cf L En G). Qed.
Lemma call_preservation_src_old_fresh_of_old : call_preservation_src_old_statement -> call_preservation_src_old_fresh_statement.
Proof. intros P s m c ps b0 b1 e args n Dw K1 K2 Sh So Cm Cf L En G _. exact (P s m c ps b0 b1 e args n Dw K1 K2 Sh So Cm Cf L En G). Qed.

Theorem preservation_old_of_new : preservation'_statement -> old_reflect_statement -> preservation_old_fresh_statement.
Proof.
 intros Pr Rf n s c m H Fs G. destruct env_ok_inhabited as [rs Eo].
 destruct (Pr n [] c m rs Eo (ms_embed [] s c m H (storerel_nil s m G) Fs))
   as [(c' & m' & k & tS & tT & mu' & Ss & Tr & Le & Mp & Mx & Ms)|(m1 & k & tS & tT & En & Tr & Mp)].
 - destruct (proj1 (Rf s c m rs k tS tT m' Eo H G Tr Mp) c' mu' Ss Mx Ms) as [E0 Ms0]. subst tS; cbn in Mp; subst tT.
   left. exists c', m', k. repeat split; auto; [apply srun_nil_sstar; exact Ss|eapply trun_nil_tn; exact Tr].
 - destruct (proj2 (Rf s c m rs k tS tT m1 Eo H G Tr Mp) En) as [E0 En0]. subst tS; cbn in Mp; subst tT.
   right. exists m1. split; [exact En0|]. eapply tn_tstar. eapply trun_nil_tn; exact Tr.
Qed.

Theorem call_preservation_old_of_new : call_preservation'_statement -> old_reflect_statement -> call_preservation_old_fresh_statement.
Proof.
 intros Cp Rf s m c ps b args n Cm Cf L En G Fs c0. destruct env_ok_inhabited as [rs Eo].
 pose proof (ms_entered s m c ps b args Cm Cf L En) as H0.
 destruct (Cp [] s m c ps b args n rs Eo (sm_embed [] s [] m Cm (Forall_nil _) (storerel_nil s m G) Fs)
   (comp_embed_fn _ _ _ Cf) L (entered_embed [] s m c args Cm En))
   as [(c' & m' & k & tS & tT & mu' & Ss & Tr & Le & Mp & Mx & Ms)|(m1 & k & tS & tT & En1 & Tr & Mp)].
 - destruct (proj1 (Rf s c0 m rs k tS tT m' Eo H0 G Tr Mp) c' mu' Ss Mx Ms) as [E0 Ms0]. subst tS; cbn in Mp; subst tT.
   left. exists c', m', k. repeat split; auto; [apply srun_nil_sstar; exact Ss|eapply trun_nil_tn; exact Tr].
 - destruct (proj2 (Rf s c0 m rs k tS tT m1 Eo H0 G Tr Mp) En1) as [E0 En0]. subst tS; cbn in Mp; subst tT.
   right. exists m1. split; [exact En0|]. eapply tn_tstar. eapply trun_nil_tn; exact Tr.
Qed.

Theorem call_preservation_src_old_of_new : call_preservation_src'_statement -> old_reflect_statement ->
 old_reflect_src_statement -> call_preservation_src_old_fresh_statement.
Proof.
 intros Cp Rf Rs s m c ps b0 b1 e args n Dw K1 K2 Sh So Cm Cf L En G Fs c0 ce. destruct env_ok_inhabited as [rs Eo].
 pose proof (ms_entered s m c ps e args Cm Cf L En) as H0.
 destruct (Cp [] s m c ps b0 b1 e args n rs Eo Dw K1 K2 Sh So (sm_embed [] s [] m Cm (Forall_nil _) (storerel_nil s m G) Fs)
   (comp_embed_fn _ _ _ Cf) L (entered_embed [] s m c args Cm En))
   as [(c' & m' & k & tS & tT & mu' & Ss & Tr & Le & Mp & Mx & Ms)|(m1 & k & tS & tT & En1 & Tr & Mp)].
 - destruct (proj1 (Rf s ce m rs k tS tT m' Eo H0 G Tr Mp) c' mu' Ss Mx Ms) as [E0 Ms0]. subst tS; cbn in Mp; subst tT.
   left. exists c', m', k. repeat split; auto; [apply srun_nil_sstar; exact Ss|eapply trun_nil_tn; exact Tr].
 - destruct (Rs s m c ps b0 b1 e args rs k tS tT m1 Eo Dw K1 K2 Sh So Cm Cf L En G Tr Mp En1) as [E0 En0].
   subst tS; cbn in Mp; subst tT.
   right. exists m1. split; [exact En0|]. eapply tn_tstar. eapply trun_nil_tn; exact Tr.
Qed.

(* ---------- the reflection with source catch-up (a proposal for review) ----------
   old_reflect_statement asks for MS at the SAME source configuration c' that MS' relates, and
   old_reflect_false refutes that through the do frame KD'_do2: MS' may relate a source that has
   not yet made its pending call of do to a machine that has already returned from it. The old
   conclusions (preservation, call_preservation and call_preservation_src) only ask for SOME source configuration that the
   source reaches silently, so old_reflect'_statement lets the source catch up: from c', some c''
   with Sstar c' c'' is MS-related to the same machine m1. The second conjunct (ends) is
   old_reflect_statement's, unchanged. old_reflect_statement and old_reflect_false are kept as
   they are.
   NOT proved; truth UNKNOWN. cx_catch_up (below, closed) shows that old_reflect_false's
   counterexample is not one to this statement: two silent source steps (the call of do, and do's
   body Y) reach the let frame, which MS relates to the machine after do's return.
   Does NOT say: anything about a state outside the old fragment or a run with IO; that MS' and
   MS relate the same pairs (they do not, cx_ms'1/cx_not_ms1); that the catch-up survives a family
   rule overlapping the old fragment without that family re-proving it (OB-JIT-LOWER-FRAGMENT). *)
Definition old_reflect'_statement : Prop := forall s c m (rs : nat -> B.jreq -> B.jres) k tS tT m1,
 env_ok rs -> MS s c m -> GvalsRel [] s m -> TRun rs k m tT m1 -> map Some tS = tT ->
 (forall c' mu', Srun c tS c' -> mext [] mu' -> MS' mu' c' m1 -> tS = [] /\ exists c'', Sstar c' c'' /\ MS s c'' m1) /\
 (Ends' [] c m1 tS -> tS = [] /\ JitLowerThm.Ends E pt sealed s c m1).

(* The old conclusions, verbatim, from the new statements and the catch-up reflection. These are
   implications between statements: each old conclusion is recovered only once its hypotheses
   (preservation'/call_preservation'/call_preservation_src' and the reflections) are proved, and
   none of them is yet. *)
Theorem preservation_old_of_new' : preservation'_statement -> old_reflect'_statement -> preservation_old_fresh_statement.
Proof.
 intros Pr Rf n s c m H Fs G. destruct env_ok_inhabited as [rs Eo].
 destruct (Pr n [] c m rs Eo (ms_embed [] s c m H (storerel_nil s m G) Fs))
   as [(c' & m' & k & tS & tT & mu' & Ss & Tr & Le & Mp & Mx & Ms)|(m1 & k & tS & tT & En & Tr & Mp)].
 - destruct (proj1 (Rf s c m rs k tS tT m' Eo H G Tr Mp) c' mu' Ss Mx Ms) as [E0 (c'' & S2 & Ms0)].
   subst tS; cbn in Mp; subst tT.
   left. exists c'', m', k. repeat split; auto;
     [eapply Sstar_trans; [apply srun_nil_sstar; exact Ss|exact S2]|eapply trun_nil_tn; exact Tr].
 - destruct (proj2 (Rf s c m rs k tS tT m1 Eo H G Tr Mp) En) as [E0 En0]. subst tS; cbn in Mp; subst tT.
   right. exists m1. split; [exact En0|]. eapply tn_tstar. eapply trun_nil_tn; exact Tr.
Qed.

Theorem call_preservation_old_of_new' : call_preservation'_statement -> old_reflect'_statement -> call_preservation_old_fresh_statement.
Proof.
 intros Cp Rf s m c ps b args n Cm Cf L En G Fs c0. destruct env_ok_inhabited as [rs Eo].
 pose proof (ms_entered s m c ps b args Cm Cf L En) as H0.
 destruct (Cp [] s m c ps b args n rs Eo (sm_embed [] s [] m Cm (Forall_nil _) (storerel_nil s m G) Fs)
   (comp_embed_fn _ _ _ Cf) L (entered_embed [] s m c args Cm En))
   as [(c' & m' & k & tS & tT & mu' & Ss & Tr & Le & Mp & Mx & Ms)|(m1 & k & tS & tT & En1 & Tr & Mp)].
 - destruct (proj1 (Rf s c0 m rs k tS tT m' Eo H0 G Tr Mp) c' mu' Ss Mx Ms) as [E0 (c'' & S2 & Ms0)].
   subst tS; cbn in Mp; subst tT.
   left. exists c'', m', k. repeat split; auto;
     [eapply Sstar_trans; [apply srun_nil_sstar; exact Ss|exact S2]|eapply trun_nil_tn; exact Tr].
 - destruct (proj2 (Rf s c0 m rs k tS tT m1 Eo H0 G Tr Mp) En1) as [E0 En0]. subst tS; cbn in Mp; subst tT.
   right. exists m1. split; [exact En0|]. eapply tn_tstar. eapply trun_nil_tn; exact Tr.
Qed.

Theorem call_preservation_src_old_of_new' : call_preservation_src'_statement -> old_reflect'_statement ->
 old_reflect_src_statement -> call_preservation_src_old_fresh_statement.
Proof.
 intros Cp Rf Rs s m c ps b0 b1 e args n Dw K1 K2 Sh So Cm Cf L En G Fs c0 ce. destruct env_ok_inhabited as [rs Eo].
 pose proof (ms_entered s m c ps e args Cm Cf L En) as H0.
 destruct (Cp [] s m c ps b0 b1 e args n rs Eo Dw K1 K2 Sh So (sm_embed [] s [] m Cm (Forall_nil _) (storerel_nil s m G) Fs)
   (comp_embed_fn _ _ _ Cf) L (entered_embed [] s m c args Cm En))
   as [(c' & m' & k & tS & tT & mu' & Ss & Tr & Le & Mp & Mx & Ms)|(m1 & k & tS & tT & En1 & Tr & Mp)].
 - destruct (proj1 (Rf s ce m rs k tS tT m' Eo H0 G Tr Mp) c' mu' Ss Mx Ms) as [E0 (c'' & S2 & Ms0)].
   subst tS; cbn in Mp; subst tT.
   left. exists c'', m', k. repeat split; auto;
     [eapply Sstar_trans; [apply srun_nil_sstar; exact Ss|exact S2]|eapply trun_nil_tn; exact Tr].
 - destruct (Rs s m c ps b0 b1 e args rs k tS tT m1 Eo Dw K1 K2 Sh So Cm Cf L En G Tr Mp En1) as [E0 En0].
   subst tS; cbn in Mp; subst tT.
   right. exists m1. split; [exact En0|]. eapply tn_tstar. eapply trun_nil_tn; exact Tr.
Qed.
(* ---------- the reflections narrowed (closed; fix round 3) ----------
   B.next is a function, so under one environment the machine has one run from m. Together with
   the PROVED old theorems (JitLowerThm.preservation and call_preservation) and, for the src
   reflection, JitKRefCompose.call_preservation_src_of_fundamental, this settles:
   - old_reflect'_silent: from a state MS relates, every run is IO-free (tS = []), so the trace
     parts of old_reflect'_statement and old_reflect_src_statement hold;
   - old_reflect'_ends: old_reflect'_statement's second conjunct (Ends' at mu = [] read back as
     JitLowerThm.Ends with the same store), unconditionally;
   - old_reflect'_iff_core: old_reflect'_statement is EQUIVALENT to old_reflect_core_statement,
     the catch-up of MS' to MS along an IO-free run (no trace, no environment). That core is the
     one part of old_reflect' NOT proved; truth UNKNOWN. With JitEmitRel's family hooks empty it is
     a property of MS' and JitEmitKont's extra frames (do, handlers, closures, frame_prim's
     primitives); a family whose rule overlaps the old fragment must re-prove it.
   - old_reflect_src_of_fundamental: old_reflect_src_statement follows from the fundamental
     property. This is a reduction, NOT a proof: its end case comes entirely from
     call_preservation_src_of_fundamental, so the src corollary adds nothing beyond that theorem.
     JitKRefFund.fundamental now proves fundamental_statement, so old_reflect_src (fix round 4,
     below) proves old_reflect_src_statement.
   - preservation_old_holds, call_preservation_old_holds and call_preservation_src_old_of_fundamental:
     the *_old_statement targets follow from the old theorems directly (the src one from
     fundamental). A sanity check that the targets of the *_old_of_new' corollaries are true; it
     says nothing about the new statements (preservation', call_preservation', call_preservation_src').
   Does NOT say: anything about a run that starts outside the old fragment; that old_reflect_core
   holds. *)

Lemma tn_trun : forall k m m1, JitLowerThm.TN E pt k m m1 -> forall rs, TRun rs k m [] m1.
Proof. intros k m m1 H; induction H; intros rs; [constructor|econstructor; [eassumption|auto]]. Qed.

Lemma sstar_srun : forall c c', Sstar c c' -> Srun c [] c'.
Proof.
 intros c c' H; induction H; [constructor|].
 unfold Srun. replace (@nil event) with (trace_of Tau ++ []) by reflexivity. econstructor; eauto.
Qed.

Lemma trun_tn_prefix : forall j m mj, JitLowerThm.TN E pt j m mj ->
 forall rs k tT m1, TRun rs k m tT m1 -> (k <= j)%nat -> tT = [].
Proof.
 intros j m mj H. induction H as [m|j m ma mj T H IH]; intros rs k tT m1 Tr Le.
 - assert (k = 0%nat) by lia. subst k. apply TRun_0 in Tr as [-> _]. reflexivity.
 - destruct k as [|k]; [apply TRun_0 in Tr as [-> _]; reflexivity|].
   unfold TS in T. inversion Tr; subst.
   + match goal with N : B.next E pt m = B.MTau _ |- _ => rewrite T in N; injection N as <- end.
     eapply IH; [eassumption|lia].
   + match goal with N : B.next E pt m = B.MIO _ _ |- _ => rewrite T in N; discriminate end.
Qed.

Lemma tn_next_tau : forall j m mj, JitLowerThm.TN E pt j m mj -> forall k m1, JitLowerThm.TN E pt k m m1 -> (k < j)%nat ->
 exists m', B.next E pt m1 = B.MTau m'.
Proof.
 intros j m mj H. induction H as [m|j m ma mj T H IH]; intros k m1 Hk Lt; [lia|].
 unfold TS in T. inversion Hk; subst; [exists ma; exact T|].
 match goal with T' : TS E pt m _, Hk' : JitLowerThm.TN E pt _ _ m1 |- _ =>
   unfold TS in T'; rewrite T in T'; injection T' as <-; apply (IH _ m1 Hk'); lia end.
Qed.

Lemma tstar_final_trun : forall m mf, TStar m mf -> forall o m2, B.next E pt mf = B.MFinal o m2 ->
 forall rs k tT m1, TRun rs k m tT m1 -> tT = [].
Proof.
 intros m mf H. induction H as [m|m ma mf T H IH]; intros o m2 F rs k tT m1 Tr.
 - destruct k as [|k]; [apply TRun_0 in Tr as [-> _]; reflexivity|].
   inversion Tr; subst; match goal with N : B.next E pt m = _ |- _ => rewrite F in N; discriminate end.
 - destruct k as [|k]; [apply TRun_0 in Tr as [-> _]; reflexivity|].
   unfold TS in T. inversion Tr; subst.
   + match goal with N : B.next E pt m = B.MTau _ |- _ => rewrite T in N; injection N as <- end.
     eapply IH; eauto.
   + match goal with N : B.next E pt m = B.MIO _ _ |- _ => rewrite T in N; discriminate end.
Qed.

Lemma tstar_final_eq : forall m a, TStar m a -> forall b, TStar m b -> forall o1 n1 o2 n2,
 B.next E pt a = B.MFinal o1 n1 -> B.next E pt b = B.MFinal o2 n2 -> a = b.
Proof.
 intros m a H. induction H as [m|m ma a T H IH]; intros b Hb o1 n1 o2 n2 Fa Fb.
 - inversion Hb; subst; [reflexivity|].
   match goal with T' : TS E pt m _ |- _ => unfold TS in T'; rewrite Fa in T'; discriminate end.
 - unfold TS in T. inversion Hb; subst; [rewrite T in Fb; discriminate|].
   match goal with T' : TS E pt m _ |- _ => unfold TS in T'; rewrite T in T'; injection T' as <- end.
   eapply IH; eauto.
Qed.

(* From a state MS relates, a run under any environment takes no IO step. *)
Theorem old_reflect'_silent : forall s c m rs k tT m1, MS s c m -> TRun rs k m tT m1 ->
 tT = [] /\ JitLowerThm.TN E pt k m m1.
Proof.
 intros s c m rs k tT m1 H Tr.
 assert (E0 : tT = []).
 { destruct (JitLowerThm.preservation E pt sealed k s c m H) as [(c' & m' & j & Ss & Tn & Le & Ms)|(mf & En & Ts)].
   - eapply trun_tn_prefix; eauto.
   - destruct (JitLowerThm.Ends_final E pt sealed s c mf En) as (o & m2 & F). eapply tstar_final_trun; eauto. }
 subst tT. split; [reflexivity|eapply trun_nil_tn; exact Tr].
Qed.

(* old_reflect'_statement's second conjunct, proved. *)
Theorem old_reflect'_ends : forall s c m rs k tS tT m1, MS s c m -> TRun rs k m tT m1 -> map Some tS = tT ->
 Ends' [] c m1 tS -> tS = [] /\ JitLowerThm.Ends E pt sealed s c m1.
Proof.
 intros s c m rs k tS tT m1 H Tr Mp En'. destruct (Ends'_final _ _ _ _ En') as (o & m2 & F).
 destruct (old_reflect'_silent s c m rs k tT m1 H Tr) as [-> Tn].
 destruct tS; [|discriminate]. split; [reflexivity|].
 destruct (JitLowerThm.preservation E pt sealed (S k) s c m H) as [(c' & m' & j & Ss & Tj & Le & Ms)|(mf & En & Ts)].
 - exfalso. destruct (tn_next_tau j m m' Tj k m1 Tn ltac:(lia)) as [m'' N]. rewrite F in N; discriminate.
 - destruct (JitLowerThm.Ends_final E pt sealed s c mf En) as (o' & m2' & F').
   assert (mf = m1) by (eapply tstar_final_eq; [exact Ts|eapply tn_tstar; exact Tn|exact F'|exact F]).
   subst mf; exact En.
Qed.

(* The one part of old_reflect'_statement not proved: MS' at mu' extending [], on a state the
   source reaches silently from an MS-related one after an IO-free bytecode run, catches up with
   MS. NOT proved; truth UNKNOWN. old_reflect'_iff_core: it is exactly as strong as
   old_reflect'_statement.
   Does NOT say: anything outside the old fragment; that MS' and MS relate the same pairs (they do
   not, cx_ms'1/cx_not_ms1). *)
Definition old_reflect_core_statement : Prop := forall s c m k m1 c' mu',
 MS s c m -> GvalsRel [] s m -> JitLowerThm.TN E pt k m m1 -> Sstar c c' -> mext [] mu' -> MS' mu' c' m1 ->
 exists c'', Sstar c' c'' /\ MS s c'' m1.

Theorem old_reflect'_of_core : old_reflect_core_statement -> old_reflect'_statement.
Proof.
 intros Co s c m rs k tS tT m1 Eo H G Tr Mp. split.
 - intros c' mu' Ss Mx Ms. destruct (old_reflect'_silent s c m rs k tT m1 H Tr) as [-> Tn].
   destruct tS; [|discriminate]. split; [reflexivity|].
   eapply Co; [exact H|exact G|exact Tn|apply srun_nil_sstar; exact Ss|exact Mx|exact Ms].
 - intros En'. eapply old_reflect'_ends; eauto.
Qed.

Theorem old_reflect_core_of' : old_reflect'_statement -> old_reflect_core_statement.
Proof.
 intros Rf s c m k m1 c' mu' H G Tn Ss Mx Ms. destruct env_ok_inhabited as [rs Eo].
 destruct (proj1 (Rf s c m rs k [] [] m1 Eo H G (tn_trun k m m1 Tn rs) eq_refl) c' mu' (sstar_srun _ _ Ss) Mx Ms)
   as [_ X]. exact X.
Qed.

Theorem old_reflect'_iff_core : old_reflect'_statement <-> old_reflect_core_statement.
Proof. split; [apply old_reflect_core_of'|apply old_reflect'_of_core]. Qed.

(* old_reflect_src_statement from the fundamental property (a reduction; see above). *)
Theorem old_reflect_src_of_fundamental : JitKRef.JitKRef.fundamental_statement sealed D -> old_reflect_src_statement.
Proof.
 intros F s m c ps b0 b1 e args rs k tS tT m1 Eo Dw K1 K2 Sh So Cm Cf L En G Tr Mp Es.
 pose proof (ms_entered s m c ps e args Cm Cf L En) as H0.
 destruct (old_reflect'_silent _ _ _ _ _ _ _ H0 Tr) as [-> Tn].
 destruct tS; [|discriminate]. split; [reflexivity|].
 destruct (EndsSrc'_final _ _ _ _ _ Es) as (o & m2 & Fn).
 pose proof (JitKRefCompose.JitKRefCompose.call_preservation_src_of_fundamental sealed D E pt F
   s m c ps b0 b1 e args (S k) Dw K1 K2 Sh So Cm Cf L En) as CP. cbv zeta in CP.
 destruct CP as [(c' & m' & j & Ss & Tj & Le & Ms)|(mf & Ef & Ts)].
 - exfalso. destruct (tn_next_tau j m m' Tj k m1 Tn ltac:(lia)) as [m'' N]. rewrite Fn in N; discriminate.
 - assert (Fm : exists o' m2', B.next E pt mf = B.MFinal o' m2') by (destruct Ef; eauto).
   destruct Fm as (o' & m2' & Ff).
   assert (mf = m1) by (eapply tstar_final_eq; [exact Ts|eapply tn_tstar; exact Tn|exact Ff|exact Fn]).
   subst mf; exact Ef.
Qed.

(* Sanity: the *_old_statement targets are true (from the old theorems; the src one from
   fundamental). Says nothing about the new statements. *)
Theorem preservation_old_holds : preservation_old_statement.
Proof. intros n s c m H _. exact (JitLowerThm.preservation E pt sealed n s c m H). Qed.

Theorem call_preservation_old_holds : call_preservation_old_statement.
Proof.
 intros s m c ps b args n Cm Cf L En _.
 exact (JitLowerThm.call_preservation E pt sealed s m c ps b args n Cm Cf L En).
Qed.

Theorem call_preservation_src_old_of_fundamental : JitKRef.JitKRef.fundamental_statement sealed D ->
 call_preservation_src_old_statement.
Proof.
 intros F s m c ps b0 b1 e args n Dw K1 K2 Sh So Cm Cf L En _.
 exact (JitKRefCompose.JitKRefCompose.call_preservation_src_of_fundamental sealed D E pt F
   s m c ps b0 b1 e args n Dw K1 K2 Sh So Cm Cf L En).
Qed.

(* ---------- old_reflect_src_statement, proved (closed) ----------
   JitKRefFund.fundamental proves JitKRef's fundamental property outright (DoD (1)), so the
   reduction old_reflect_src_of_fundamental and call_preservation_src_old_of_fundamental become
   proofs. old_reflect_src: the end case of the src reflection holds, with no hypothesis beyond its
   own premises. call_preservation_src_old_holds: the target of call_preservation_src_old_of_new'
   holds. call_preservation_src_old_of_new'': call_preservation_src_old_of_new' with its
   old_reflect_src_statement hypothesis discharged, so the src corollary waits only on
   call_preservation_src'_statement and old_reflect'_statement (equivalently old_reflect_core).
   Does NOT say: anything about call_preservation_src'_statement or old_reflect_core_statement
   (both UNKNOWN). *)
Theorem old_reflect_src : old_reflect_src_statement.
Proof. exact (old_reflect_src_of_fundamental (JitKRefFund.JitKRefFund.fundamental sealed D)). Qed.

Theorem call_preservation_src_old_holds : call_preservation_src_old_statement.
Proof. exact (call_preservation_src_old_of_fundamental (JitKRefFund.JitKRefFund.fundamental sealed D)). Qed.

Theorem call_preservation_src_old_of_new'' : call_preservation_src'_statement -> old_reflect'_statement ->
 call_preservation_src_old_fresh_statement.
Proof. intros Cp Rf. exact (call_preservation_src_old_of_new' Cp Rf old_reflect_src). Qed.
End Src.
End Inv.

(* ---------- old_reflect_statement is false (closed) ----------
   A counterexample, at E with no allocation or stack failure, the empty primitive table and no
   sealed names. The store defines the kernel's do, (defun do (X Y) Y), and every primitive. The
   machine is at the call of do in (let Z (do 1 2) Z) (call 0 1 do 2, then return slot 0), with
   1 and 2 in the window: MS relates the source, at Ret 2 with the pending call of do and the let
   frame, to it (cx_ms0, through KD_call). After two silent steps (the call, and do's return)
   the machine has returned 2 to slot 0. MS' relates the SAME source configuration to that
   machine (cx_ms'1): KD'_do2 makes the source's pending call of do transparent. MS does not
   (cx_not_ms1): its frames for a pending named call need the call instruction ahead. So the
   first conjunct of old_reflect_statement fails at c' = c, mu' = [] (old_reflect_false).
   What this says: MS' relates pairs MS does not even when the run starts in the old fragment,
   because JitEmitKont's do frames, not a family rule, overlap the old syntax (a named call of
   do). The three *_old_of_new corollaries take old_reflect_statement as a hypothesis, so they
   hold vacuously and recover nothing. How the old conclusions are to be recovered is open
   (OB-JIT-LOWER-FRAGMENT): see the ledger's review items.
   Does NOT say: anything about old_reflect_src_statement (proved separately, old_reflect_src), or that sim'_statement or any
   other new statement is false. *)
Definition cx_x : name := kw "X".
Definition cx_y : name := kw "Y".
Definition cx_z : name := kw "Z".
Definition prim_tab : list (name * fundef) := map (fun p => (of_string (prim_name p), FPrim p)) all_prims.
Lemma lookup_prim_tab_gen : forall f l, lookup f (map (fun p => (of_string (prim_name p), FPrim p)) l) =
  option_map FPrim (find (fun p => text_eqb f (of_string (prim_name p))) l).
Proof. intros f l; induction l as [|p l IH]; cbn; [reflexivity|]. destruct (text_eqb f _); auto. Qed.
Lemma lookup_prim_tab : forall f, lookup f prim_tab = option_map FPrim (prim_of_name f).
Proof. intro f. apply lookup_prim_tab_gen. Qed.
Definition cx_sg (gv : list (name * value)) : store := Store [] gv ((do_name, FUser [cx_x; cx_y] (EVar cx_y)) :: prim_tab).
Definition cx_s : store := cx_sg [].
Lemma do_not_prim : prim_of_name do_name = None.
Proof. vm_compute. reflexivity. Qed.
Lemma cx_lookup : forall gv f, lookup f (gfuns (cx_sg gv)) =
 if text_eqb f do_name then Some (FUser [cx_x; cx_y] (EVar cx_y)) else option_map FPrim (prim_of_name f).
Proof. intros gv f. unfold cx_sg. cbn [gfuns lookup]. destruct (text_eqb f do_name); [reflexivity|apply lookup_prim_tab]. Qed.

Definition cx_do : B.code := B.Code B.VNil 2 None 4 [] [B.IReturn (B.OSlot 3)] [] B.VNil.
Definition cx_r : list B.instr := [B.ICall 0 1 (B.sym_of_text do_name) 2; B.IReturn (B.OSlot 0)].
Definition cx_f : B.code := B.Code B.VNil 0 None 5 [] cx_r [] B.VNil.
Definition cx_gfun : B.tree B.val := B.tset (B.sym_of_text do_name) (B.VClo 1) B.Leaf.
Definition cx_heap : B.tree B.obj := B.tset 1 (B.OClo cx_do []) B.Leaf.
(* A machine over cx_heap is fresh when its m_next is past key 1. *)
Lemma cx_fresh : forall m, B.m_heap m = cx_heap -> (2 <= B.m_next m)%positive -> Fresh m.
Proof.
 intros m H L p Lp. rewrite H. unfold cx_heap. rewrite JitMeta.JitMeta.tget_tset_other by lia.
 apply JitMeta.JitMeta.tget_leaf.
Qed.
Definition cx_m : B.machine := B.Machine (B.tset (B.skey 3) (B.VFix 1) (B.tset (B.skey 4) (B.VFix 2) B.Leaf)) 0 cx_f cx_r
 [] [] B.VCleared cx_heap 2 B.Leaf cx_gfun B.Leaf false 0.
Definition cx_E : B.env := B.Env (fun _ => false) (fun _ => false) (fun _ => 0%Z).
Definition cx_pt : B.tree (B.prim * nat) := B.Leaf.
Definition mstep (m : B.machine) : B.machine := match B.next cx_E cx_pt m with B.MTau m' => m' | _ => m end.
Definition cx_st0 : B.tree B.val := B.tset (B.skey 3) (B.VFix 1) (B.tset (B.skey 4) (B.VFix 2) B.Leaf).
Definition cx_m1 : B.machine := B.Machine (B.tset (B.skey 0) (B.VFix 2) (B.tset (B.skey 2) (B.VClo 1) cx_st0)) 0 cx_f
 [B.IReturn (B.OSlot 0)] [] [] B.VCleared cx_heap 2 B.Leaf cx_gfun B.Leaf false 0.
Lemma cx_step1 : B.next cx_E cx_pt cx_m = B.MTau (mstep cx_m). Proof. vm_compute. reflexivity. Qed.
Lemma cx_step2 : B.next cx_E cx_pt (mstep cx_m) = B.MTau cx_m1. Proof. vm_compute. reflexivity. Qed.

Definition cx_k : list frame := [KCallArgs do_name [VNum (NInt 1)] [] []; KLet cx_z (EVar cx_z) []].
Definition cx_c : config := Cfg (Ret (VNum (NInt 2))) cx_k cx_s.

Lemma cx_comp_do : CompFn cx_do [cx_x; cx_y] (EVar cx_y).
Proof.
 exists []. eapply JitLowerRel.C_ret. eapply JitLowerRel.O_var; [vm_compute; reflexivity|vm_compute; reflexivity].
Qed.

Lemma cx_funrel : forall gv m, B.m_gfun m = cx_gfun -> B.m_heap m = cx_heap -> FunRel (cx_sg gv) m.
Proof.
 intros gv m G H. constructor.
 - intros f ps b L. rewrite cx_lookup in L. destruct (text_eqb f do_name) eqn:E.
   + apply text_eqb_eq in E; subst f. inversion L; subst. exists 1%positive, cx_do, []. rewrite G, H.
     split; [apply JitMeta.JitMeta.tget_tset_same|]. split; [apply JitMeta.JitMeta.tget_tset_same|].
     split; [reflexivity|]. split; [reflexivity|]. exact cx_comp_do.
   + destruct (prim_of_name f); discriminate.
 - intros f L l. rewrite G. rewrite cx_lookup in L. destruct (text_eqb f do_name) eqn:E; [discriminate|].
   unfold cx_gfun. destruct (Pos.eq_dec (B.sym_of_text f) (B.sym_of_text do_name)) as [P|P].
   + apply B.sym_of_text_inj in P. subst f. rewrite text_eqb_refl in E. discriminate.
   + rewrite JitMeta.JitMeta.tget_tset_other by exact P. rewrite JitMeta.JitMeta.tget_leaf. discriminate.
 - intros f p L. rewrite cx_lookup in L. destruct (text_eqb f do_name); [discriminate|].
   destruct (prim_of_name f); inversion L; reflexivity.
 - intros f p L. rewrite cx_lookup. destruct (text_eqb f do_name) eqn:E.
   + apply text_eqb_eq in E; subst f. rewrite do_not_prim in L. discriminate.
   + rewrite L. reflexivity.
Qed.

(* MS relates the source at the pending call of do to the machine at its call instruction. *)
Lemma cx_ms0g : forall gv, MS (cx_sg gv) (Cfg (Ret (VNum (NInt 2))) cx_k (cx_sg gv)) cx_m.
Proof.
 intro gv. unfold cx_k.
 eapply MS_ret with (o := B.OSlot 4) (v' := B.VFix 2) (w := fun x => 4 <= x).
 - split; [reflexivity|apply cx_funrel; reflexivity].
 - vm_compute. reflexivity.
 - constructor.
 - eapply KD_call with (g := []) (a := 1) (d := 0) (n := 2) (i := B.ICall 0 1 (B.sym_of_text do_name) 2)
     (r1 := [B.IReturn (B.OSlot 0)]) (w1 := fun _ => True).
   + exact do_not_prim.
   + reflexivity.
   + reflexivity.
   + intros x s L; discriminate.
   + intros x s L; discriminate.
   + intros x s L; discriminate.
   + apply JitLowerRel.W_nil.
   + left; reflexivity.
   + cbn. econstructor; [vm_compute; reflexivity|constructor|constructor].
   + intros a A; exact A.
   + intros a A; exact I.
   + intros a A; exact I.
   + exact I.
   + eapply KD_let with (g := []) (top := 1) (dst := DRet) (r2 := []) (w1 := fun _ => True).
     * intros x s L; discriminate.
     * intros x s L; discriminate.
     * intros x s L; discriminate.
     * vm_compute; reflexivity.
     * eapply JitLowerRel.C_ret. eapply JitLowerRel.O_var; [vm_compute; reflexivity|vm_compute; reflexivity].
     * intros a A; exact A.
     * intros a A; exact I.
     * apply KC_ret; [intros a A; cbn; lia|constructor].
Qed.
Lemma cx_ms0 : MS cx_s cx_c cx_m.
Proof. exact (cx_ms0g []). Qed.


Lemma cx_sm1 : SM [] cx_s cx_k cx_m1.
Proof.
 split.
 - constructor.
   + exact pbij_nil.
   + intros l p I; destruct I.
   + split; [intros x v L; discriminate|intros x _ v' T; cbn in T; rewrite JitMeta.JitMeta.tget_leaf in T; discriminate].
   + apply funrel_embed. apply cx_funrel; reflexivity.
   + apply cx_fresh; [reflexivity|cbn; lia].
 - unfold HK. cbn. constructor.
Qed.

(* MS' relates the same source configuration to the machine after do has returned: the source's
   pending call of do is transparent (KD'_do2). *)
Lemma cx_ms'1 : MS' [] cx_c cx_m1.
Proof.
 unfold cx_c.
 eapply MS'_ret with (cv := []) (caps := []) (o := B.OSlot 0) (v' := B.VFix 2) (w := fun _ => True).
 - exact cx_sm1.
 - vm_compute. reflexivity.
 - constructor.
 - left; reflexivity.
 - left; reflexivity.
 - unfold cx_k. apply KD'_do2.
   + exists cx_x, cx_y. split; [vm_compute; discriminate|reflexivity].
   + eapply KD'_let with (g := []) (top := 1) (dst := DRet) (r2 := []) (w1 := fun _ => True).
     * split; [intros x s L; discriminate|intros i x N; destruct i; discriminate].
     * intros x s L; discriminate.
     * intros x s L; discriminate.
     * vm_compute; reflexivity.
     * eapply C_ret. eapply O_var; [vm_compute; reflexivity|vm_compute; reflexivity].
     * intros a A; exact A.
     * intros a A; exact I.
     * apply KC'_ret; [intros a A; cbn; lia|constructor].
Qed.

(* MS does not: its only frame for a pending named call is KD_call (or KD_tail), which needs the
   call instruction still ahead, and the machine has already returned. *)
Lemma cx_not_ms1 : ~ MS cx_s cx_c cx_m1.
Proof.
 intro H. inversion H as [| | |v v' o k w m Cm Ro Vr Kd E1 E2]; subst. cbn in Kd. unfold cx_k in Kd.
 inversion Kd; subst.
 - (* KD_ret *) match goal with Hr : RK _ _ _ _ |- _ => inversion Hr end.
 - (* KD_prim *) match goal with P : prim_of_name do_name = Some _ |- _ => rewrite do_not_prim in P; discriminate end.
 - (* KD_call *) match goal with W : JitLowerRel.CompW _ _ _ [] _ _ |- _ => inversion W; subst end.
   match goal with C : call_instr _ _ _ _ _ |- _ => destruct C; discriminate end.
 - (* KD_tail *) match goal with W : JitLowerRel.CompTA _ _ _ _ [] _ _ _ |- _ => inversion W; subst end.
   match goal with Hm : map _ ?ms ++ _ = _ |- _ => destruct ms; cbn in Hm; inversion Hm; subst end.
   match goal with C : tail_instr _ _ _ _ |- _ => destruct C; discriminate end.
Qed.

Lemma cx_trun : forall rs, TRun cx_E cx_pt rs 2 cx_m [] cx_m1.
Proof.
 intro rs. econstructor; [exact cx_step1|]. econstructor; [exact cx_step2|]. constructor.
Qed.

Theorem old_reflect_false : ~ old_reflect_statement cx_E cx_pt [].
Proof.
 intro R. destruct env_ok_inhabited as [rs Eo].
 assert (G : GvalsRel [] cx_s cx_m).
 { split; [intros x v L; discriminate|intros x _ v' T; cbn in T; rewrite JitMeta.JitMeta.tget_leaf in T; discriminate]. }
 destruct (R cx_s cx_c cx_m rs 2%nat [] [] cx_m1 Eo cx_ms0 G (cx_trun rs) eq_refl) as [R1 _].
 destruct (R1 cx_c [] (star_refl _ _ _) (conj (incl_refl _) pbij_nil) cx_ms'1) as [_ M].
 exact (cx_not_ms1 M).
Qed.
(* GvalsRel is not implied by the old theorems' premises: MS holds, and MS' at no mu, when the
   store binds a global the machine does not. *)
Example gvals_needed : let s := cx_sg [(kw "g", VNum (NInt 0))] in
 MS s (Cfg (Ret (VNum (NInt 2))) cx_k s) cx_m /\ forall mu, ~ MS' mu (Cfg (Ret (VNum (NInt 2))) cx_k s) cx_m.
Proof.
 cbv zeta. split; [apply cx_ms0g|].
 intros mu H. inversion H; subst.
 match goal with Sm : SM _ _ _ _ |- _ => destruct Sm as [[_ _ [G1 _] _] _] end.
 assert (L : lookup (kw "g") (gvals (cx_sg [(kw "g", VNum (NInt 0))])) = Some (VNum (NInt 0)))
   by (unfold cx_sg; cbn [gvals lookup]; rewrite text_eqb_refl; reflexivity).
 destruct (G1 _ _ L) as (v1 & T & _).
 cbn in T. rewrite JitMeta.JitMeta.tget_leaf in T. discriminate.
Qed.


(* old_reflect_false's counterexample is not one to old_reflect'_statement: from cx_c (the
   source at the pending call of do, which MS' relates to cx_m1, the machine after do's return),
   two silent source steps reach the let frame, and MS relates that configuration to cx_m1.
   Does NOT say: that old_reflect'_statement holds (UNKNOWN). *)
Definition cx_c2 : config := Cfg (Ret (VNum (NInt 2))) [KLet cx_z (EVar cx_z) []] cx_s.
Lemma cx_src_catch_up : JitLowerStep.Sstar [] cx_c cx_c2.
Proof.
 eapply JitLowerStep.S1; [vm_compute; reflexivity|].
 eapply JitLowerStep.S1'. vm_compute. reflexivity.
Qed.
Lemma cx_ms2 : MS cx_s cx_c2 cx_m1.
Proof.
 unfold cx_c2.
 eapply MS_ret with (o := B.OSlot 0) (v' := B.VFix 2) (w := fun _ => True).
 - split; [reflexivity|apply cx_funrel; reflexivity].
 - vm_compute. reflexivity.
 - constructor.
 - eapply KD_let with (g := []) (top := 1) (dst := DRet) (r2 := []) (w1 := fun _ => True).
   + intros x s L; discriminate.
   + intros x s L; discriminate.
   + intros x s L; discriminate.
   + vm_compute; reflexivity.
   + eapply JitLowerRel.C_ret. eapply JitLowerRel.O_var; [vm_compute; reflexivity|vm_compute; reflexivity].
   + intros a A; exact A.
   + intros a A; exact I.
   + apply KC_ret; [intros a A; cbn; lia|constructor].
Qed.
Example cx_catch_up : MS' [] cx_c cx_m1 /\ ~ MS cx_s cx_c cx_m1 /\
 exists c'', JitLowerStep.Sstar [] cx_c c'' /\ MS cx_s c'' cx_m1.
Proof. split; [exact cx_ms'1|]. split; [exact cx_not_ms1|]. exists cx_c2. split; [exact cx_src_catch_up|exact cx_ms2]. Qed.

(* ---------- the frame narrowing: primitive-level divergences (closed) ----------
   Each Example below is one hand-argued reason JitEmitKont.frame_prim, the window bound or
   env_ok narrows the statements, checked in Rocq at the primitive (or call) level: the source
   rule (KLPort.prim_rule_r under jit_rules, or apply_value_r) against the bytecode's
   (JitBytecode.prim_step, enter, or an IO continuation) on related arguments. They are
   divergences, NOT refutations of sim'_statement: each says that a frame (or response) admitting
   the case would need a different statement or a source/bytecode decision.
   - absvector 2^48: the source allocates, the bytecode raises (dv_absvector_src/_byt).
   - error-to-string: the source answers "error", the bytecode the exception's text (dv_ets_rel, dv_ets_src, dv_ets_byt).
   - open: the bytecode's request prefixes *home-directory*; no translated event equals the
     source's (dv_open).
   - close, read-byte and write-byte on a closed stream: the source asks the environment, the
     bytecode answers or raises without a request (dv_close, dv_read_closed, dv_write_closed).
   - = on two NaNs: the bytecode is stuck, the source answers (dv_eq_nan). = on two distinct
     cyclic vectors: the source goes wrong (OWrong) and the bytecode is stuck (RCyclic), so it is
     not a disagreement on an answer, but a state Out' has no case for (dv_eq_cycle, at the end
     of this file); on one cyclic vector both answer true (dv_eq_cycle_same).
   - a dynamic call of two arguments on a one-parameter closure, the two closures VRh-related
     (dv_window_rel): the source over-applies, the bytecode raises (dv_window).
   - an IO failure: the bytecode's continuation resumes the machine with no result, the source
     throws; resp_ok excludes the answer (dv_io_fail). This is what env_ok is for.
   - GvalsRel in the *_old statements: MS holds at a store with a bound global the machine does
     not have, and no MS' does, at any mu (gvals_needed). It is not implied by the old premises.
   get-time is not excluded: get_time_agree proves its request, answer and result agree. *)
Definition dv_E : B.env := B.Env (fun _ => false) (fun _ => false) (fun _ => 0%Z).
Definition dv_s : store := Store [] [] [].
Definition dv_code1 : B.code := B.Code B.VNil 1 None 3 [] [B.IReturn (B.OSlot 2)] [] B.VNil.
Definition dv_heap : B.tree B.obj :=
 B.tset 1 (B.OExn (B.t "hd: 1 is not a pair") (B.VFix 1)) (B.tset 2 (B.OStream 5 B.SIn false)
  (B.tset 3 (B.OClo dv_code1 []) (B.tset 4 (B.OStream 6 B.SOut false) B.Leaf))).
Definition dv_m (gval : B.tree B.val) : B.machine :=
 B.Machine B.Leaf 0 dv_code1 [] [] [] B.VCleared dv_heap 4 gval B.Leaf B.Leaf false 0.
Definition dv_mm := dv_m B.Leaf.
Definition src (p : prim) (args : list value) : presult := prim_rule_r (jit_rules []) jit_profile p args dv_s.
Definition byt (m : B.machine) (q : B.prim) (args : list B.val) : B.move := B.prim_step dv_E B.Leaf m 0 q args.

(* absvector of 2^48 *)
Example dv_absvector_src : exists s', src PAbsvector [VNum (NInt 281474976710656)] = PDone (ORet (VVec 0) s').
Proof. eexists. unfold src, prim_rule_r, prim_rule, rule_absvector. cbn [heap dv_s]. reflexivity. Qed.
Example dv_absvector_byt : exists l m', byt dv_mm B.PAbsvector [B.VFix 281474976710656] = B.MFinal (B.FError (B.VExn l)) m'.
Proof. vm_compute. eauto. Qed.

(* error-to-string on an exception the bytecode raised: the source answers sys_message's text. *)
Example dv_ets_rel : VRh [] dv_heap (VExn (XPrim PHd)) (B.VExn 1).
Proof. econstructor; [reflexivity|exact I]. Qed.
Example dv_ets_src : src PErrorToString [VExn (XPrim PHd)] = PDone (ORet (VStr (of_string "error")) dv_s).
Proof. vm_compute. reflexivity. Qed.
Example dv_ets_byt : exists t, byt dv_mm B.PErrorToString [B.VExn 1] = B.ret_to (B.set_rest dv_mm []) 0 (B.VStr t) /\ t <> of_string "error".
Proof. vm_compute. eexists; split; [reflexivity|discriminate]. Qed.

(* open: the bytecode prefixes *home-directory*. *)
Definition dv_home : B.tree B.val := B.tset B.S__home_directory_ (B.VStr (B.t "/h/")) B.Leaf.
Example dv_open : exists f kk, src POpen [VStr (of_string "a"); VSym (of_string "in")] = PIO (QOpen (of_string "a") DIn) f /\
 byt (dv_m dv_home) B.POpen [B.VStr (B.t "a"); B.VSym B.S_in] = B.MIO (B.JOpen (B.t "/h/a") B.SIn) kk /\
 forall r e, ev_of (B.JOpen (B.t "/h/a") B.SIn) r = Some e -> forall r', e <> EvIO (QOpen (of_string "a") DIn) r'.
Proof.
 do 2 eexists. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
 intros r e E r' H; subst e. destruct r; cbn in E; inversion E; vm_compute in *; congruence.
Qed.

(* close on a closed stream: the source asks the environment, the bytecode does not. *)
Example dv_close_rel : VRh [] dv_heap (VStream 5) (B.VStream 2).
Proof. econstructor; reflexivity. Qed.
Example dv_close : (exists f, src PClose [VStream 5] = PIO (QClose 5) f) /\
 byt dv_mm B.PClose [B.VStream 2] = B.ret_to (B.set_rest dv_mm []) 0 B.VNil.
Proof. split; [eexists; vm_compute; reflexivity|vm_compute; reflexivity]. Qed.
Example dv_read_closed : (exists f, src PReadByte [VStream 5] = PIO (QRead 5 1) f) /\
 exists l m', byt dv_mm B.PReadByte [B.VStream 2] = B.MFinal (B.FError (B.VExn l)) m'.
Proof. split; [eexists; vm_compute; reflexivity|vm_compute; eauto]. Qed.

(* = on two NaNs: the bytecode is stuck, the source answers. *)
Definition dv_nan : N := 9221120237041090560.
Example dv_eq_nan : (exists b, src PEqual [VNum (NFloat dv_nan); VNum (NFloat dv_nan)] = PDone (ORet (VBool b) dv_s)) /\
 byt dv_mm B.PEq [B.VReal dv_nan; B.VReal dv_nan] = B.MStuck B.RIdentity.
Proof. split; [eexists; vm_compute; reflexivity|vm_compute; reflexivity]. Qed.

(* A dynamic call of a one-parameter closure with two arguments, on related closures (identity
   cell 0 through mu = [(0, 3)]): the source over-applies, the bytecode's call raises. *)
Definition dv_rho : lenv := [(id_key, VVec 0)].
Example dv_window_rel : VRh [(0%nat, 3%positive)] dv_heap (VLam (kw "X") (EVar (kw "X")) dv_rho) (B.VClo 3).
Proof.
 eapply VRh_lam with (nc := dv_code1) (caps := []) (cv := []) (l0 := 0%nat).
 - reflexivity.
 - split; [reflexivity|]. split; [reflexivity|]. exists [].
   eapply C_ret. eapply O_var; vm_compute; reflexivity.
 - reflexivity.
 - left; reflexivity.
 - reflexivity.
 - intros i y N. destruct i; discriminate.
Qed.
Example dv_window : apply_value_r (jit_rules []) jit_profile (VLam (kw "X") (EVar (kw "X")) dv_rho) [VNum (NInt 1); VNum (NInt 2)] [] dv_s =
 MTau (Cfg (Eval ((kw "X", VNum (NInt 1)) :: dv_rho) (EVar (kw "X"))) [KApply [VNum (NInt 2)]] dv_s) /\
 exists l m', B.enter dv_E dv_mm (B.VClo 3) 2 B.Leaf 0 [] = B.MFinal (B.FError (B.VExn l)) m'.
Proof. split; [reflexivity|vm_compute; eauto]. Qed.

(* write-byte on a closed output stream: the source asks the environment, the bytecode raises. *)
Example dv_write_closed_rel : VRh [] dv_heap (VStream 6) (B.VStream 4).
Proof. econstructor; reflexivity. Qed.
Example dv_write_closed : (exists f, src PWriteByte [VNum (NInt 65); VStream 6] = PIO (QWrite 6 [65]) f) /\
 exists l m', byt dv_mm B.PWriteByte [B.VFix 65; B.VStream 4] = B.MFinal (B.FError (B.VExn l)) m'.
Proof. split; [eexists; vm_compute; reflexivity|vm_compute; eauto]. Qed.


(* An IO failure with no handler: the bytecode's continuation resumes the machine without a
   result, while the source throws. *)
Example dv_io_fail :
 match src PGetTime [VSym (of_string "run")] with
 | PIO q f => q = QTime (of_string "run") /\ f (RFailed (EOther 0)) = OThrow (XIO (EOther 0)) | _ => False end /\
 match byt dv_mm B.PGetTime [B.VSym B.S_run] with
 | B.MIO q kk => q = B.JTime true /\ kk B.JFailed = B.set_rest dv_mm [] | _ => False end /\
 ~ resp_ok (B.JTime true) B.JFailed.
Proof. split; [vm_compute; split; reflexivity|]. split; [vm_compute; split; reflexivity|]. cbn. auto. Qed.
(* ---------- env_ok is necessary for preservation'_statement (closed) ----------
   dv_io_fail is primitive-level. env_ok_needed is statement-level: preservation_noenv_statement
   (preservation'_statement without env_ok rs) is FALSE. MS' relates the source at get-time's frame
   (run evaluated, the call pending: KD'_prim, then KD'_ret) to the machine at its
   (get-time run) instruction (gt_ms). The machine's first step asks the clock (gt_next). Under an
   environment whose first answer ev_of does not translate (JFailed, an IO failure; or a clock
   reading of 2^64, outside resp_ok's 64 bits), every run of one step or more starts with None
   (gt_trun_none), which no source trace maps to, and the machine is not final at step 0. So
   neither disjunct holds at n = 1 (noenv_false_at), and env_ok_needed and resp_ok_bound_needed
   instantiate it. The call statements (call_preservation', call_preservation_src') are analogous;
   NOT proved here.
   Does NOT say: that preservation'_statement (with env_ok) is true (UNKNOWN); anything about
   which environment the pinned binary's runtime gives (env_ok is an assumption on the
   environment, not derived from the pin). *)
Definition gt_name : name := of_string "get-time".
Definition gt_r : list B.instr := [B.IPrim 0 B.PGetTime [B.OSlot 2]; B.IReturn (B.OSlot 0)].
Definition gt_f : B.code := B.Code B.VNil 0 None 5 [] gt_r [] B.VNil.
Definition gt_st : B.tree B.val := B.tset (B.skey 2) (B.VSym (B.sym_of_text (of_string "run"))) B.Leaf.
Definition gt_m : B.machine := B.Machine gt_st 0 gt_f gt_r [] [] B.VCleared cx_heap 2 B.Leaf cx_gfun B.Leaf false 0.
Definition gt_k : list frame := [KCallArgs gt_name [] [] []].
Definition gt_c : config := Cfg (Ret (VSym (of_string "run"))) gt_k cx_s.

Lemma gt_sm : SM [] cx_s gt_k gt_m.
Proof.
 split.
 - constructor.
   + exact pbij_nil.
   + intros l p I; destruct I.
   + split; [intros x v L; discriminate|intros x _ v' T; cbn in T; rewrite JitMeta.JitMeta.tget_leaf in T; discriminate].
   + apply funrel_embed. apply cx_funrel; reflexivity.
   + apply cx_fresh; [reflexivity|cbn; lia].
 - unfold HK. cbn. constructor.
Qed.

Lemma gt_ms : MS' [] gt_c gt_m.
Proof.
 unfold gt_c.
 eapply MS'_ret with (cv := []) (caps := []) (o := B.OSlot 2) (v' := B.VSym (B.sym_of_text (of_string "run")))
   (w := fun _ => True).
 - exact gt_sm.
 - vm_compute. reflexivity.
 - constructor.
 - left; reflexivity.
 - left; reflexivity.
 - unfold gt_k.
   eapply KD'_prim with (p := PGetTime) (g := []) (top := 3) (ops := []) (dops := []) (d := 0)
     (r1 := [B.IReturn (B.OSlot 0)]) (w1 := fun _ => True).
   + vm_compute; reflexivity.
   + reflexivity.
   + reflexivity.
   + split; [intros x s L; discriminate|intros i x N; destruct i; discriminate].
   + intros x s L; discriminate.
   + intros x s L; discriminate.
   + apply Os_nil.
   + vm_compute; reflexivity.
   + constructor.
   + constructor.
   + constructor.
   + cbn. lia.
   + intros a A; exact A.
   + intros a A; exact I.
   + exact I.
   + apply KD'_ret; [intros a A; cbn; lia|constructor].
Qed.

Lemma gt_next : exists kk, B.next cx_E cx_pt gt_m = B.MIO (B.JTime true) kk.
Proof. eexists. vm_compute. reflexivity. Qed.

Lemma gt_trun_none : forall rs, ev_of (B.JTime true) (rs O (B.JTime true)) = None ->
 forall k tT m', TRun cx_E cx_pt rs (S k) gt_m tT m' -> exists t, tT = None :: t.
Proof.
 intros rs Hn k tT m' Tr. destruct gt_next as [kk Nx]. inversion Tr; subst.
 - match goal with N : B.next _ _ gt_m = B.MTau _ |- _ => rewrite Nx in N; discriminate end.
 - match goal with N : B.next _ _ gt_m = B.MIO _ _ |- _ => rewrite Nx in N; injection N as <- _ end.
   rewrite Hn. eauto.
Qed.

Theorem noenv_false_at : forall rs, ev_of (B.JTime true) (rs O (B.JTime true)) = None ->
 ~ preservation_noenv_statement cx_E cx_pt [].
Proof.
 intros rs Hn P. destruct (P 1%nat [] gt_c gt_m rs gt_ms)
   as [(c' & m' & k & tS & tT & mu' & _ & Tr & Le & Mp & _)|(m1 & k & tS & tT & En & Tr & Mp)].
 - destruct k as [|k]; [lia|]. destruct (gt_trun_none rs Hn k tT m' Tr) as [t ->].
   destruct tS; discriminate.
 - destruct k as [|k].
   + apply TRun_0 in Tr as [_ ->]. apply Ends'_final in En. destruct En as (o & m2 & F).
     destruct gt_next as [kk Nx]. rewrite Nx in F. discriminate.
   + destruct (gt_trun_none rs Hn k tT m1 Tr) as [t ->]. destruct tS; discriminate.
Qed.

Definition rs_failed : nat -> B.jreq -> B.jres := fun _ _ => B.JFailed.
Definition rs_time64 : nat -> B.jreq -> B.jres := fun _ _ => B.JTimeIs 18446744073709551616.

Theorem env_ok_needed : ~ preservation_noenv_statement cx_E cx_pt [].
Proof. exact (noenv_false_at rs_failed eq_refl). Qed.

(* resp_ok's 64-bit bound on a clock reading is needed too: the same refutation at an environment
   answering 2^64, which ev_of does not translate; neither environment is env_ok. *)
Theorem resp_ok_bound_needed : ~ preservation_noenv_statement cx_E cx_pt [] /\
 ~ env_ok rs_time64 /\ ~ env_ok rs_failed.
Proof.
 split; [exact (noenv_false_at rs_time64 ltac:(vm_compute; reflexivity))|]. split.
 - intro H. specialize (H O (B.JTime true)). cbn in H. lia.
 - intro H. specialize (H O (B.JTime true)). exact H.
Qed.

(* = on two distinct cyclic vectors (each one's only cell holds the other), related through
   mu = [(0, 5); (1, 6)]: the source goes wrong (OWrong equality-undefined, its depth bound
   exhausted), the bytecode is stuck (RCyclic, its fuel exhausted). Neither side answers, so this
   is NOT a disagreement on an answer; it is a state Out' has no case for (neither side steps), so
   a frame admitting = here would need the statements to say what happens when the source goes
   wrong. On the same cyclic vector both answer true (dv_eq_cycle_same). *)
Definition cy_s : store := Store [[VVec 1]; [VVec 0]] [] [].
Definition cy_heap : B.tree B.obj := B.tset 5 (B.OVec [B.VVec 6]) (B.tset 6 (B.OVec [B.VVec 5]) B.Leaf).
Definition cy_m : B.machine := B.Machine B.Leaf 0 dv_code1 [] [] [] B.VCleared cy_heap 6 B.Leaf B.Leaf B.Leaf false 0.
Example dv_eq_cycle_rel : VRh [(0%nat, 5%positive); (1%nat, 6%positive)] cy_heap (VVec 0) (B.VVec 5) /\
 VRh [(0%nat, 5%positive); (1%nat, 6%positive)] cy_heap (VVec 1) (B.VVec 6).
Proof. split; econstructor; [left; reflexivity|reflexivity|right; left; reflexivity|reflexivity]. Qed.
Example dv_eq_cycle : (exists w, prim_rule_r (jit_rules []) jit_profile PEqual [VVec 0; VVec 1] cy_s = PDone (OWrong w)) /\
 B.prim_step dv_E B.Leaf cy_m 0 B.PEq [B.VVec 5; B.VVec 6] = B.MStuck B.RCyclic.
Proof. split; [eexists; vm_compute; reflexivity|vm_compute; reflexivity]. Qed.
Example dv_eq_cycle_same : prim_rule_r (jit_rules []) jit_profile PEqual [VVec 0; VVec 0] cy_s = PDone (ORet (VBool true) cy_s) /\
 exists m', B.prim_step dv_E B.Leaf cy_m 0 B.PEq [B.VVec 5; B.VVec 5] = B.MTau m' /\
   slotv (B.m_stack m') 0 = Some (B.VBool true).
Proof. split; [vm_compute; reflexivity|eexists; split; [vm_compute; reflexivity|vm_compute; reflexivity]]. Qed.
End JitEmitInv.
