"""Shen/JIT lane mutants; Rocq decides (each must be refused).

ShenJitAgreedRange, ShenJitAgreedArity, ShenJitAgreedWrites, ShenJitAgreedIdentity: an option of
  agreed_rules that isn't what KLSemantics does. next_r_agreed must fail.
ShenJitAgreedPortPrim: agreed_rules gives shen-jit.write-bytes a port primitive, so a call of it
  no longer raises XUndefinedFun. next_r_agreed must fail.
ShenJitPortPrimsWired: jit_rules takes the proposed (hash-free) port primitives before Reuben's decision.
  jit_port_prims_off must fail.
ShenJitClosureIdentity: closures that always compare equal. closure_identity must fail.
ShenJitNoOverflow: no integer range in jit_rules. jit_overflow_raises must fail.
ShenJitRoundedCompare: comparison through a double, as before 0.3. jit_compare_exact must fail.
ShenJitByteChars: n->string takes only 0 to 255, as before 0.6. jit_byte_strings must fail.
ShenJitAgreedChars: agreed_rules' n->string skips the scalar-value check. rule_n_to_string_agreed must fail.
ShenJitWriteBytesFrom: write_bytes_io claims the bytes are taken from 0, not from I. It must fail.
ShenJitReadErrorIgnored: read_byte_error_raises claims a read error gives -1, as before 0.6. It must fail.
ShenJitUncheckedWrites: jit_rules ignores a failed write, as before 0.4. jit_writes_checked must fail.
ShenJitNoSealing: defun ignores the sealed set. jit_defun_sealed_refused must fail.
ShenJitLowerWrongPrim: + related to the bytecode's -. p_add must fail.
ShenJitLowerCheckMove: the checker accepts a move from any slot. chk_sound must fail.
ShenJitLowerCheckLabel: the checker skips the else label of an if. chk_sound must fail.
ShenJitLowerCheckConst: the checker accepts any integer constant. vrb_sound must fail.
ShenJitLowerChainSlot: the checker's cons chain reads any slot, not the one the tail went to.
  chain_tail_ok must fail.
ShenJitLowerChainConst: the checker's cons chain takes any constant as the head. chain_tail_ok
  must fail.
ShenJitLowerEndsDecoupled: Ends's E_ok binds its own final machine and ignores the machine
  parameter, as Ends did before the end case was tied to the run, so the machine the run reaches
  need not be the one that returns. Ends_final must fail.
ShenJitEquivEndsSameStore: EndsSrc's ok case claims the source ends in the starting store itself,
  which b0's one-sided closure cells make false. call_preservation_src_of_fundamental must fail.
ShenJitEquivAdequacyStrict: adequacy claims the source's final store is the target's. b0 and e
  allocate different cells, so adequacy_of_fundamental must fail.
ShenJitEquivComposeLeft: composing two worlds keeps the first and drops the second, so the composed
  world no longer relates the final stores. In_compose, on which GStore_trans rests, must fail.
  Since K00 these three statements are in rocq/JitKRef.v and their proofs in JitKRefGround.v and
  JitKRefCompose.v; the runner compiles one file, so each mutant is the chain of files
  (mutate_chain), the first one mutated.
ShenJitLowerEqPair: = agrees against a pair constant, which can hold a NaN. eq_core must fail.
ShenJitLowerEqNaN: = agrees against any real constant, NaN included. eq_core must fail
  (OB-JIT-NAN-IDENTITY).
ShenJitLowerCheckEqGuard: the checker admits = without a safe constant operand. chk_sound must fail.
ShenJitSymBase256: symbols as the name's elements in base 256, as before, which merges [1;1] with
  [65537]. text_of_sym_of_text must fail.
ShenJitEqStepNotLeast: least_true_pointers without its 'least d' premise: a true pair at any budget
  need not have identical pointers. least_true_pointers must fail.
ShenJitWalkNoTrans: the walk bound's section drops transitivity of number equality, so leaf
  agreement is no longer a PER. lag_trans must fail.
ShenJitWalkTolInstance: the statement walk_bound_needs_trans refutes now carries the transitivity
  hypothesis, i.e. it is walk_bound itself. Instantiating it with JitEqBudget's tolerance profile
  on h5 needs a transitivity proof tol does not have, so walk_bound_needs_trans must fail.
ShenJitWalkPrefixAbove: the order on stop paths puts a prefix above its extensions, which breaks
  the threshold equivalence's monotonicity. ltl_total must fail.
ShenJitEqCoreNoTrans: the assembly of the = budget core drops transitivity of number equality
  (eq_budget_refuted shows the budget statement false without it), so the base case walk_bound
  cannot be applied. core_settled, and with it eq_core, must fail.
ShenJitEqCoreNoClosure: eq_budget_closed_statement without the S-closure hypothesis
  (closed_in h cs replaced by True): the cells of cs may point outside cs. eq_budget_closed must fail.
ShenJitKRefKRelStrict: KRel_with quantifies over j < k instead of j <= k, so a continuation is no
  longer related at its own index. Built as JitKRef.v + JitKRefGround.v + JitKRefBase.v; rejected.
ShenJitKRefDefunSealed: jit_rules' defun_allowed admits sealed names. The single-file mutant is
  JitProfile.v, so jit_defun_fixed_refused rejects it first; with JitProfile's two refusal theorems
  deleted (a throwaway build), sealed_step (JitKRefBase) fails on the same option.
ShenJitKRefLamNoSameId: VBody's VLam clause without same_id, so two related lambdas need not have
  corresponding identities. Built as JitKRef.v + JitKRefGround.v + JitKRefBase.v + JitKRefCompatClo.v;
  rejected first by VBody_ground (JitKRefGround.v): = on closures compares identities, so the ground
  relation needs same_id. JitKRefCompatClo's lemmas only establish same_id (lam_core), never use it.
ShenJitKRefAbsvectorNoWext: absvector's result is claimed at the same world w, without the pair of new
  locations. The new vector is then related to nothing (its locations are fresh on both sides), so
  absvector_param (JitKRefPrim) must fail.
ShenJitKRefEqBudgetFree: the = case compares the two sides at their raw budgets S (length heap), which
  differ by the one-sided cells, without eq_budget_closed moving each to S (length w). The lockstep
  walk eq_lock is at one budget, so kl_eq_rel_from (JitKRefPrim) must fail. The statement itself is
  true: this is a rejected proof, showing the = case rests on eq_budget_closed.
ShenJitEmitRuleOpaque: a family's *_all lemma made opaque (Qed). JitEmitRel's hand-written Comp_ind'
  recurses through it, so the guard checker refuses Comp_ind' (mutate_chain over the rule file and
  JitEmitRel).
ShenJitEmitEmbedCaptures: JitEmitRel's copy of C_move asks for no captures (cv = []), in the
  constructor and in Comp_ind''s case alike. comp_embed must fail: a JitLowerRel move embeds at any cv.
ShenJitEmitNestSwap: the non-empty dummy rule of JitEmitNestTest ends with its code lists swapped.
  suffix, proved by the dummy's Comp_ind' through the nested premises, must fail.
ShenJitEmitTrapNoHandler: KD'_trap no longer consumes a handler. trap_has_handler must fail.
ShenJitEmitPmapx: pmapx relates + to the bytecode's -. pmapx_pmap must fail.
ShenJitEmitVRhPartial: VRh relates a partial application to a closure. VRh_no_partial must fail.
ShenJitEmitEndsDecoupled: Ends''s E'_ok binds its own final machine, as ShenJitLowerEndsDecoupled
  does for Ends. Ends'_final must fail.
ShenJitEmitSMNonEmpty: SM asks for a non-empty partial bijection, which StoreRel does not give (the
  old fragment at mu = [] has none). sm_embed (and ms_embed) must fail.
ShenJitEmitFrameEqGuard: frame_prim drops JitLowerRel's guard on =, so a frame admits = on two NaNs.
  frame_prim_pmap must fail.
ShenJitEmitTRunZero: a run of 0 steps may end at any machine. TRun_0 must fail.
ShenJitEmitSimCRest, ShenJitEmitSimTRest, ShenJitEmitSimORest: SimC/SimT/SimO no longer ask the
  machine to be at the derivation's code position. SimC_of_sim' (SimT_, SimO_) must fail.
ShenJitEmitSimSDrop: SimS's cons case drops the head operand. SimS_of_sim' must fail.
ShenJitEmitSimWSlot: SimW's element IH is at s, not s + 1, where CompW evaluates it. SimW_of_sim'
  must fail.
ShenJitEmitSimAKill: SimA's direct case keeps the environment, where CompTA kills slot s.
  SimA_of_sim' must fail.
ShenJitEmitMSRetCapture: MS'_ret asks for captures, which no old return state has. ms_embed must
  fail.
ShenJitEmitOutRaiseNoHK: O'_raise relates the store only (SMs), not the handlers (SM's HK), so the
  raise may leave the machine stuck on a missing label. Out'_not_stuck must fail.
ShenJitEmitEndsSrcDecoupled: EndsSrc''s ok case binds its own final machine. EndsSrc'_final must
  fail.
ShenJitEmitHKTwice: HK asks two handlers per KTrap frame. HK_length must fail.
ShenJitEmitGvalsCleared: GvalsRel lets a bound global be cleared in the machine, where value raises.
  value_bound must fail.
ShenJitEmitDoSame: DoOK lets do's two parameters be the same name, so do returns its first argument.
  do_body_second must fail.
ShenJitEmitFunRelCaps: FunRel' asks a function's closure to have no captures, which the old
  invariant does not carry. funrel_embed (and sm_embed) must fail.
ShenJitEmitTimeRefused: resp_ok admits no clock answer, so no environment is well formed and every
  statement under env_ok is vacuous. env_ok_inhabited must fail.
ShenJitEmitEvOfTime: ev_of translates no clock answer, as before the get-time counterexample.
  ev_of_time must fail.
ShenJitEmitStoreRelNonEmpty: StoreRel asks for a non-empty bijection, which the old fragment at
  mu = [] has not. storerel_nil must fail.
ShenJitEmitReflectTrace: old_reflect_statement no longer says the old-fragment run takes no source
  IO (True in place of tS = []), so its conclusion is no silent run. preservation_old_of_new must
  fail (at subst tS).
ShenJitEmitReflectSrcTrace: the same for old_reflect_src_statement. call_preservation_src_old_of_new
  must fail (at subst tS).
ShenJitEmitOldGvalsDropped: preservation_old_statement's GvalsRel [] s m premise becomes True. The
  proof builds StoreRel [] s m from it for ms_embed, so preservation_old_of_new must fail (at
  storerel_nil).
ShenJitEmitTRunIOSilent: TRun's IO step records no event, so an IO-free trace no longer means a
  silent run. trun_nil_tn must fail.
ShenJitEmitNestShapeAccepted: the uniform-code nesting of JitEmitNestTest.NestShape is asserted
  accepted (Fail removed). Rocq refuses it (non strictly positive), so the file must fail.
ShenJitEmitGetTimeSwap: ev_of reads the run clock as unix and the unix clock as run, so the
  bytecode's clock request no longer translates to the source's. get_time_agree must fail.
ShenJitEmitDo2Opaque: KD'_do2 (the source's pending call of do is transparent) needs False, so MS'
  no longer relates the machine that has returned from do. old_reflect_false (cx_ms'1) must fail.
ShenJitKRefCondSwap: a copy of compat_cond whose target is the clauses in reverse order
  (ECond (rev cl)), with compat_cond's own proof. cond tries clauses in order, so the copy is false
  and its proof must fail.
ShenJitKRefTrapNoPrim: AppExn (JitKRefCompatCtl) restricted to handlers that are not a partial
  application of a table primitive (a premise: f0 = VPartial gn args -> lookup gn (gfuns s0) <>
  Some (FPrim p)), with AppExn_of's primitive case discharged by that premise instead of by
  prim_compat_statement. Rocq rejects KRel_KApply_exn, the trap frame's handler step that
  ERel_trap, compat_trap_lt and compat_trap_fb rest on: the handler there is any value the
  continuation returns, and the residual goal (printed by Show in the log) is False from
  lookup gn (gfuns s0) = Some (FPrim p), which nothing refutes. A handler may be a partial primitive,
  so trap needs AppExn at primitive handlers, i.e. prim_compat. compat_trap_fb is true
  (prim_compat is closed), so this is a rejected proof, not a false statement.
ShenJitKRefAppExnNoPrim: AppExn_of's premise prim_compat_statement weakened to primitive outcomes
  related on EQUAL argument lists only (forall k w p args s0 s, SRel k w s0 s -> PrimOutRel k w
  (prim_rule_r p args s0) (prim_rule_r p args s)), its use instantiated at the source's arguments.
  Rocq rejects AppExn_of in its primitive case: the target applies the primitive to args0 ++
  [VExn x], related to the source's args ++ [VExn x] by VRel but not equal, so the weakened premise
  relates the wrong pair and pout_obs's PoutRel premise is not met. AppExn_fb is true, so this is a
  rejected proof, not a false statement; it shows the primitive case needs parametricity over
  related, unequal arguments, which prim_compat_statement states.
ShenJitKRefFundBelowLe: fund_below k quantifies over j <= k instead of j < k, so it claims the index
  k itself. A stronger hypothesis, not a false statement. Built as JitKRef.v + JitKRefFv.v; the proof
  of fund_below_0 (JitKRefFv; lia on j < 0) fails first. fund_below_S's step, from fund_below k and
  the index k, cannot supply the index S k the mutant also asks for.
ShenJitKRefFvLamUnfiltered: fv of (ELam x b) does not filter the binder x out of fv b. scoped_fv is
  then false (ELam x (EVar x) is scoped in [] but x is free), so scoped_fv (JitKRefFv) must fail. Built
  as JitKRef.v + JitKRefFv.v.
ShenJitKRefPoutThrowAny: PoutRel relates any two exceptions (OThrow x0, OThrow x => True). The handler
  continuations are related for the same exception only, so pout_obs (JitKRefCompatClo) must fail.
  Built as JitKRef.v + JitKRefGround.v + JitKRefBase.v + JitKRefCompatClo.v. ShenJitKRefAbsvectorNoWext
  and ShenJitKRefEqBudgetFree mutate proofs in JitKRefPrim.v, not PoutRel's or PrimOutRel's text, so
  they do not test these definitions; this mutant and the next do.
ShenJitKRefPrimOutAnyIO: PrimOutRel relates two IO requests without q0 = q. The two sides then make
  different requests, and call_rel (JitKRefCompatClo), which must give the same request on both
  sides, must fail. Built as the chain of ShenJitKRefPoutThrowAny.
ShenJitEmitCatchUpNone: cx_c2, the configuration the source catches up to, is cx_c itself (no source
  step), and cx_src_catch_up is re-proved for it by SS_refl, so Rocq reaches cx_ms2. MS does not relate
  cx_c to cx_m1 (cx_not_ms1), so cx_ms2 (behind cx_catch_up) must fail.
ShenJitEmitEqCycleAcyclic: cy_s's second cell holds VVec 1 instead of VVec 0, so the source's = on
  VVec 0 and VVec 1 answers true instead of going wrong. dv_eq_cycle must fail.
ShenJitKRefCallNoTable: SRel_with (and GStore, so that SRel_ground still holds) without the clause
  gfuns s0 = gfuns s, each replaced by True so no destructuring shifts. Built as JitKRef.v +
  JitKRefGround.v + JitKRefBase.v + JitKRefCompatClo.v; the first three compile, and Rocq rejects
  JitKRefCompatClo.call_rel, the named-call move compat_call (JitKRefCompatCall) rests on: with two
  function tables no longer equal, a call of f may run different definitions on the two sides.
  A rejected proof only. That call_rel is false without the clause is shown separately in Rocq by
  JitKRefCallNoTableCex.call_rel_no_table_refuted (call_rel's statement with SRel's table clause
  replaced by True, over the unmutated VRel, KRel and fund_below).
ShenJitKRefCallNoTableCexTable: JitKRefCallNoTableCex.SRel_nt with the table clause restored
  (gfuns s0 = gfuns s for True, and SRel_nt_table's proof supplying it). The counterexample's two
  stores have different tables, so call_rel_no_table_refuted must fail where it establishes SRel_nt
  for them. The mutant also tries the restored clause by vm_compute; reflexivity (not exact I, whose
  type mismatch would fail on any goal), so the rejection is Rocq computing the two tables and
  finding them different; JitKRefCallNoTableCex.cx_tables_differ proves gfuns cx_s0 <> gfuns cx_s.
ShenJitEmitCoreNoCatchUp: old_reflect_core_statement asks for MS at c' itself instead of at some c''
  the source reaches silently from c'. That is old_reflect_statement's first conjunct, which
  old_reflect_false refutes, so the core would no longer be equivalent to old_reflect'_statement:
  old_reflect'_of_core must fail.
ShenJitEmitIoFailTranslated: ev_of translates a failed clock request (JTime, JFailed) to a source
  IO failure event. The environment that answers JFailed then has a translated trace, so it no
  longer refutes preservation_noenv_statement: env_ok_needed must fail.
ShenJitKRefFundNoTrapCase: fund_step (JitKRefFund) with its trap case proved as a literal
  (eapply ERel_lit; reflexivity) instead of by ERel_trap with JitKRefCompatCtl.AppExn_fb. Rocq
  rejects it at the trap goal: lit_val (ETrap a b) is None, so no compat lemma covers the case.
ShenJitKRefStoreReflNoStoreOk: store_refl_statement without its store_ok s premise, chained as
  JitKRef.v + JitKRefGround.v. store_ok is carried beside SRel as a premise because SRel does not give
  it (JitKRefBase.SRel_lok_refuted); without it, store_refl_of_fundamental (and adequacy_of_fundamental,
  which uses it) must fail.
ShenJitKTermResourceSteps: jit_rules_nr (rocq/JitKTerm.v) with jit_rules' own resource field (heap and
  stack failures catchable as XUser "out of memory" / "stack overflow"), chained as JitKTerm.v +
  JitKTermGround.v + JitKRefTerm.v. KTerm then speaks of runs that may raise a resource error at any
  running state, so a looping target "terminates" by raising, and KTerm_omega_refuted (a looping
  target does not refine a source raising (simple-error "out of memory")) is false. Rocq must reject
  om_srun, the lemma that the loop's runs stay inside its invariant, at its resource-step case.
ShenJitKTermLamAppIdKey: JitKRefTermThm.KTerm_lambda_app with its ~ In id_key g premise replaced by True. The
  source's body runs under the closure's identity cell (id_key, VVec l), the target's let body does
  not, so a scope naming id_key relates two different values (the statement is then false: with
  g = [id_key] and b0 = b = id_key the source returns its fresh cell, the target the environment's
  value); the proof must fail at the id_key case, where nothing contradicts In id_key g.
ShenJitFrontAlphaCapture: aeq's variable test forgets that a target binder hides a free name, so
  (lambda x (f x y)) and (lambda y (f y y)) count as alpha-equivalent. aeq_capture must fail.
ShenJitFrontInlFrozenFree: the inline site checker lets a thawed-in-place argument read a name the
  expansion binds. site_when_capture must fail.
ShenJitFrontDCompiled: D_compiled' stops asking check_fn of each callee's code. D_compiled'_spec
  must fail.
ShenJitFrontPortUnify: D_of's port_used brings in only the unify form the normal form calls, so
  D_has_port_unify (which asks both) is unreachable. port_used_unify must fail.
ShenJitFrontInlHidden: inl_eq thaws a frozen argument in place without checking that no binder
  inside N hides one of its free names. site_frozen_hidden must fail.
ShenJitFrontBindLetdo: bind_site stops reading e_B's unused let as do, so no real bound-now site
  matches. site_bind (and site_bind_real) must fail.
ShenJitFrontBindFresh: bind_site drops its fresh_seq guard, so a let value may read a fresh name
  bound just above it (the source's outer a1 passed as Y is captured by the expansion's a1).
  site_bind_fresh must fail.
ShenJitFrontCblkCondTrue: cblk_of walks the clauses after a (true X) clause of cond, which
  C_cond_true never compiles. cblk_of_Comp must fail.
ShenJitFrontCblkEqAll: cblk_of reports = as a blocker unless EVERY operand is a literal; pguard asks
  for one. prim_gate_ok (and so cblk_of_Comp) must fail.
ShenJitFrontWhyOther: D_why drops an entry check_fn rejects with no blocker. D_why_spec must fail.
ShenJitFrontSiteNargsNoInfer: site_nargs cannot read back an integer argument, so integer sites
  are unread. class_hds must fail.
ShenJitFrontPairReadBack: pair_src checks the site against its own read-back arguments, not the
  source call's. pair_src_lrules_wrong must fail.
ShenJitFrontIsitesNoLets: isites counts no parameter lets above a marker, so a site starts at the
  marker. isites_fbound must fail.
ShenJitFrontSugarCondTrueAny: chk_cond ends the chain at ANY clause, not only one whose test is
  the literal true, so (cond (false 1)) checks against 1. chk_cond_sound must fail.
ShenJitFrontSugarCondIfSwap: chk_cond's if case checks the clause body against the else branch and
  the rest of the chain against the then branch. chk_cond_sound must fail.
ShenJitFrontSugarProtectAny: chk_sugar drops (protect X) to X without asking D for the kernel's
  protect, so a store whose protect is anything else is accepted. chk_sugar_sound must fail.
ShenJitFrontSugarLamIdKey: chk_sugar's lambda application no longer refuses a scope holding
  KLPort.id_key, where the source body's closure cell shadows the scoped name (see
  ShenJitKTermLamAppIdKey). chk_sugar_sound must fail.
ShenJitFrontSugarThawAny: chk_thaw takes (thaw X) to [apply X] without asking D for the kernel's
  thaw. chk_thaw_sound must fail.
ShenJitFrontSugarTrapScope: chk_trap accepts a handler eta whose fresh name is in scope, so the
  target's handler reads the exception where the source reads the scoped value. chk_trap_sound
  must fail.
ShenJitFrontPrologIdKey: beq's thawed-place guard tests p4 instead of id_key, so a frozen body that
  reads the closure-identity key is run in place (D00's bind_site gap). beq_sound and
  bind_rule_rejects_id_key must fail.
ShenJitFrontPrologHidden: beq's thawed-place guard reads hidden against no binders, so the thawed
  body may read an expansion binder. beq_sound must fail.
ShenJitFrontPrologFreeVar: beq compares a variable unbound in rn by name, so e_B's free names read
  unrelated environments. beq_sound must fail.
ShenJitFrontPrologLetdo: beq reads (let X A B) as (do A' B') even when B uses X. beq_sound must fail.
ShenJitFrontPrologScope: bind_rule checks the fresh names against no scope, so a let may shadow a
  name of g the next argument reads. bind_rule_sound must fail.
ShenJitFrontPrologDoFirst: bind_rule takes a do returning its FIRST argument. bind_rule_sound must fail.
ShenJitFrontPrologP4Key: bind_rule checks p3, not p4, against id_key. bind_rule_sound must fail.
ShenJitFrontPrologCutWhen: cut_rule takes any else branch of D's when, so (when false ...) need not be
  false. cut_rule_rejects_when_body (and cut_rule_sound) must fail.
ShenJitFrontPrologCutEq: cut_rule takes any D entry for =, so (= false false) need not be true.
  cut_rule_rejects_user_eq (and cut_rule_sound) must fail.
ShenJitFrontPrologCutSwap: cut_rule pairs shen.cut's p3 with L and p2 with K in A, so the target's
  (shen.lock L K) is accepted for (shen.lock K L). cut_rule_accepts and cut_rule_rejects_swap must fail.
ShenJitFrontPrologCutScope: cut_rule checks the call's variables against no scope, so a source lookup
  may fail where the target returns. cut_rule_rejects_scope (and cut_rule_sound) must fail.
ShenJitImageNoCodeEq: check_def gives Match without comparing the loaded code with the image's
  decoded code. check_def_sound must fail.
ShenJitEmitCheckLabel: JitEmitCheck's stepC skips the label of a returning if's else branch (the
  port of ShenJitLowerCheckLabel). stepC_sound must fail.
ShenJitEmitCheckHookRest: JitEmitCheck's orC, when it falls back to a hook, returns the code it
  started from instead of the hook's rest, so the checker claims a family derivation from r to r.
  lift_orC must fail.
ShenJitEmitCheckMismatch: the Eq family's lift injects through Comp's Store hook (inj_C_Store), so
  the checker would read an Eq hook's derivation as a Store rule's. liftC_Eq must fail (Rocq refuses
  the mismatched Rule_X).
ShenJitEmitCheckNoneAccept: the empty hook noneC (every family's hook while its Rule_X is empty)
  accepts, returning the code it was given, so the checker accepts a hook node for which no Rule_X
  derivation exists. A behavioural mutant: it changes what the checker accepts. none_okC must fail.
ShenJitFrontNoScope: fchk's equality case without `scoped g e`. KRef_refl needs it (a free variable
  outside the scope may be bound to unrelated values on the two sides). Rejected first at the
  decision: fchk_rejects_unscoped (vm_compute, placed right after fchk) no longer holds.
ShenJitFrontSameFuel: fchk passes its own fuel, not fuel - 1, to the rules' recursive checker.
  The definition is no longer structural; Rocq refuses the Fixpoint (the guard condition is the
  property itself: termination of the check, and the induction fchk_sound runs on the fuel).
ShenJitFrontShareElseSwap: share's chain base accepts (if T' (thaw G) X'), the else and then branches
  swapped. Rejected first at the decision: share_rejects_swap (vm_compute, before every proof).
ShenJitFrontShareThawAny: share accepts (thaw H) for any variable H as the else branch, not only the
  ElseN the let binds. Rejected first at the decision: share_rejects_thaw_other (vm_compute).
ShenJitFrontShareReuseOpBlind: share's reuse compares a reused path by its base variable only, not
  its hd/tl operations (path_eqb without the operation list). Rejected first at the decision:
  share_reuse_rejects_wrong_op (vm_compute: (hd V) against a variable bound to (tl V)).
ShenJitFrontShareChainFactUnchecked: a chain let records the fact of the source's (hd y)/(tl y)
  without checking that the target's let binds the same expression. Rejected at chain_fact_cases
  (the fact must be the target's own path; JitFrontShare.v, the proof's expr_eqb_eq step). A proof-level
  mutant: with rec = fchk share_rules, (hd y)/(tl y) is accepted only against itself, so no decision of
  check_share changes; ShenJitFrontShareReuseOpBlind is the reuse relation's decision-level mutant.
ShenJitFrontAeqLamNoRn: aeq compares a lambda's bodies without pairing the two binders, so
  ((lambda x x) 1) is alpha-equivalent to ((lambda y x) 1), a pair JitFrontInline's
  aeq_lam_cx_not_KRef proves is not a refinement. Built as JitFrontD.v + JitFrontInline.v
  (mutate_chain); JitFrontD's Example aeq_shadow fails first (the mutant also rejects an equivalent
  pair); JitFrontInline's aeq_lam_cx pins the unsound direction.
ShenJitFrontAeqLetIdKey: aeq's let case drops binder_ok, so a let may bind the closure-identity key,
  which a freeze then rebinds on one side only. Built as JitFrontD.v + JitFrontInline.v; the
  Example aeq_let_cx must fail: the mutant accepts the pair aeq_let_cx_not_KRef proves is not a
  refinement.
ShenJitFrontInlGuard: inl_site_g drops its id_key guard on frozen arguments, so it accepts the
  inline counterexample. inl_site_g_cx must fail: the mutant accepts the site cx_not_KRef proves
  is not a refinement. (Test evidence about the guard: the guarded checker's soundness is open.)
ShenJitFrontBindGuard: bind_site_g drops its id_key guard, so it accepts the bound-now
  counterexample. bind_site_g_cx must fail: the mutant accepts the site bx_not_KRef proves is not a
  refinement. (Test evidence about the guard, as above.)
ShenJitFrontChainFinalThrow: chain_ok stops checking that its last configuration is not a raise, so
  a chain may end in the (XUnboundVar y) raise no_reach_iter excludes (no_reach_iter is then
  false). The Lemma chain_final_raise must fail. (Dropping the check on the configurations before
  the last instead is an equivalent mutant: with no trap frame, a raise there reaches the last.)
ShenJitFrontFoldNoRange: cfold folds + without the fixnum range check, where jit_rules' + raises.
  cfold_run must fail.
ShenJitFrontFoldNoPrim: cfold folds + without asking that D binds + to the primitive, so the store's
  + may be any function. cfold_run must fail.
ShenJitFrontFoldMinusAdds: cfold's - case computes x + y. cfold_run must fail.
ShenJitFrontCfVarScope: cf_same accepts a variable without asking that it is in scope, where the two
  environments may bind it to unrelated values. cf_same_sound must fail.
ShenJitFrontCopyLetScope: the let-frozen intro rule checks the body with X still in scope, so a target
  X (an outer binding) would be compared with the source's closure. cc_intro_sound must fail.
ShenJitFrontCopyNoDrop: cc_same keeps every known-closure entry under a lambda binder, though the binder
  may rebind the closure's name or a free name of its body. cc_same_sound must fail.
ShenJitFrontLamArgScope: the known-lambda site checks the arguments in the full scope, though the target
  evaluates the later ones under the earlier parameters' lets. cc_lam_sound must fail.
ShenJitFrontKcInvIdKey: the frozen entry's invariant forgets that its free names exclude the closure-
  identity key, which tagged environments bind on one side only. Rocq rejects it at kc_inv_mono, the
  first proof that destructures the invariant (Inv_tag also needs the dropped conjunct).
ShenJitFrontThawNoD: the (thaw X) site is accepted without the kernel's thaw body in D, so the store's
  thaw may be any function. cc_thaw_sound must fail.
ShenJitFrontCopyBindScope: cc_bind checks the expansion's fresh names against no scope, so a let may
  shadow a name of g the next argument reads. cc_bind_sound must fail.
ShenJitFrontCopyBindDrop: cc_bind checks Y0 with every known-closure entry, though the first let may
  shadow a name of an entry's closure scope. cc_bind_sound must fail.
"""
import re
from pathlib import Path
out = Path('_build/mutations')
out.mkdir(parents=True, exist_ok=True)
names = []

def mutate(name, path, old, new):
    src = Path(path).read_text()
    assert src.count(old) == 1, (name, old)
    (out / (name + '.v')).write_text(src.replace(old, new))
    names.append(name)

def mutate_chain(name, paths, old, new):
    """A statement in paths[0] whose proof is in a later file. The runner compiles one file, so the
    mutant is the files concatenated in order, the first mutated, each later file's Require of an
    earlier one dropped and its paths Mod.Mod.x shortened to Mod.x (the module is now in the same
    file). Text assembly only; Rocq decides."""
    mods = [Path(p).stem for p in paths]
    texts = [Path(p).read_text() for p in paths]
    assert texts[0].count(old) == 1, (name, old)
    texts[0] = texts[0].replace(old, new)
    for i in range(1, len(texts)):
        for m in mods[:i]:
            req = re.compile(r'^(From Buri Require Import .*) ' + m + r'(?=[ .])', re.M)
            assert len(req.findall(texts[i])) == 1, (name, m)
            texts[i] = req.sub(lambda g: g.group(1), texts[i])
            texts[i] = re.sub(r'(?<![\w.])' + m + r'\.' + m + r'(?!\w)', m, texts[i])
    (out / (name + '.v')).write_text('\n'.join(texts))
    names.append(name)

def mutate_all(name, path, old, new, count):
    """mutate, where the text occurs exactly `count` times and every occurrence changes."""
    src = Path(path).read_text()
    assert src.count(old) == count, (name, old, src.count(old))
    (out / (name + '.v')).write_text(src.replace(old, new))
    names.append(name)

agreed = ' None (fun z => if scalar_ok z then Some [Z.to_N z] else None) false false (fun _ _ => true) (fun _ => true) false (fun _ => None)\n (fun _ => None).'
for name, new in [
    ('ShenJitAgreedRange', ' (Some (0%Z, 1%Z)) (fun z => if scalar_ok z then Some [Z.to_N z] else None) false false (fun _ _ => true) (fun _ => true) false (fun _ => None)\n (fun _ => None).'),
    ('ShenJitAgreedArity', ' None (fun z => if scalar_ok z then Some [Z.to_N z] else None) false true (fun _ _ => true) (fun _ => true) false (fun _ => None)\n (fun _ => None).'),
    ('ShenJitAgreedWrites', ' None (fun z => if scalar_ok z then Some [Z.to_N z] else None) false false (fun _ _ => true) (fun _ => true) true (fun _ => None)\n (fun _ => None).'),
    ('ShenJitAgreedIdentity', ' None (fun z => if scalar_ok z then Some [Z.to_N z] else None) true false (fun _ _ => true) (fun _ => true) false (fun _ => None)\n (fun _ => None).'),
]:
    mutate(name, 'rocq/KLPort.v', agreed, new)
mutate('ShenJitAgreedPortPrim', 'rocq/KLPort.v', agreed,
       agreed.replace('\n (fun _ => None).', '\n (fun g => if text_eqb g (kw "shen-jit.write-bytes"%string) then Some (4%nat, fun _ _ s => ret VNil s) else None).'))
mutate('ShenJitPortPrimsWired', 'rocq/JitProfile.v',
       ' (fun _ => None) (* port primitives: none until', ' jit_port_prims_core (* port primitives: none until')
mutate('ShenJitClosureIdentity', 'rocq/KLPort.v',
       '| Some x, Some y => Some (Nat.eqb x y)', '| Some x, Some y => Some true')
mutate('ShenJitNoOverflow', 'rocq/JitProfile.v',
       ' (Some (JitBytecode.JitBytecode.fix_min, JitBytecode.JitBytecode.fix_max))', ' None')
mutate('ShenJitRoundedCompare', 'rocq/JitProfile.v',
       ' | NInt x, NFloat y => jit_order p (JitBytecode.JitBytecode.compare_fix_real x y)',
       ' | NInt x, NFloat y => jit_order p (JitFloat.JitFloat.compare (JitFloat.JitFloat.of_Z x) y)')
mutate('ShenJitByteChars', 'rocq/JitProfile.v',
       ':= JitBytecode.JitBytecode.utf8_of z.', ':= if (Z.leb 0 z && Z.leb z 255)%bool then Some [Z.to_N z] else None.')
mutate('ShenJitAgreedChars', 'rocq/KLPort.v',
       ' None (fun z => if scalar_ok z then Some [Z.to_N z] else None) false false',
       ' None (fun z => Some [Z.to_N z]) false false')
mutate('ShenJitWriteBytesFrom', 'rocq/JitMeta.v',
       '   MIO (JWrites h (firstn (Z.to_nat n) (skipn (Z.to_nat i) (bytes_of m l)))) k /\\',
       '   MIO (JWrites h (firstn (Z.to_nat n) (bytes_of m l))) k /\\')
mutate('ShenJitReadErrorIgnored', 'rocq/JitMeta.v',
       '   k JReadFailed = match raise_s m "read-byte: the read failed" with MTau m\' => m\' | _ => m end.',
       '   k JReadFailed = set_stack m (swrite m d (VFix (-1))).')
mutate('ShenJitUncheckedWrites', 'rocq/JitProfile.v',
       ' false (* 0.4: write-byte and close raise', ' true (* 0.4: write-byte and close raise')
mutate('ShenJitNoSealing', 'rocq/JitProfile.v',
       '(fun _ f => negb (is_fixed_name f || existsb (text_eqb f) sealed))', '(fun _ f => negb (is_fixed_name f))')
mutate('ShenJitLowerWrongPrim', 'rocq/JitLowerPrim.v',
       "Lemma p_add : forall a b a' b', VR a a' -> VR b b' -> PR sealed E pt m d PAdd B.PAdd [a; b] [a'; b'] s.",
       "Lemma p_add : forall a b a' b', VR a a' -> VR b b' -> PR sealed E pt m d PAdd B.PSub [a; b] [a'; b'] s.")
mutate('ShenJitLowerCheckMove', 'rocq/JitLowerCheck.v',
       "| B.IMove d' s' :: r' => if N.eqb d d' && N.eqb s s' then Some r' else None",
       "| B.IMove d' s' :: r' => if N.eqb d d' then Some r' else None")
mutate('ShenJitLowerCheckLabel', 'rocq/JitLowerCheck.v',
       "       | Some (B.ILabel l' :: r3) => if N.eqb l l' && lbl_ok l r3 then chk n g top b dst r3 else None",
       "       | Some (B.ILabel l' :: r3) => if N.eqb l l' then chk n g top b dst r3 else None")
mutate('ShenJitLowerCheckConst', 'rocq/JitLowerCheck.v',
       " | VNum (NInt z), B.VFix y => Z.eqb z y", " | VNum (NInt z), B.VFix y => true")
mutate('ShenJitLowerChainSlot', 'rocq/JitLowerCheck.v',
       "   if N.eqb d d' && N.eqb d d2 && q_eqb B.PCons q && konst_vr v k then Some r' else None",
       "   if N.eqb d d' && q_eqb B.PCons q && konst_vr v k then Some r' else None")
mutate('ShenJitLowerChainConst', 'rocq/JitLowerCheck.v',
       "   if N.eqb d d' && N.eqb d d2 && q_eqb B.PCons q && konst_vr v k then Some r' else None",
       "   if N.eqb d d' && N.eqb d d2 && q_eqb B.PCons q then Some r' else None")
mutate('ShenJitLowerEndsDecoupled', 'rocq/JitLowerThm.v',
       " | E_ok v v' m2 : Sstar sealed c (Cfg (Ret v) [] s) -> B.next E pt m1 = B.MFinal (B.FReturn v') m2 -> VR v v' -> Ends s c m1",
       " | E_ok v v' m0 m2 : Sstar sealed c (Cfg (Ret v) [] s) -> B.next E pt m0 = B.MFinal (B.FReturn v') m2 -> VR v v' -> Ends s c m1")
mutate_chain('ShenJitEquivEndsSameStore', ['rocq/JitKRef.v', 'rocq/JitKRefGround.v', 'rocq/JitKRefCompose.v'],
       " | ES_ok v v' m2 s0 w : Sstar sealed c (Cfg (Ret v) [] s0)",
       " | ES_ok v v' m2 s0 w : Sstar sealed c (Cfg (Ret v) [] s)")
mutate_chain('ShenJitEquivAdequacyStrict', ['rocq/JitKRef.v', 'rocq/JitKRefGround.v'],
       "    exists s0 w, srun (Cfg (Eval rho e0) [] s) [] (Cfg (Ret v) [] s0) /\\ wext (id_world s) w /\\ GStore w s0 s') /\\",
       "    exists s0 w, srun (Cfg (Eval rho e0) [] s) [] (Cfg (Ret v) [] s') /\\ wext (id_world s) w /\\ GStore w s0 s') /\\")
mutate_chain('ShenJitEquivComposeLeft', ['rocq/JitKRef.v', 'rocq/JitKRefGround.v'],
       " flat_map (fun p => map (fun q => (fst p, snd q)) (filter (fun q => Nat.eqb (snd p) (fst q)) w2)) w1.",
       " w1.")
eq_core = "VR a a' -> VR b b' -> existsb eq_safe_val [a'; b'] = true ->\n exists r,"
mutate('ShenJitLowerEqPair', 'rocq/JitLowerPrim.v', eq_core,
       "VR a a' -> VR b b' -> existsb (fun w => eq_safe_val w || match w with B.VPair _ _ => true | _ => false end) [a'; b'] = true ->\n exists r,")
mutate('ShenJitLowerEqNaN', 'rocq/JitLowerPrim.v', eq_core,
       "VR a a' -> VR b b' -> existsb (fun w => eq_safe_val w || match w with B.VReal _ => true | _ => false end) [a'; b'] = true ->\n exists r,")
mutate('ShenJitLowerCheckEqGuard', 'rocq/JitLowerCheck.v',
       "os_eqb ops ops' && pguard c q ops then Some r' else None", "os_eqb ops ops' then Some r' else None")
mutate('ShenJitSymBase256', 'rocq/JitBytecode.v',
       ' fold_right (fun n acc => sym_push (N.succ_pos n) acc) xH s.',
       ' fold_left (fun acc b =>\n   Pos.add (Pos.mul acc 256) (match b with N0 => 256 | Npos p => p end)) s xH.')
mutate('ShenJitEqStepNotLeast', 'rocq/JitEqBudgetStep.v',
       " (forall d' p q, d' < d -> In p cs -> In q cs -> p <> q -> cellcmp R P h d' p q <> Some true) ->\n"
       " list_eq (leaf_eq R P) xs ys = Some true.\nProof.\n intros R P h cs d x y xs ys C Ix Iy Ex Ey T Lst.",
       " list_eq (leaf_eq R P) xs ys = Some true.\nProof.\n intros R P h cs d x y xs ys C Ix Iy Ex Ey T.")
walk = 'rocq/JitEqBudgetWalk.v'
mutate('ShenJitWalkNoTrans', walk,
       ' (Htr : forall x y z, num_cmp P PEqual x y = true -> num_cmp P PEqual y z = true -> num_cmp P PEqual x z = true).',
       ' (Htr : True).')
mutate('ShenJitWalkTolInstance', walk,
       ' (forall x y, num_cmp P PEqual x y = num_cmp P PEqual y x) ->\n closed_in h S -> no_true_pairs R P h S ->',
       ' (forall x y, num_cmp P PEqual x y = num_cmp P PEqual y x) ->\n'
       ' (forall x y z, num_cmp P PEqual x y = true -> num_cmp P PEqual y z = true -> num_cmp P PEqual x z = true) ->\n'
       ' closed_in h S -> no_true_pairs R P h S ->')
mutate('ShenJitWalkPrefixAbove', walk,
       ' | [], _ :: _ => true\n | _ :: _, [] => false\n',
       ' | [], _ :: _ => false\n | _ :: _, [] => true\n')
core = 'rocq/JitEqBudgetCore.v'
mutate('ShenJitEqCoreNoTrans', core,
       'Hypothesis Tr : forall x y z, num_cmp P PEqual x y = true -> num_cmp P PEqual y z = true -> num_cmp P PEqual x z = true.',
       'Hypothesis Tr : True.')
mutate('ShenJitEqCoreNoClosure', core,
       ' NoDup cs -> St.closed_in h cs ->\n forall a b,',
       ' NoDup cs -> True ->\n forall a b,')
mutate_chain('ShenJitKRefKRelStrict', ['rocq/JitKRef.v', 'rocq/JitKRefGround.v', 'rocq/JitKRefBase.v'],
       "Definition KRel_with (k : nat) (w : world) (K0 K : list frame) : Prop :=\n forall j, (j <= k)%nat ->",
       "Definition KRel_with (k : nat) (w : world) (K0 K : list frame) : Prop :=\n forall j, (j < k)%nat ->")
mutate('ShenJitKRefDefunSealed', 'rocq/JitProfile.v',
       '(fun _ f => negb (is_fixed_name f || existsb (text_eqb f) sealed))',
       '(fun _ f => negb (is_fixed_name f) || existsb (text_eqb f) sealed)')
mutate_chain('ShenJitKRefLamNoSameId', ['rocq/JitKRef.v', 'rocq/JitKRefGround.v', 'rocq/JitKRefBase.v', 'rocq/JitKRefCompatClo.v'],
       " | VLam x0 b0 r0, VLam x b r => same_id w r0 r /\\\n     forall j, (j < k)%nat -> forall w', wext w w' -> forall a0 a, V j w' a0 a ->",
       " | VLam x0 b0 r0, VLam x b r =>\n     forall j, (j < k)%nat -> forall w', wext w w' -> forall a0 a, V j w' a0 a ->")
prim = 'rocq/JitKRefPrim.v'
mutate('ShenJitKRefAbsvectorNoWext', prim,
       "   | exists ((List.length (heap s0), List.length (heap s)) :: w);\n"
       "     split; [exact (wext_alloc k w s0 s HS)|split; [apply VRel_vec; left; reflexivity|]];\n",
       "   | exists w;\n"
       "     split; [eapply Bs.wext_self; exact HS|split; [apply VRel_vec; left; reflexivity|]];\n")
mutate('ShenJitKRefEqBudgetFree', prim,
       " unfold kl_eq_r.\n rewrite (EBC P (heap s0) (map fst w) Sy Tr N0 (closed_bridge _ _ C0) a0 b0 (din_src _ _ _ _ Ha) (din_src _ _ _ _ Hb)\n"
       "   (S (List.length (heap s0)))) by (rewrite Bs.len_map; lia).\n"
       " rewrite (EBC P (heap s) (map snd w) Sy Tr N1 (closed_bridge _ _ C1) a b (din_tgt _ _ _ _ Ha) (din_tgt _ _ _ _ Hb)\n"
       "   (S (List.length (heap s)))) by (rewrite Bs.len_map; lia).\n"
       " rewrite L. apply (eq_lock sealed w).\n",
       " unfold kl_eq_r.\n apply (eq_lock sealed w).\n")
# emit-spec: the family hooks, the copied block, the nested dummy, the frames and the invariant.
mutate_chain('ShenJitEmitRuleOpaque', ['rocq/JitEmitRuleEq.v', 'rocq/JitEmitRel.v'],
       "c cv g top e o top2 r r' :=\n match H with end.\nEnd JitEmitRuleEq.",
       "c cv g top e o top2 r r'.\nProof. destruct H. Qed.\nEnd JitEmitRuleEq.")
mutate_all('ShenJitEmitEmbedCaptures', 'rocq/JitEmitRel.v',
       "lookup x g = Some s -> s <> d ->", "lookup x g = Some s -> s <> d /\\ cv = [] ->", 2)
mutate('ShenJitEmitNestSwap', 'rocq/JitEmitNestTest.v',
       "Rule_Dummy Cp Ct Co Cs Cw Ca c cv g top (EApp t [a; b]) (DSlot d) r r'.",
       "Rule_Dummy Cp Ct Co Cs Cw Ca c cv g top (EApp t [a; b]) (DSlot d) r' r.")
mutate('ShenJitEmitTrapNoHandler', 'rocq/JitEmitKont.v',
       "KD' c cv caps fp st cs (B.Handler c lH fp cs (quiet_of rh) :: hs) w (B.OSlot s) (B.IPopHandler :: r1)",
       "KD' c cv caps fp st cs hs w (B.OSlot s) (B.IPopHandler :: r1)")
mutate('ShenJitEmitPmapx', 'rocq/JitEmitKont.v', " | PAdd => Some B.PAdd |", " | PAdd => Some B.PSub |")
mutate('ShenJitEmitVRhPartial', 'rocq/JitEmitInv.v',
       " | VRh_stream hd p d o :",
       " | VRh_partial f args p : VRh mu h (VPartial f args) (B.VClo p)\n | VRh_stream hd p d o :")
mutate('ShenJitEmitEndsDecoupled', 'rocq/JitEmitInv.v',
       " | E'_ok v v' s' m2 mu' : Srun c t (Cfg (Ret v) [] s') -> B.next E pt m1 = B.MFinal (B.FReturn v') m2 ->",
       " | E'_ok v v' s' m0 m2 mu' : Srun c t (Cfg (Ret v) [] s') -> B.next E pt m0 = B.MFinal (B.FReturn v') m2 ->")
mutate('ShenJitEmitSMNonEmpty', 'rocq/JitEmitInv.v', " sm_bij : pbij mu;", " sm_bij : pbij mu /\\ mu <> [];")
mutate('ShenJitEmitFrameEqGuard', 'rocq/JitEmitKont.v', " | _ => pguard c q ops end.", " | _ => true end.")
mutate('ShenJitEmitTRunZero', 'rocq/JitEmitInv.v', " | TR_0 rs m : TRun rs 0 m [] m", " | TR_0 rs m m' : TRun rs 0 m [] m'")
mutate('ShenJitEmitSimCRest', 'rocq/JitEmitInv.v', "code m = c -> B.m_rest m = r -> EvalCtx", "code m = c -> EvalCtx")
mutate('ShenJitEmitSimTRest', 'rocq/JitEmitInv.v', "code m = c -> B.m_rest m = r -> TestCtx", "code m = c -> TestCtx")
mutate('ShenJitEmitSimORest', 'rocq/JitEmitInv.v', "code m = c -> B.m_rest m = r -> OpCtx", "code m = c -> OpCtx")
mutate('ShenJitEmitSimSDrop', 'rocq/JitEmitInv.v', "     SimS c cv g top (e :: es) (o :: os) r r'.", "     SimS c cv g top (e :: es) os r r'.")
mutate('ShenJitEmitSimWSlot', 'rocq/JitEmitInv.v', " : SimC c cv g (s + 1) e (DSlot s) r r1 -> SimW", " : SimC c cv g s e (DSlot s) r r1 -> SimW")
mutate('ShenJitEmitSimAKill', 'rocq/JitEmitInv.v', "     SimA c cv (kill s g) (s + 1) t es ms r1 r' -> SimA", "     SimA c cv g (s + 1) t es ms r1 r' -> SimA")
mutate('ShenJitEmitMSRetCapture', 'rocq/JitEmitInv.v', " | MS'_ret cv caps v v' o k s w m :\n     SM mu s k m ->", " | MS'_ret cv caps v v' o k s w m :\n     SM mu s k m -> cv <> [] ->")
mutate('ShenJitEmitOutRaiseNoHK', 'rocq/JitEmitInv.v', "exn_ok x msg -> mext mu mu' -> SM mu' s' k m2 ->", "exn_ok x msg -> mext mu mu' -> SMs mu' s' m2 ->")
mutate('ShenJitEmitEndsSrcDecoupled', 'rocq/JitEmitInv.v',
       " | ES'_ok v0 v v' s0 s' w m2 mu' : Srun c0 t (Cfg (Ret v0) [] s0) ->\n     JitKRef.JitKRef.wext (JitKRef.JitKRef.id_world s) w -> JitKRef.JitKRef.GVal w v0 v ->\n     JitKRef.JitKRef.GStore w s0 s' ->\n     B.next E pt m1 =",
       " | ES'_ok v0 v v' s0 s' w m0 m2 mu' : Srun c0 t (Cfg (Ret v0) [] s0) ->\n     JitKRef.JitKRef.wext (JitKRef.JitKRef.id_world s) w -> JitKRef.JitKRef.GVal w v0 v ->\n     JitKRef.JitKRef.GStore w s0 s' ->\n     B.next E pt m0 =")
mutate('ShenJitEmitHKTwice', 'rocq/JitEmitInv.v', " B.h_quiet hd = quiet_of r) hs (trap_frames k).", " B.h_quiet hd = quiet_of r) hs (trap_frames k ++ trap_frames k).")
mutate('ShenJitEmitGvalsCleared', 'rocq/JitEmitInv.v', "Some v' /\\ v' <> B.VCleared /\\ VRh mu", "Some v' /\\ VRh mu")
mutate('ShenJitEmitDoSame', 'rocq/JitEmitInv.v', " exists x y, x <> y /\\ lookup do_name (gfuns s) = Some (FUser [x; y] (EVar y)).\n", " exists x y, lookup do_name (gfuns s) = Some (FUser [x; y] (EVar y)).\n")
mutate('ShenJitEmitFunRelCaps', 'rocq/JitEmitInv.v', "   B.tget l (B.m_heap m) = Some (B.OClo c caps) /\\\n", "   B.tget l (B.m_heap m) = Some (B.OClo c caps) /\\ caps = [] /\\\n")
mutate('ShenJitEmitTimeRefused', 'rocq/JitEmitInv.v', " | B.JTime _, B.JTimeIs b => (b < 18446744073709551616)%N", " | B.JTime _, B.JTimeIs b => False")
mutate('ShenJitEmitEvOfTime', 'rocq/JitEmitInv.v', "   if (b <? 18446744073709551616)%N\n   then Some", "   if false\n   then Some")
mutate('ShenJitEmitStoreRelNonEmpty', 'rocq/JitEmitInv.v', " pbij mu /\\ HeapRel mu s m /\\ GvalsRel mu s m.", " pbij mu /\\ mu <> [] /\\ HeapRel mu s m /\\ GvalsRel mu s m.")
mutate('ShenJitEmitReflectTrace', 'rocq/JitEmitInv.v', "-> tS = [] /\\ MS s c' m1) /\\", "-> True /\\ MS s c' m1) /\\")
mutate('ShenJitEmitReflectSrcTrace', 'rocq/JitEmitInv.v', " tS = [] /\\ JitKRef.JitKRef.EndsSrc sealed E pt s (Cfg", " True /\\ JitKRef.JitKRef.EndsSrc sealed E pt s (Cfg")
mutate('ShenJitEmitOldGvalsDropped', 'rocq/JitEmitInv.v', "forall n s c m, MS s c m -> GvalsRel [] s m ->", "forall n s c m, MS s c m -> True ->")
mutate('ShenJitEmitTRunIOSilent', 'rocq/JitEmitInv.v', " TRun rs (S n) m (ev_of q (rs O q) :: t) m2", " TRun rs (S n) m t m2")
mutate('ShenJitEmitNestShapeAccepted', 'rocq/JitEmitNestTest.v', "Fail Inductive Tree", "Inductive Tree")
mutate('ShenJitEmitGetTimeSwap', 'rocq/JitEmitInv.v', '(QTime (of_string (if run then "run"%string else "unix"%string)))',
       '(QTime (of_string (if run then "unix"%string else "run"%string)))')
mutate_chain('ShenJitEmitDo2Opaque', ['rocq/JitEmitKont.v', 'rocq/JitEmitInv.v'],
       " | KD'_do2 c cv caps fp st cs hs w o r v rho k1 : DoK -> KD'", " | KD'_do2 c cv caps fp st cs hs w o r v rho k1 : False -> DoK -> KD'")
mutate('ShenJitKRefCondSwap', 'rocq/JitKRefCompatCtl.v',
       "Theorem compat_type : compat_type_statement.",
       "Theorem compat_cond_swap : forall g cl0 cl,\n Forall2 (fun p0 p => KRef g (fst p0) (fst p) /\\ KRef g (snd p0) (snd p)) cl0 cl ->\n KRef g (ECond cl0) (ECond (rev cl)).\nProof.\n intros g cl0 cl F k w rho0 rho Ww HE. apply ERel_cond.\n eapply Forall2_impl; [|exact F]. intros p0 p [H1 H2]. split; [apply H1|apply H2]; assumption.\nQed.\n\nTheorem compat_type : compat_type_statement.")
fvchain = ['rocq/JitKRef.v', 'rocq/JitKRefFv.v']
mutate_chain('ShenJitKRefFundBelowLe', fvchain,
       "Definition fund_below (k : nat) : Prop :=\n forall j, (j < k)%nat ->",
       "Definition fund_below (k : nat) : Prop :=\n forall j, (j <= k)%nat ->")
mutate_chain('ShenJitKRefFvLamUnfiltered', fvchain,
       " | ELam x b => filter (fun y => negb (text_eqb y x)) (fv b)\n",
       " | ELam x b => fv b\n")
clochain = ['rocq/JitKRef.v', 'rocq/JitKRefGround.v', 'rocq/JitKRefBase.v', 'rocq/JitKRefCompatClo.v']
mutate_chain('ShenJitKRefPoutThrowAny', clochain,
       " | OThrow x0, OThrow x => x0 = x\n",
       " | OThrow x0, OThrow x => True\n")
mutate_chain('ShenJitKRefPrimOutAnyIO', clochain,
       " | PIO q0 c0, PIO q c => q0 = q /\\ forall r, PoutRel k w (c0 r) (c r)\n",
       " | PIO q0 c0, PIO q c => forall r, PoutRel k w (c0 r) (c r)\n")
mutate('ShenJitEmitCatchUpNone', 'rocq/JitEmitInv.v',
       "Definition cx_c2 : config := Cfg (Ret (VNum (NInt 2))) [KLet cx_z (EVar cx_z) []] cx_s.\n"
       "Lemma cx_src_catch_up : JitLowerStep.Sstar [] cx_c cx_c2.\n"
       "Proof.\n"
       " eapply JitLowerStep.S1; [vm_compute; reflexivity|].\n"
       " eapply JitLowerStep.S1'. vm_compute. reflexivity.\n"
       "Qed.",
       "Definition cx_c2 : config := cx_c.\n"
       "Lemma cx_src_catch_up : JitLowerStep.Sstar [] cx_c cx_c2.\n"
       "Proof. apply JitLowerStep.SS_refl. Qed.")
mutate('ShenJitEmitEqCycleAcyclic', 'rocq/JitEmitInv.v',
       "Definition cy_s : store := Store [[VVec 1]; [VVec 0]] [] [].",
       "Definition cy_s : store := Store [[VVec 1]; [VVec 1]] [] [].")
def mutate_chain_n(name, paths, edits):
    """mutate_chain with several (old, new) edits, all in paths[0], each old occurring once."""
    src = Path(paths[0]).read_text()
    for old, new in edits:
        assert src.count(old) == 1, (name, old)
        src = src.replace(old, new)
    mods = [Path(p).stem for p in paths]
    texts = [src] + [Path(p).read_text() for p in paths[1:]]
    for i in range(1, len(texts)):
        for m in mods[:i]:
            req = re.compile(r'^(From Buri Require Import .*) ' + m + r'(?=[ .])', re.M)
            assert len(req.findall(texts[i])) == 1, (name, m)
            texts[i] = req.sub(lambda g: g.group(1), texts[i])
            texts[i] = re.sub(r'(?<![\w.])' + m + r'\.' + m + r'(?!\w)', m, texts[i])
    (out / (name + '.v')).write_text('\n'.join(texts))
    names.append(name)

ctl = 'rocq/JitKRefCompatCtl.v'
mutate_chain_n('ShenJitKRefTrapNoPrim', [ctl],
       [(" forall j w K0 K x f0 f s0 s, (j <= k)%nat -> KRel j w K0 K -> VRel j w f0 f -> SRel j w s0 s ->\n"
         "  ObsT j w (Cfg (Ret f0) (KApply [VExn x] :: K0) s0)",
         " forall j w K0 K x f0 f s0 s, (j <= k)%nat -> KRel j w K0 K -> VRel j w f0 f -> SRel j w s0 s ->\n"
         "  (forall gn args p, f0 = VPartial gn args -> lookup gn (gfuns s0) <> Some (FPrim p)) ->\n"
         "  ObsT j w (Cfg (Ret f0) (KApply [VExn x] :: K0) s0)"),
        (" intros j' w' v0 v s0 s L' W HV HS. apply HA; [lia|eapply KRel_mono; [exact L'|exact W|exact HK]|exact HV|exact HS].\n",
         " intros j' w' v0 v s0 s L' W HV HS. apply HA; [lia|eapply KRel_mono; [exact L'|exact W|exact HK]|exact HV|exact HS|].\n"
         " intros gn args p E Lk. Show. congruence.\n"),
        (" intros Hp k Hf j w K0 K x f0 f s0 s L HK HV HS. destruct j as [|j]; [apply ObsT_0|].\n",
         " intros Hp k Hf j w K0 K x f0 f s0 s L HK HV HS NP. destruct j as [|j]; [apply ObsT_0|].\n"),
        ("   unfold call_named_r. rewrite G. destruct (lookup gn (gfuns s)) as [[p|ps body]|].\n"
         "   + (* a primitive *)\n"
         "     rewrite Ln. destruct (arity_mismatch R (List.length (args0 ++ [VExn x])) (prim_arity p)) eqn:A; cbn [MRel]; [apply Thr|].\n"
         "     apply arity_ok in A. rewrite A, Nat.ltb_irrefl. rewrite !firstn_all2, !skipn_all2 by lia.\n"
         "     unfold prim_move_r. pose proof (proj1 (Hp j w) p _ _ s0 s Fj HSj) as Hr.\n"
         "     destruct (prim_rule_r R P p (args ++ [VExn x]) s0), (prim_rule_r R P p (args0 ++ [VExn x]) s);\n"
         "      cbn in Hr; try contradiction; cbn [MRel].\n"
         "     * eapply pout_obs; [exact Hf|lia|exact HKj|exact HSj|exact Hr].\n"
         "     * destruct Hr as [<- Hr]. split; [reflexivity|]. intros r.\n"
         "       eapply pout_obs; [exact Hf|lia|exact HKj|exact HSj|apply Hr].\n",
         "   unfold call_named_r. rewrite G. destruct (lookup gn (gfuns s)) as [[p|ps body]|] eqn:Lk.\n"
         "   + (* a primitive: excluded by NP *)\n"
         "     exfalso. apply (NP _ _ p eq_refl). rewrite G. exact Lk.\n")])
mutate_chain_n('ShenJitKRefAppExnNoPrim', [ctl],
       [("Theorem AppExn_of : prim_compat_statement -> forall k, fund_below k -> AppExn k.",
         "Theorem AppExn_of : (forall k w p args s0 s, SRel k w s0 s ->\n"
         "   PrimOutRel k w (prim_rule_r R P p args s0) (prim_rule_r R P p args s)) -> forall k, fund_below k -> AppExn k."),
        ("     unfold prim_move_r. pose proof (proj1 (Hp j w) p _ _ s0 s Fj HSj) as Hr.\n",
         "     unfold prim_move_r. pose proof (Hp j w p (args ++ [VExn x]) s0 s HSj) as Hr.\n")])
mutate_chain_n('ShenJitKRefCallNoTable',
       ['rocq/JitKRef.v', 'rocq/JitKRefGround.v', 'rocq/JitKRefBase.v', 'rocq/JitKRefCompatClo.v'],
       [(" gfuns s0 = gfuns s /\\\n Forall2 (fun p0 p => fst p0 = fst p /\\ GVal w",
         " True /\\\n Forall2 (fun p0 p => fst p0 = fst p /\\ GVal w"),
        ("StoreHas s0 /\\ StoreHas s /\\ gfuns s0 = gfuns s /\\",
         "StoreHas s0 /\\ StoreHas s /\\ True /\\")])
mutate('ShenJitEmitCoreNoCatchUp', 'rocq/JitEmitInv.v',
       " MS s c m -> GvalsRel [] s m -> JitLowerThm.TN E pt k m m1 -> Sstar c c' -> mext [] mu' -> MS' mu' c' m1 ->\n exists c'', Sstar c' c'' /\\ MS s c'' m1.",
       " MS s c m -> GvalsRel [] s m -> JitLowerThm.TN E pt k m m1 -> Sstar c c' -> mext [] mu' -> MS' mu' c' m1 ->\n MS s c' m1.")
mutate('ShenJitEmitIoFailTranslated', 'rocq/JitEmitInv.v',
       " | B.JTime run, B.JTimeIs b =>",
       " | B.JTime run, B.JFailed => Some (EvIO (QTime (of_string \"run\"%string)) (RFailed (EOther 0)))\n | B.JTime run, B.JTimeIs b =>")
fund = 'rocq/JitKRefFund.v'
mutate('ShenJitKRefFundNoTrapCase', fund,
       "   apply JitKRefCompatCtl.JitKRefCompatCtl.ERel_trap;\n"
       "    [exact (JitKRefCompatCtl.JitKRefCompatCtl.AppExn_fb sealed D k Fb)|ih IHa Ww HE|ih IHb Ww HE].\n",
       "   eapply ERel_lit; reflexivity.\n")
mutate_chain('ShenJitKRefStoreReflNoStoreOk', ['rocq/JitKRef.v', 'rocq/JitKRefGround.v'],
       " D_wf -> StoreHas s -> store_ok s -> SRel k (id_world s) s s.\n",
       " D_wf -> StoreHas s -> SRel k (id_world s) s s.\n")
kterm = ['rocq/JitKTerm.v', 'rocq/JitKTermGround.v', 'rocq/JitKRefTerm.v']
mutate_chain('ShenJitKTermResourceSteps', kterm,
       " false\n (fun _ => None)\n (fun _ => None).\n",
       " false\n (fun r => match r with\n  | Observation.Observation.RHeap => Some (XUser (of_string \"out of memory\"))\n  | Observation.Observation.RStack => Some (XUser (of_string \"stack overflow\")) end)\n (fun _ => None).\n")
mutate('ShenJitKTermLamAppIdKey', 'rocq/JitKRefTermThm.v',
       "Theorem KTerm_lambda_app : forall g x a b0 b, atom_in g a = true -> ~ In id_key g ->\n",
       "Theorem KTerm_lambda_app : forall g x a b0 b, atom_in g a = true -> True ->\n")
front = 'rocq/JitFrontD.v'
mutate('ShenJitFrontAlphaCapture', front,
       ' | (a, b) :: rn => if text_eqb a x then text_eqb b y else if text_eqb b y then false else var_ok rn x y end.',
       ' | (a, b) :: rn => if text_eqb a x then text_eqb b y else var_ok rn x y end.')
mutate('ShenJitFrontInlFrozenFree', front,
       ' && frozen_free sg (map fst fr ++ qs) &&', ' &&')
mutate('ShenJitFrontDCompiled', front,
       '                  && check_fn c ps b)%bool', '                  && true)%bool')
mutate('ShenJitFrontPortUnify', front,
       '  then [unify_name; unify_bang_name] else []).', '  then [unify_bang_name] else []).')
mutate('ShenJitFrontInlHidden', front,
       '     | Some (SFrozen x) => expr_eqb x e && forallb (fun y => negb (hidden rn y)) (K.fv x)',
       '     | Some (SFrozen x) => expr_eqb x e')
mutate('ShenJitFrontBindLetdo', front,
       '     inl_eq (S (dsize eB)) fold true D [(p4, SFrozen ex)]',
       '     inl_eq (S (dsize eB)) fold false D [(p4, SFrozen ex)]')
mutate('ShenJitFrontBindFresh', front,
       "     fresh_seq [] [(a1, x'); (a2, y'); (a3, b')] &&\n", '')
mutate('ShenJitFrontCblkCondTrue', front,
       '     | (t, a) :: rest => if is_true_lit t then cblk_of c a else cblk_of c t ++ cblk_of c a ++ go rest end) cl',
       '     | (t, a) :: rest => cblk_of c t ++ cblk_of c a ++ go rest end) cl')
mutate('ShenJitFrontCblkEqAll', front,
       '(if existsb is_lit args then [] else [KEq])', '(if forallb is_lit args then [] else [KEq])')
mutate('ShenJitFrontWhyOther', front,
       '         | [] => if check_fn c ps b then [] else [(fst p, DOther)]', '         | [] => []')
mutate('ShenJitFrontSiteNargsNoInfer', front,
       '           | Some (SInt z) => Some (ENum (NInt z) :: l)', '           | Some (SInt z) => None')
mutate('ShenJitFrontPairReadBack', front,
       '[x; y; b; _] => bind_site false D [x; y; b; ex] s', '[x; y; b; _] => bind_site false D rb s')
mutate('ShenJitFrontIsitesNoLets', front,
       ' | (x, NVar _, _) :: anc => if bound ps x then S (trailing ps anc) else O',
       ' | (x, NVar _, _) :: anc => if bound ps x then O else O')
sugar = 'rocq/JitFrontSugar.v'
mutate('ShenJitFrontSugarCondTrueAny', sugar,
       '   (is_true_lit c0 && rec g b0 e) ||', '   (true && rec g b0 e) ||')
mutate('ShenJitFrontSugarCondIfSwap', sugar,
       '   match e with EIf c b r => rec g c0 c && rec g b0 b && rec g (ECond rest0) r | _ => false end',
       '   match e with EIf c b r => rec g c0 c && rec g b0 r && rec g (ECond rest0) b | _ => false end')
mutate('ShenJitFrontSugarProtectAny', sugar,
       ' | ECall f [a0] => text_eqb f protect_name && has_protect && rec g a0 e',
       ' | ECall f [a0] => text_eqb f protect_name && true && rec g a0 e')
mutate('ShenJitFrontSugarLamIdKey', sugar,
       ' | EApp (ELam x b0) [a0] => negb (bound g id_key) &&', ' | EApp (ELam x b0) [a0] => true &&')
mutate('ShenJitFrontSugarThawAny', sugar,
       ' | ECall f [a0], EApp a [] => text_eqb f thaw_name && has_thaw && rec g a0 a',
       ' | ECall f [a0], EApp a [] => text_eqb f thaw_name && true && rec g a0 a')
mutate('ShenJitFrontSugarTrapScope', sugar,
       '   text_eqb x y && negb (bound g x) && negb (bound g id_key) && rec g a0 a && rec g h0 h',
       '   text_eqb x y && true && negb (bound g id_key) && rec g a0 a && rec g h0 h')
prolog = 'rocq/JitFrontProlog.v'
mutate('ShenJitFrontPrologIdKey', prolog,
       ' && negb (bound (fv e) id_key) && tk e', ' && negb (bound (fv e) p4) && tk e')
mutate('ShenJitFrontPrologHidden', prolog,
       ' text_eqb p p4 && forallb (fun y => negb (F.hidden rn y)) (fv e)', ' text_eqb p p4 && forallb (fun y => negb (F.hidden [] y)) (fv e)')
mutate('ShenJitFrontPrologFreeVar', prolog,
       ' | EVar x, EVar y => negb (F.free_in rn x) && F.var_ok rn x y', ' | EVar x, EVar y => F.var_ok rn x y')
mutate('ShenJitFrontPrologLetdo', prolog,
       ' => text_eqb d do_name && negb (bound (fv b0) x) && go rn a0 a && go rn b0 b', ' => text_eqb d do_name && true && go rn a0 a && go rn b0 b')
mutate('ShenJitFrontPrologScope', prolog,
       ' && F.disjoint [a1; a2; a3] g &&', ' && F.disjoint [a1; a2; a3] [] &&')
mutate('ShenJitFrontPrologDoFirst', prolog,
       '     negb (text_eqb v1 v2) && text_eqb v2 v2\' &&', '     negb (text_eqb v1 v2) && text_eqb v1 v2\' &&')
mutate('ShenJitFrontPrologP4Key', prolog,
       ' && negb (text_eqb p4 id_key) &&', ' && negb (text_eqb p3 id_key) &&')
mutate('ShenJitFrontPrologCutWhen', prolog,
       ' match e with EIf (EVar q1) _ (EBool false) => Some q1 | _ => None end.', ' match e with EIf (EVar q1) _ _ => Some q1 | _ => None end.')
mutate('ShenJitFrontPrologCutEq', prolog,
       ' Some (FPrim PEqual), Some (FUser [d1; d2] (EVar d2\')) =>', ' Some _, Some (FUser [d1; d2] (EVar d2\')) =>')
mutate('ShenJitFrontPrologCutSwap', prolog,
       ' p2 [(p3, kk); (p2, l)] a aT', ' p2 [(p3, l); (p2, kk)] a aT')
mutate('ShenJitFrontPrologCutScope', prolog,
       ' forallb (bound g) [b; l; kk; b2; l2; k2; c] &&', ' forallb (bound g) [] &&')
image = 'rocq/JitImage.v'
mutate('ShenJitImageNoCodeEq', image,
       '     | Some k\' => if code_eqb k k\' then Match g else Differ g end end',
       '     | Some k\' => if true then Match g else Differ g end end')
cex = 'rocq/JitKRefCallNoTableCex.v'
mutate_chain_n('ShenJitKRefCallNoTableCexTable', [cex],
       [(" wf_world w /\\ StoreHas s0 /\\ StoreHas s /\\ True /\\\n",
         " wf_world w /\\ StoreHas s0 /\\ StoreHas s /\\ gfuns s0 = gfuns s /\\\n"),
        ("(conj W (conj H0 (conj H1 (conj I (conj Fv Hh)))))", "(conj W (conj H0 (conj H1 (conj G (conj Fv Hh)))))"),
        ("split; [exact I|split; [constructor|intros l0 l []]]", "split; [vm_compute; reflexivity|split; [constructor|intros l0 l []]]")])
emitcheck = 'rocq/JitEmitCheck.v'
mutate('ShenJitEmitCheckLabel', emitcheck,
       "       | Some (B.ILabel l' :: r3) => if N.eqb l l' && lbl_ok c l r3 then rc c cv g top b dst r3 else None",
       "       | Some (B.ILabel l' :: r3) => if N.eqb l l' then rc c cv g top b dst r3 else None")
mutate('ShenJitEmitCheckHookRest', emitcheck,
       " orelse (h1 rc rt ro rs rw ra c cv g top e d r) (fun _ => h2 rc rt ro rs rw ra c cv g top e d r).",
       " orelse (h1 rc rt ro rs rw ra c cv g top e d r) (fun _ => match h2 rc rt ro rs rw ra c cv g top e d r with Some _ => Some r | None => None end).")
mutate('ShenJitEmitCheckMismatch', emitcheck,
       "JitEmitRuleEq.Rule_Eq_all inj_C_Eq.", "JitEmitRuleEq.Rule_Eq_all inj_C_Store.")
mutate('ShenJitEmitCheckNoneAccept', emitcheck,
       "Definition noneC : HkC := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => None.",
       "Definition noneC : HkC := fun _ _ _ _ _ _ _ _ _ _ _ _ r => Some r.")
mutate('ShenJitFrontNoScope', 'rocq/JitFrontCheck.v',
       ' | S f => (expr_eqb e0 e && scoped g e)', ' | S f => (expr_eqb e0 e)')
mutate('ShenJitFrontSameFuel', 'rocq/JitFrontCheck.v',
       '          || existsb (fun r => r (fchk rules f) g e0 e) rules', '          || existsb (fun r => r (fchk rules fuel) g e0 e) rules')
mutate('ShenJitFrontShareElseSwap', 'rocq/JitFrontShare.v',
       " | EIf T' X' Z => is_thaw_of G Z && rec g C T' && then_chk rec g0 [] Pt X X'", " | EIf T' Z X' => is_thaw_of G Z && rec g C T' && then_chk rec g0 [] Pt X X'")
mutate('ShenJitFrontShareThawAny', 'rocq/JitFrontShare.v',
       ' | ECall t [EVar H] => text_eqb t thaw_name && text_eqb H G', ' | ECall t [EVar H] => text_eqb t thaw_name')
mutate('ShenJitFrontShareReuseOpBlind', 'rocq/JitFrontShare.v',
       "Definition path_eqb (p q : path) : bool := text_eqb (fst p) (fst q) && forall2b Bool.eqb (snd p) (snd q).",
       "Definition path_eqb (p q : path) : bool := text_eqb (fst p) (fst q).")
mutate('ShenJitFrontShareChainFactUnchecked', 'rocq/JitFrontShare.v',
       "   | Some o => if expr_eqb E E' && bound g y then", "   | Some o => if bound g y then")
finl = ['rocq/JitFrontD.v', 'rocq/JitFrontInline.v']
mutate_chain('ShenJitFrontAeqLamNoRn', finl,
       ' | ELam x b0, ELam y b => binder_ok x y && aeq ((x, y) :: rn) b0 b\n | ELet x a0 b0, ELet y a b => binder_ok x y && aeq rn a0 a',
       ' | ELam x b0, ELam y b => binder_ok x y && aeq rn b0 b\n | ELet x a0 b0, ELet y a b => binder_ok x y && aeq rn a0 a')
mutate_chain('ShenJitFrontAeqLetIdKey', finl,
       ' | ELet x a0 b0, ELet y a b => binder_ok x y && aeq rn a0 a && aeq ((x, y) :: rn) b0 b\n | EIf c0 a0 b0, EIf c a b => aeq rn c0 c',
       ' | ELet x a0 b0, ELet y a b => aeq rn a0 a && aeq ((x, y) :: rn) b0 b\n | EIf c0 a0 b0, EIf c a b => aeq rn c0 c')
mutate('ShenJitFrontInlGuard', 'rocq/JitFrontInline.v',
       ' forallb (fun n => negb (reads_id n)) nargs && F.inl_site fold letdo D f nargs e.',
       ' F.inl_site fold letdo D f nargs e.')
mutate('ShenJitFrontBindGuard', 'rocq/JitFrontInline.v',
       ' forallb (fun n => negb (reads_id n)) nargs && F.bind_site fold D nargs e.',
       ' F.bind_site fold D nargs e.')
mutate('ShenJitFrontChainFinalThrow', 'rocq/JitFrontInline.v',
       ' && is_final (next_r R P (iter N c0)) && no_trap (kont (iter N c0)) && not_throw (iter N c0).',
       ' && is_final (next_r R P (iter N c0)) && no_trap (kont (iter N c0)).')
cf = 'rocq/JitFrontCopyFold.v'
mutate('ShenJitFrontFoldNoRange', cf,
       "     if (text_eqb f plus_name && d_has D plus_name is_add && fits (x + y))%bool then Some (x + y)%Z",
       "     if (text_eqb f plus_name && d_has D plus_name is_add)%bool then Some (x + y)%Z")
mutate('ShenJitFrontFoldNoPrim', cf,
       "     if (text_eqb f plus_name && d_has D plus_name is_add && fits (x + y))%bool then Some (x + y)%Z",
       "     if (text_eqb f plus_name && fits (x + y))%bool then Some (x + y)%Z")
mutate('ShenJitFrontFoldMinusAdds', cf,
       "     else if (text_eqb f minus_name && d_has D minus_name is_sub && fits (x - y))%bool then Some (x - y)%Z",
       "     else if (text_eqb f minus_name && d_has D minus_name is_sub && fits (x - y))%bool then Some (x + y)%Z")
mutate('ShenJitFrontCfVarScope', cf,
       " | EVar x, EVar y => text_eqb x y && bound g x\n",
       " | EVar x, EVar y => text_eqb x y\n")
mutate('ShenJitFrontCopyLetScope', cf,
       "     rec (KF x b0 (K.fv b0) :: drop x F) (rem x g) body0 e",
       "     rec (KF x b0 (K.fv b0) :: drop x F) g body0 e")
mutate('ShenJitFrontCopyNoDrop', cf,
       " | ELam x b0, ELam y b => text_eqb x y && rec (drop x F) (x :: g) b0 b",
       " | ELam x b0, ELam y b => text_eqb x y && rec F (x :: g) b0 b")
mutate('ShenJitFrontLamArgScope', cf,
       "forall2b (rec (dropl (p :: ps) F) (reml (p :: ps) g)) (a1 :: as0) as1",
       "forall2b (rec (dropl (p :: ps) F) g) (a1 :: as0) as1")
mutate('ShenJitFrontKcInvIdKey', cf,
       " | KF x e0 gl => x <> id_key /\\ ~ In id_key gl /\\",
       " | KF x e0 gl => x <> id_key /\\")
mutate('ShenJitFrontThawNoD', cf,
       " | ECall f [EVar x] => text_eqb f FD.thaw_name && d_has D FD.thaw_name is_thaw_body &&",
       " | ECall f [EVar x] => text_eqb f FD.thaw_name &&")
mutate('ShenJitFrontCopyBindScope', cf,
       "     FD.binder_ok p1 a1 && FD.binder_ok p2 a2 && FD.binder_ok p3 a3 && FD.disjoint [a1; a2; a3] g &&",
       "     FD.binder_ok p1 a1 && FD.binder_ok p2 a2 && FD.binder_ok p3 a3 && FD.disjoint [a1; a2; a3] [] &&")
mutate('ShenJitFrontCopyBindDrop', cf,
       "     rec F g x0 x && rec (dropl [a1] F) g y0 y && rec (dropl [a2; a1] F) g b0 b &&",
       "     rec F g x0 x && rec F g y0 y && rec (dropl [a2; a1] F) g b0 b &&")
print(' '.join(names))
