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
ShenJitKRefCondSwap: a copy of compat_cond whose target is the clauses in reverse order
  (ECond (rev cl)), with compat_cond's own proof. cond tries clauses in order, so the copy is false
  and its proof must fail.
ShenJitKRefTrapNoPrim: compat_trap_fb (trap from fund_below k alone) proved from compat_trap_lt
  without supplying JitKRefPrim.prim_compat. compat_trap_lt's prim_compat_statement premise is then
  an open goal that no hypothesis closes, so the proof must fail: the fund_below-only form rests on
  primitive parametricity (a handler may be a partial primitive).
ShenJitKRefAppExnNoPrim: AppExn_fb proved from AppExn_of without JitKRefPrim.prim_compat; the same
  premise is left open and the proof must fail.
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
ShenJitKRefCallNoTable: SRel_with (and GStore, so that SRel_ground still holds) without the clause
  gfuns s0 = gfuns s, each replaced by True so no destructuring shifts. Built as JitKRef.v +
  JitKRefGround.v + JitKRefBase.v + JitKRefCompatClo.v; the first three compile, and Rocq rejects
  JitKRefCompatClo.call_rel, the named-call move compat_call (JitKRefCompatCall) rests on: with two
  function tables no longer equal, a call of f may run different definitions on the two sides.
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
mutate('ShenJitKRefCondSwap', 'rocq/JitKRefCompatCtl.v',
       "Theorem compat_type : compat_type_statement.",
       "Theorem compat_cond_swap : forall g cl0 cl,\n Forall2 (fun p0 p => KRef g (fst p0) (fst p) /\\ KRef g (snd p0) (snd p)) cl0 cl ->\n KRef g (ECond cl0) (ECond (rev cl)).\nProof.\n intros g cl0 cl F k w rho0 rho Ww HE. apply ERel_cond.\n eapply Forall2_impl; [|exact F]. intros p0 p [H1 H2]. split; [apply H1|apply H2]; assumption.\nQed.\n\nTheorem compat_type : compat_type_statement.")
mutate('ShenJitKRefTrapNoPrim', 'rocq/JitKRefCompatCtl.v',
       "Proof. intros k. exact (compat_trap_lt (JitKRefPrim.JitKRefPrim.prim_compat sealed D) k). Qed.",
       "Proof. intros k. apply compat_trap_lt; assumption. Qed.")
mutate('ShenJitKRefAppExnNoPrim', 'rocq/JitKRefCompatCtl.v',
       "Proof. intros k Hf. exact (AppExn_of (JitKRefPrim.JitKRefPrim.prim_compat sealed D) k Hf). Qed.",
       "Proof. intros k Hf. apply AppExn_of; [|exact Hf]; assumption. Qed.")
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

mutate_chain_n('ShenJitKRefCallNoTable',
       ['rocq/JitKRef.v', 'rocq/JitKRefGround.v', 'rocq/JitKRefBase.v', 'rocq/JitKRefCompatClo.v'],
       [(" gfuns s0 = gfuns s /\\\n Forall2 (fun p0 p => fst p0 = fst p /\\ GVal w",
         " True /\\\n Forall2 (fun p0 p => fst p0 = fst p /\\ GVal w"),
        ("StoreHas s0 /\\ StoreHas s /\\ gfuns s0 = gfuns s /\\",
         "StoreHas s0 /\\ StoreHas s /\\ True /\\")])
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
