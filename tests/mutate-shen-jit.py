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
print(' '.join(names))
