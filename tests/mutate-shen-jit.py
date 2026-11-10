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
ShenJitLowerEqSym: = agrees against a symbol constant. eq_core must fail.
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
ShenJitKRefKRelStrict: KRel_with quantifies over j < k instead of j <= k, so a continuation is no
  longer related at its own index. Built as JitKRef.v + JitKRefGround.v + JitKRefBase.v; rejected.
ShenJitKRefDefunSealed: jit_rules' defun_allowed admits sealed names. The single-file mutant is
  JitProfile.v, so jit_defun_sealed_refused rejects it first; sealed_step (JitKRefBase) reads the same
  option.
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
mutate('ShenJitLowerEqSym', 'rocq/JitLowerPrim.v', eq_core,
       "VR a a' -> VR b b' -> existsb (fun w => eq_safe_val w || match w with B.VSym _ => true | _ => false end) [a'; b'] = true ->\n exists r,")
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
mutate_chain('ShenJitKRefKRelStrict', ['rocq/JitKRef.v', 'rocq/JitKRefGround.v', 'rocq/JitKRefBase.v'],
       "Definition KRel_with (k : nat) (w : world) (K0 K : list frame) : Prop :=\n forall j, (j <= k)%nat ->",
       "Definition KRel_with (k : nat) (w : world) (K0 K : list frame) : Prop :=\n forall j, (j < k)%nat ->")
mutate('ShenJitKRefDefunSealed', 'rocq/JitProfile.v',
       '(fun _ f => negb (is_fixed_name f || existsb (text_eqb f) sealed))',
       '(fun _ f => negb (is_fixed_name f) || existsb (text_eqb f) sealed)')
print(' '.join(names))
