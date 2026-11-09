"""Shen/JIT lane mutants; Rocq decides (each must be refused).

ShenJitAgreedRange, ShenJitAgreedArity, ShenJitAgreedWrites, ShenJitAgreedIdentity: an option of
  agreed_rules that isn't what KLSemantics does. next_r_agreed must fail.
ShenJitClosureIdentity: closures that always compare equal. closure_identity must fail.
ShenJitNoOverflow: no integer range in jit_rules. jit_overflow_raises must fail.
ShenJitRoundedCompare: comparison through a double, as before 0.3. jit_compare_exact must fail.
ShenJitBigChars: n->string up to 256. jit_byte_strings must fail.
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
ShenJitLowerEqSym: = agrees against a symbol constant. eq_core must fail.
ShenJitLowerEqNaN: = agrees against any real constant, NaN included. eq_core must fail
  (OB-JIT-NAN-IDENTITY).
ShenJitLowerCheckEqGuard: the checker admits = without a safe constant operand. chk_sound must fail.
ShenJitSymBase256: symbols as the name's elements in base 256, as before, which merges [1;1] with
  [65537]. text_of_sym_of_text must fail.
"""
from pathlib import Path
out = Path('_build/mutations')
out.mkdir(parents=True, exist_ok=True)
names = []

def mutate(name, path, old, new):
    src = Path(path).read_text()
    assert src.count(old) == 1, (name, old)
    (out / (name + '.v')).write_text(src.replace(old, new))
    names.append(name)

agreed = ' None scalar_ok false false (fun _ _ => true) (fun _ => true) false (fun _ => None).'
for name, new in [
    ('ShenJitAgreedRange', ' (Some (0%Z, 1%Z)) scalar_ok false false (fun _ _ => true) (fun _ => true) false (fun _ => None).'),
    ('ShenJitAgreedArity', ' None scalar_ok false true (fun _ _ => true) (fun _ => true) false (fun _ => None).'),
    ('ShenJitAgreedWrites', ' None scalar_ok false false (fun _ _ => true) (fun _ => true) true (fun _ => None).'),
    ('ShenJitAgreedIdentity', ' None scalar_ok true false (fun _ _ => true) (fun _ => true) false (fun _ => None).'),
]:
    mutate(name, 'rocq/KLPort.v', agreed, new)
mutate('ShenJitClosureIdentity', 'rocq/KLPort.v',
       '| Some x, Some y => Some (Nat.eqb x y)', '| Some x, Some y => Some true')
mutate('ShenJitNoOverflow', 'rocq/JitProfile.v',
       ' (Some (JitBytecode.JitBytecode.fix_min, JitBytecode.JitBytecode.fix_max))', ' None')
mutate('ShenJitRoundedCompare', 'rocq/JitProfile.v',
       ' | NInt x, NFloat y => jit_order p (JitBytecode.JitBytecode.compare_fix_real x y)',
       ' | NInt x, NFloat y => jit_order p (JitFloat.JitFloat.compare (JitFloat.JitFloat.of_Z x) y)')
mutate('ShenJitBigChars', 'rocq/JitProfile.v', 'Z.leb z 255', 'Z.leb z 256')
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
mutate('ShenJitEquivEndsSameStore', 'rocq/JitLowerEquiv.v',
       " | ES_ok v v' m2 s0 w : Sstar sealed c (Cfg (Ret v) [] s0)",
       " | ES_ok v v' m2 s0 w : Sstar sealed c (Cfg (Ret v) [] s)")
mutate('ShenJitEquivAdequacyStrict', 'rocq/JitLowerEquiv.v',
       "    exists s0 w, srun (Cfg (Eval rho e0) [] s) [] (Cfg (Ret v) [] s0) /\\ wext (id_world s) w /\\ GStore w s0 s') /\\",
       "    exists s0 w, srun (Cfg (Eval rho e0) [] s) [] (Cfg (Ret v) [] s') /\\ wext (id_world s) w /\\ GStore w s0 s') /\\")
mutate('ShenJitEquivComposeLeft', 'rocq/JitLowerEquiv.v',
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
print(' '.join(names))
