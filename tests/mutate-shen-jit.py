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
print(' '.join(names))
