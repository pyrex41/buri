"""Shen/JIT lane mutants; Rocq decides (each must be refused).

ShenJitAgreedRange, ShenJitAgreedArity, ShenJitAgreedWrites, ShenJitAgreedIdentity: an option of
  agreed_rules that isn't what KLSemantics does. next_r_agreed must fail.
ShenJitClosureIdentity: closures that always compare equal. closure_identity must fail.
ShenJitNoOverflow: no integer range in jit_rules. jit_overflow_raises must fail.
ShenJitRoundedCompare: comparison through a double, as before 0.3. jit_compare_exact must fail.
ShenJitBigChars: n->string up to 256. jit_byte_strings must fail.
ShenJitNoSealing: defun ignores the sealed set. jit_defun_sealed_refused must fail.
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
mutate('ShenJitNoSealing', 'rocq/JitProfile.v',
       '(fun _ f => negb (is_fixed_name f || existsb (text_eqb f) sealed))', '(fun _ f => negb (is_fixed_name f))')
print(' '.join(names))
