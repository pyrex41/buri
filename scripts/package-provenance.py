"""Literal capture packaging only; selected-body acceptance is proved in Rocq."""
from pathlib import Path
import sys
kind, source, destination = sys.argv[1:]
if kind not in ('bootstrap', 'observer', 'compiler_pass', 'checked_io', 'order_call', 'observer_forms', 'io_read', 'equality_core', 'equality_seal', 'kernel_list', 'eq1_base', 'eq1_equations', 'eq1_theory', 'eq1_kernel', 'compiler_branches', 'kernel_element', 'e2e07_klambda'):
    raise SystemExit('Unknown packaging profile')
bits = Path(source).read_bytes()
if not bits or any(b not in b'01' for b in bits):
    raise SystemExit('Expected literal ASCII bits')
# Selection is explicit in the theorem input, not semantic Python decoding.
count, names = {'bootstrap': (2, ['kl:buri.native-bytes', 'kl:buri.native-node']),
                'observer': (1, ['kl:buri.install-observed']),
                'compiler_pass': (1, ['kl:_scm.merge-nested-lets']),
                'checked_io': (1, ['kl:buri.checked-write']),
                'order_call': (6, ['kl:_scm.merge-nested-lets','kl:_scm.simple-scheme-expression?','kl:_scm.has-computation?','kl:_scm.fresh-call-variable','kl:_scm.order-call-inputs','kl:_scm.order-call']),
                'observer_forms': (2, ['kl:buri.install-observed','kl:buri.observe-forms']),
                'io_read': (1, ['kl:read-file-as-string']),
                'equality_core': (4, ['kl:buri.eq2-derive','kl:buri.eq2-sym','kl:buri.eq2-trans','kl:buri.eq2-cong']),
                'kernel_list': (4, ['kl:buri.kernel.occurrences','kl:buri.kernel.reverse','kl:buri.kernel.reverse-help','kl:buri.kernel.not']),
                'equality_seal': (4, ['kl:buri.eq2-seal-definition','kl:buri.eq2-seal-program','kl:buri.eq2-seal-request','kl:buri.make-sealed-eq2']),
                # E2E-15 compiler branches: exact upstream defines read inside the
                # upstream package header, and the kernel element? they call.
                'compiler_branches': (8, ['kl:_scm.yields-boolean?','kl:_scm.force-boolean','kl:_scm.emit-symbol','kl:_scm.emit-let','kl:_scm.emit-if','kl:_scm.emit-cond','kl:_scm.emit-cond-clauses','kl:_scm.emit-equality-check']),
                'kernel_element': (1, ['kl:buri.kernel.element?']),
                # EQ-1: every definition of each source file, in source order.
                'eq1_base': (17, ['kl:buri.member?','kl:buri.unique?','kl:buri.append','kl:buri.rev','kl:buri.rev-h','kl:buri.get','kl:buri.keys','kl:buri.remove','kl:buri.nat?','kl:buri.index','kl:buri.every-list?','kl:buri.all-symbols?','kl:buri.check','kl:buri.exact-integer?','kl:buri.integer-spelling?','kl:buri.unsigned-spelling?','kl:buri.digits?']),
                'eq1_equations': (23, ['kl:buri.sig','kl:buri.sort','kl:buri.sort-app','kl:buri.args?','kl:buri.context?','kl:buri.context-h?','kl:buri.subst','kl:buri.subst-var','kl:buri.substs','kl:buri.substitution?','kl:buri.rule','kl:buri.match','kl:buri.bind','kl:buri.bind-h','kl:buri.matches','kl:buri.reduce','kl:buri.reduce-match','kl:buri.normalize','kl:buri.norm','kl:buri.norm-list','kl:buri.norm-list-h','kl:buri.norm-args-result','kl:buri.norm-reduced']),
                'eq1_theory': (4, ['kl:buri.signature','kl:buri.constructors','kl:buri.rules','kl:buri.theory']),
                # E2E-07: every definition of the KL-PURE-1 reference evaluator, in source order.
                'e2e07_klambda': (26, ['kl:buri.literal?','kl:buri.expression?','kl:buri.expressions?','kl:buri.definitions?','kl:buri.definitions-h?','kl:buri.definition-names','kl:buri.definition','kl:buri.evaluate','kl:buri.eval','kl:buri.lookup-value','kl:buri.eval-let','kl:buri.eval-if','kl:buri.eval-function','kl:buri.eval-argument','kl:buri.apply-value','kl:buri.apply-global','kl:buri.apply-bound','kl:buri.eval-args','kl:buri.eval-args-first','kl:buri.eval-args-rest','kl:buri.eval-primitive','kl:buri.primitive','kl:buri.eval-raise','kl:buri.eval-trap','kl:buri.eval-handler','kl:buri.eval-thaw']),
                'eq1_kernel': (22, ['kl:buri.check-bundle','kl:buri.bundle-h','kl:buri.bundle-next','kl:buri.goal?','kl:buri.check-theorem','kl:buri.check-cases','kl:buri.fresh?','kl:buri.zip','kl:buri.zip-h','kl:buri.variables','kl:buri.check-case-bound','kl:buri.induction-hyps','kl:buri.check-steps','kl:buri.resolve','kl:buri.instantiate','kl:buri.check-step-result','kl:buri.after-rewrite','kl:buri.replace','kl:buri.replace-arg','kl:buri.replace-head','kl:buri.replace-tail','kl:buri.replace-app'])}[kind]
text = '''From Coq Require Import List String.
From Buri Require Import Wire Native.
Import ListNotations Native.Native.
Open Scope string_scope.
Definition CAP_text : string := "BITS".
Definition CAP_nodes :=
 match Wire.decode_text CAP_text with
 | Some (Wire.Cons (Wire.Atom false "buri-constructor-native-1") (Wire.Cons tagged Wire.Nil)) =>
   match untag 500 tagged with Some root => elements root | _ => None end
 | _ => None end.
Definition CAP_decode := match CAP_nodes with
 | Some xs => definitions 500 (firstn COUNT (skipn OFFSET xs)) | None => None end.
Definition CAP_program := Eval vm_compute in
 match CAP_decode with Some ds => ds | None => [] end.
Theorem CAP_exact : CAP_decode = Some CAP_program.
Proof. vm_compute. reflexivity. Qed.
Theorem CAP_names : map fst CAP_program = NAMES.
Proof. vm_compute. reflexivity. Qed.
Global Opaque CAP_text CAP_nodes CAP_decode.
'''
text = text.replace('CAP', kind).replace('BITS', bits.decode('ascii')).replace('COUNT', str(count))
text = text.replace('OFFSET', '3' if kind == 'checked_io' else '0')
text = text.replace('NAMES', '[' + ';'.join('"' + n + '"' for n in names) + ']')
if kind in ('equality_core','equality_seal','kernel_list','compiler_branches','kernel_element','eq1_','e2e07_klambda') or kind.startswith('eq1_'):
    complete = ('Theorem '+kind+'_complete : match '+kind+'_nodes with\n'
                ' | Some xs => List.length xs = '+str(count)+' | None => False end.\n'
                'Proof. vm_compute; reflexivity. Qed.\n')
    text = text.replace('Global Opaque', complete+'Global Opaque')
if kind.startswith('eq1_') or kind == 'e2e07_klambda':
    # Large captures overflow Coq's parser as one literal: emit ordered chunks
    # whose concatenation is the capture (checked literally by the checker).
    raw = bits.decode('ascii')
    pieces = [raw[i:i + 40000] for i in range(0, len(raw), 40000)]
    chunks = ''.join('Definition %s_text_%d : string := "%s".\n' % (kind, i, p) for i, p in enumerate(pieces))
    joined = 'Definition %s_text : string := (%s)%%string.\n' % (kind, ' ++ '.join('%s_text_%d' % (kind, i) for i in range(len(pieces))))
    single = 'Definition %s_text : string := "%s".\n' % (kind, raw)
    assert text.count(single) == 1
    text = text.replace(single, chunks + joined)
    text = text.replace('Global Opaque ' + kind + '_text ', 'Global Opaque ' + ' '.join('%s_text_%d' % (kind, i) for i in range(len(pieces))) + ' ' + kind + '_text ')
Path(destination).write_text(text)
