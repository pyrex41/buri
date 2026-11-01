"""EQ-1 adversarial reference kernels and models; Rocq decides (each must fail)."""
from pathlib import Path
out = Path('_build/mutations')
out.mkdir(parents=True, exist_ok=True)
kernel = Path('rocq/EqualityInductionKernel.v').read_text()
model = Path('rocq/EqualityInductionModel.v').read_text()
mutants = [
    ('EQ1NoConclusionCheck', kernel,
     '| Nil => if same l r then checked else rejected "conclusion-mismatch"', '| Nil => checked'),
    ('EQ1NoFreshness', kernel,
     'if r_allsym names && r_uniq names && r_fresh names (r_keys C) then',
     'if r_allsym names && r_uniq names then'),
    ('EQ1NoTheoryCheck', kernel,
     'Definition r_check_bundle T B N := if same T theory_value then',
     'Definition r_check_bundle T B N := if true then'),
    ('EQ1InjectedDefinition', model,
     '(ap "nadd" [ap "succ" [v "x"];v "y"]) (ap "succ" [ap "nadd" [v "x";v "y"]]);',
     '(ap "nadd" [ap "succ" [v "x"];v "y"]) (ap "nadd" [v "x";v "y"]);'),
    ('EQ1NatHypothesis', model,
     '   if String.eqb "expr" e\n', '   if String.eqb "nat" e\n'),
]
for name, source, old, new in mutants:
    assert source.count(old) == 1, name
    (out / (name + '.v')).write_text(source.replace(old, new))

# Captured-driver mutants (EQ1-DRIVERS): a structurally modified captured
# body must not satisfy its refinement lemma. Each mutant keeps the shared
# framework and only the lemma about the modified body; Rocq decides.
drivers = Path('rocq/EqualityInductionDrivers.v').read_text()
def body_def(short, name):
    return 'Definition b_%s := Eval vm_compute in def_body "%s".' % (short, name)
def mutated(short, name, rewrite):
    return 'Definition b_%s := Eval vm_compute in match def_body "%s" with %s | e0 => e0 end.' % (short, name, rewrite)
driver_mutants = [
    ('EQ1DriverNoConclusionCheck', 'steps', 'kl:buri.check-steps', 'body_steps',
     'If c (If _ a _) rest => If c a rest'),
    ('EQ1DriverSwappedDirection', 'csr', 'kl:buri.check-step-result', 'body_csr',
     'If c1 a1 (If c2 a2 r) => If c1 a2 (If c2 a1 r)'),
    ('EQ1DriverNoFreshness', 'cases', 'kl:buri.check-cases', 'body_cases',
     'If c1 t (If c2 (If (And a (And b _)) x y) z) => If c1 t (If c2 (If (And a b) x y) z)'),
    ('EQ1DriverNoTheoryCheck', 'cb', 'kl:buri.check-bundle', 'body_cb',
     'Call g [h;If _ a _] => Call g [h;a]'),
    ('EQ1DriverAcceptingHandler', 'cb', 'kl:buri.check-bundle', 'body_cb',
     'Call g [_;x] => Call g [Call "list" [Lit (Symbol "accepted")];x]'),
]
for name, short, kname, lemma, rewrite in driver_mutants:
    old = body_def(short, kname)
    assert drivers.count(old) == 1, name
    src = drivers.replace(old, mutated(short, kname, rewrite))
    start = src.index('Lemma ' + lemma + ' ')
    end = src.index('Qed.', start) + len('Qed.')
    text = src[:src.index('Lemma body_cb ')] + src[start:end] + '\n' + src[src.index('End Bodies.'):]
    (out / (name + '.v')).write_text(text)
    mutants.append((name, None, None, None))
print(' '.join(name for name, *_ in mutants))
