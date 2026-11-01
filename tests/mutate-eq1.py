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
print(' '.join(name for name, *_ in mutants))
