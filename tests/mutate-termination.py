"""EQ1-TERM and order-call progress mutants; Rocq decides (each must fail).

TermMemberNoProgress: a captured buri.member? whose recursive call passes the
  whole list instead of its tail (a non-decreasing recursive call). The same
  termination proof technique that proves the real body must not prove it.
TermBudgetDomainDropped: the guarded check-bundle body without the integer
  budget condition (a fractional budget makes Native reach an unsupported
  primitive), so the domain restriction is necessary.
TermCounterStuck: a gensym counter that does not advance; the progress proof
  of the fresh-name loop must fail.
"""
from pathlib import Path
out = Path('_build/mutations')
out.mkdir(parents=True, exist_ok=True)
header = '''From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Native EqualityInductionModel EqualityInductionSpecs EqualityInductionDrivers
 EqualityInductionRefinement EqualityInductionTrace EqualityInductionTotalBase EqualityInductionTermination.
Import ListNotations Native.Native EqualityInductionModel.EqualityInductionModel EqualityInductionSpecs.EqualityInductionSpecs
 EqualityInductionDrivers.EqualityInductionDrivers EqualityInductionTrace.EqualityInductionTrace
 EqualityInductionTotalBase.EqualityInductionTotalBase.
Open Scope string_scope.
'''
member_real = 'Call "kl:buri.member?" [Var "V5960"; Call "cdr" [Var "V5961"]]'
member_body = '''If (Call "null?" [Var "V5961"]) (Lit (Boolean false))
 (If (Call "pair?" [Var "V5961"])
  (Or (Call "kl:=" [Var "V5960"; Call "car" [Var "V5961"]])
   (Or (Call "kl:_scm.assert-boolean" [%s]) (Lit (Boolean false))))
  (Call "kl:shen.f-error" [Lit (Symbol "buri.member?")]))'''
real = member_body % member_real
mutant = member_body % 'Call "kl:buri.member?" [Var "V5960"; Var "V5961"]'
# The real body is checked to be the captured one before mutating it.
check = '''Lemma captured_member : def_of "kl:buri.member?" = Def ["V5960";"V5961"] (%s).
Proof. vm_compute. reflexivity. Qed.
''' % real
def member_case(body):
    # The inductive step of the termination proof for a member? body linked
    # into the program in place of the captured one: given termination of the
    # recursive call on every strictly smaller list, the traced run of the body
    # terminates. Calls are judged against the linked program.
    return '''Definition program_m := (("kl:buri.member?",Def ["V5960";"V5961"] (%s)) :: program)%%list.
Definition okm (c : call) := match c with (s,vs,w) => exists n, run n program_m s vs = Returned w end.
Definition Term_m rho e := match stepT oref rho e with Some (_,cs) => Forall okm cs | None => False end.
Lemma okm_w : forall s vs w w', okm (s,vs,w) -> w = w' -> okm (s,vs,w').
Proof. intros s vs w w' H <-; exact H. Qed.
Lemma okm_eq : forall a b, okm ("kl:=",[a;b],Boolean (same a b)).
Proof. intros a b. exists 5. vm_compute. reflexivity. Qed.
Lemma okm_assert : forall b, okm ("kl:_scm.assert-boolean",[Boolean b],Boolean b).
Proof. intros [|]; exists 5; vm_compute; reflexivity. Qed.
Create HintDb mdb.
#[local] Hint Resolve okm_eq okm_assert : mdb.
Lemma member_step : forall ys, (forall a b, ys = Pair a b -> forall x, lst b = true ->
   okm ("kl:buri.member?",[x;b],Boolean (r_mem x b))) ->
 forall x, lst ys = true -> Term_m (arguments ["V5960";"V5961"] [x;ys]) (%s).
Proof.
 intros ys IH x D. unfold Term_m.
 let e := eval cbv [lazify map] in (lazify (%s)) in change (%s) with e.
 tdrive; try contraT; ihs;
 repeat match goal with |- Forall _ (_ :: _) => apply Forall_cons | |- Forall _ [] => apply Forall_nil end;
 dom; try solve [eapply okm_w; [solve [eauto 5 with mdb]|weq]].
Qed.
''' % (body, body, body, body)
lemma = member_case(mutant)
control = member_case(real)
(out / 'TermMemberNoProgress.v').write_text(header + check + lemma)
domain = '''Lemma guarded_no_budget_domain : forall T B N, idata B = true -> Term oref (arguments p_cb [T;B;N]) g_cb.
Proof. intros T B N D1. tterm g_cb. Qed.
'''
(out / 'TermBudgetDomainDropped.v').write_text(header + domain)
order = Path('rocq/OrderCallProgress.v').read_text()
old = ' | Integer z => Out (Returned (Symbol (gname (z + 1)))) (Integer (z + 1)) []'
assert order.count(old) == 1
(out / 'TermCounterStuck.v').write_text(order.replace(old, ' | Integer z => Out (Returned (Symbol (gname (z + 1)))) (Integer z) []'))
(out / 'TermMemberControl.v').write_text(header + check + control)
print('TermMemberNoProgress TermBudgetDomainDropped TermCounterStuck')
