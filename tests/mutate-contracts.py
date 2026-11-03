"""E2E-08 contract-logic mutants; Rocq decides (each must be refused).

ContractIfNoNonBool: r_if without its non-Boolean premise (unsound; see
  ContractPrims.if_nonbool_premise_needed). The soundness proof must fail.
ContractTotalNoMeasure: total-correctness bodies derived against the
  unrestricted context instead of ctx_below (unsound; see
  ContractPrims.unmeasured_recursion_unsound). rec_total must fail.
ContractPartialLe: currying rule aj_partial with <= instead of < (a saturated
  call is not a partial application). The soundness proof must fail.
ContractFailNoPolicy: G_fail without the resource-policy premise (a resource
  failure outside the recorded policy would be admitted). Must fail.
ContractVerdictNoBudget: the transported theorem without its budget-exhaustion
  disjunct (false: small budgets exhaust). Must fail.
ContractCertNoMeasureCheck: the certificate checker without the
  missing-measure test; check_total_measures must fail.
ContractWriteShort: write-byte claimed to return normally after a short
  write; write_byte_visible must fail.
"""
from pathlib import Path
out = Path('_build/mutations')
out.mkdir(parents=True, exist_ok=True)

def mutate(name, path, old, new):
    src = Path(path).read_text()
    assert src.count(old) == 1, (name, old)
    (out / (name + '.v')).write_text(src.replace(old, new))

mutate('ContractIfNoNonBool', 'rocq/ContractLogic.v',
       '     (forall v s1 t1, R v s1 t1 -> (forall bb, v <> VBool bb) -> E XNotBoolean s1 t1) ->\n     deriv m Gamma Pre rho (EIf c a b) Q E',
       '     deriv m Gamma Pre rho (EIf c a b) Q E')
mutate('ContractTotalNoMeasure', 'rocq/ContractLogic.v',
       ' deriv Total (ctx_below Ts Gx (td_meas T vs s0)) (fun s => s = s0)',
       ' deriv Total (map (fun T => fd_spec (td_def T)) Ts ++ Gx) (fun s => s = s0)')
mutate('ContractPartialLe', 'rocq/ContractLogic.v',
       'List.length (prev ++ vs) < fun_arity d /\\',
       'List.length (prev ++ vs) <= fun_arity d /\\')
mutate('ContractFailNoPolicy', 'rocq/ContractLogic.v',
       'Lemma G_fail : forall m Phi n h r k s, obs_ok Phi -> RP r -> G m Phi n h (Cfg (Fail r) k s).\nProof. intros; eapply G_final; [reflexivity|]. auto. Qed.',
       'Lemma G_fail : forall m Phi n h r k s, obs_ok Phi -> G m Phi n h (Cfg (Fail r) k s).\nProof. intros; eapply G_final; [reflexivity|]. auto. Qed.')
mutate('ContractVerdictNoBudget', 'rocq/ContractTransport.v',
       ' r = C.enc_verdict C.WBudget \\/ exists v, r = C.enc_verdict (C.WRet v) /\\ R.tr_rv v = ilist (map dbl l).',
       ' exists v, r = C.enc_verdict (C.WRet v) /\\ R.tr_rv v = ilist (map dbl l).')
mutate('ContractCertNoMeasureCheck', 'rocq/ContractCert.v',
       " else if (match snd (c_stmt c) with CTotal => negb (forallb (fun f => memb f (map fst (c_measures c))) (recs_used L)) | _ => false end)\n   then Rejected (t \"missing-measure\")\n",
       "")
mutate('ContractWriteShort', 'rocq/ContractPrims.v',
       "  (write_failed (EvIO (QWrite h [Z.to_N b]) r) -> exists e, kont r = OThrow (XIO e)) /\\",
       "  (write_failed (EvIO (QWrite h [Z.to_N b]) r) -> exists v s', kont r = ORet v s') /\\")
print('ContractIfNoNonBool ContractTotalNoMeasure ContractPartialLe ContractFailNoPolicy ContractVerdictNoBudget ContractCertNoMeasureCheck ContractWriteShort')
