#!/bin/bash
# Spike helper: replay a tactic prefix on cg_correct from the saved heap and print the goals left.
export CAKEMLDIR=/opt/cakeml HOLDIR=/opt/HOL PATH=/opt/HOL/bin:$PATH
cd /root/klfrag
{ cat <<'H'
val pm_ss = [pKB_def, pKI_def, pmatch_def, env_ok_def, same_type_def, same_ctor_def,
             Boolv_def, can_pmatch_all_def, evaluate_def, kerr_def, do_con_check_def,
             build_conv_def, v_rel_def, res_rel_def, pat_bindings_def, nsOptBind_def,
             do_app_def, do_arith_def, check_type_def, the_Litv_IntLit_def,
             getOpClass_def, nsAppend_def, alist_to_ns_def, nsLookup_def, nsBind_def];
val _ = set_trace "Goalstack.print_goal_at_top" 0;
g `∀e kenv env (st : 'ffi state) kt ke.
    keval kenv e ≠ KStuck ∧ vars_ok e ∧ env_ok env kt ke ∧ env_rel kt kenv env ⇒
    ∃r. evaluate st env [cg e] = (st, r) ∧ res_rel kt ke (keval kenv e) r`;
H
cat "$1"; } | hol --holstate=klfrag.cg_correct.dumpedheap 2>&1 | tail -${2:-80}
