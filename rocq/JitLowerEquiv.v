(* Shen/JIT Phase 2, the lowerer's front passes: name preservation for the KRef split (K00).
   Until K00 this file held KRef's statements and proofs. They now live in
     JitKRef.v         every Definition, Fixpoint, Inductive and *_statement (the interface),
     JitKRefGround.v   the premise specifications, ground lemmas, KRel_top, FromFundamental,
     JitKRefCompose.v  VR_fo, the combine lemmas, call_preservation_src_of_fundamental,
   each with its old text and, after its Sections close, its old type and argument order
   (JitKRef.v's header has the file map). Importers name the constants by their old qualified paths
   (Audit_Jit.v, JitEqBudget.v, the lane scripts), and Require Export would not keep those paths,
   so this module gives each old name an only-parsing abbreviation of the moved constant. It
   declares no constant of its own: `Print Assumptions JitLowerEquiv.JitLowerEquiv.<name>` audits
   the moved constant itself (checked when K00 was made: Print Assumptions accepts an abbreviation).
   The design notes that headed this file are at the top of JitKRef.v. *)
From Buri Require Import JitBytecode JitKRef JitKRefGround JitKRefCompose.
Set Warnings "-notation-for-abbreviation".
Module JitLowerEquiv.
Module B := JitBytecode.JitBytecode.
Notation runs_ind := JitKRef.JitKRef.runs_ind (only parsing).
Notation runs_sind := JitKRef.JitKRef.runs_sind (only parsing).
Notation srun := JitKRef.JitKRef.srun (only parsing).
Notation world := JitKRef.JitKRef.world (only parsing).
Notation wf_world := JitKRef.JitKRef.wf_world (only parsing).
Notation wext := JitKRef.JitKRef.wext (only parsing).
Notation same_id := JitKRef.JitKRef.same_id (only parsing).
Notation StoreHas := JitKRef.JitKRef.StoreHas (only parsing).
Notation GVal := JitKRef.JitKRef.GVal (only parsing).
Notation GStore := JitKRef.JitKRef.GStore (only parsing).
Notation ObsT := JitKRef.JitKRef.ObsT (only parsing).
Notation SRel_with := JitKRef.JitKRef.SRel_with (only parsing).
Notation EnvRel_with := JitKRef.JitKRef.EnvRel_with (only parsing).
Notation KRel_with := JitKRef.JitKRef.KRel_with (only parsing).
Notation ERel_with := JitKRef.JitKRef.ERel_with (only parsing).
Notation VBody := JitKRef.JitKRef.VBody (only parsing).
Notation VRelF := JitKRef.JitKRef.VRelF (only parsing).
Notation VRel := JitKRef.JitKRef.VRel (only parsing).
Notation SRel := JitKRef.JitKRef.SRel (only parsing).
Notation KRel := JitKRef.JitKRef.KRel (only parsing).
Notation ERel := JitKRef.JitKRef.ERel (only parsing).
Notation KRef := JitKRef.JitKRef.KRef (only parsing).
Notation ns_stage0 := JitKRef.JitKRef.ns_stage0 (only parsing).
Notation ns_runtime := JitKRef.JitKRef.ns_runtime (only parsing).
Notation lowerer_prefixes := JitKRef.JitKRef.lowerer_prefixes (only parsing).
Notation lowerer_fixed := JitKRef.JitKRef.lowerer_fixed (only parsing).
Notation prefixb := JitKRef.JitKRef.prefixb (only parsing).
Notation digitb := JitKRef.JitKRef.digitb (only parsing).
Notation fresh_shape := JitKRef.JitKRef.fresh_shape (only parsing).
Notation reserved := JitKRef.JitKRef.reserved (only parsing).
Notation names := JitKRef.JitKRef.names (only parsing).
Notation D_bodies := JitKRef.JitKRef.D_bodies (only parsing).
Notation fresh_ok := JitKRef.JitKRef.fresh_ok (only parsing).
Notation binders := JitKRef.JitKRef.binders (only parsing).
Notation no_keyword_binders := JitKRef.JitKRef.no_keyword_binders (only parsing).
Notation D_wf := JitKRef.JitKRef.D_wf (only parsing).
Notation D_compiled := JitKRef.JitKRef.D_compiled (only parsing).
Notation scoped := JitKRef.JitKRef.scoped (only parsing).
Notation id_world := JitKRef.JitKRef.id_world (only parsing).
Notation fresh_ok_spec_statement := JitKRef.JitKRef.fresh_ok_spec_statement (only parsing).
Notation no_keyword_binders_spec_statement := JitKRef.JitKRef.no_keyword_binders_spec_statement (only parsing).
Notation D_compiled_spec_statement := JitKRef.JitKRef.D_compiled_spec_statement (only parsing).
Notation eq_budget_statement := JitKRef.JitKRef.eq_budget_statement (only parsing).
Notation jit_eq_per_statement := JitKRef.JitKRef.jit_eq_per_statement (only parsing).
Notation sealed_stable_statement := JitKRef.JitKRef.sealed_stable_statement (only parsing).
Notation storehas_stable_statement := JitKRef.JitKRef.storehas_stable_statement (only parsing).
Notation VRelF_index_statement := JitKRef.JitKRef.VRelF_index_statement (only parsing).
Notation VRel_down_statement := JitKRef.JitKRef.VRel_down_statement (only parsing).
Notation VRel_wext_statement := JitKRef.JitKRef.VRel_wext_statement (only parsing).
Notation ERel_down_statement := JitKRef.JitKRef.ERel_down_statement (only parsing).
Notation VRel_ground_statement := JitKRef.JitKRef.VRel_ground_statement (only parsing).
Notation SRel_ground_statement := JitKRef.JitKRef.SRel_ground_statement (only parsing).
Notation compose_world := JitKRef.JitKRef.compose_world (only parsing).
Notation GVal_trans_statement := JitKRef.JitKRef.GVal_trans_statement (only parsing).
Notation GStore_trans_statement := JitKRef.JitKRef.GStore_trans_statement (only parsing).
Notation KRel_top_statement := JitKRef.JitKRef.KRel_top_statement (only parsing).
Notation EnvRelAll := JitKRef.JitKRef.EnvRelAll (only parsing).
Notation fundamental_statement := JitKRef.JitKRef.fundamental_statement (only parsing).
Notation KRef_refl_statement := JitKRef.JitKRef.KRef_refl_statement (only parsing).
Notation store_refl_statement := JitKRef.JitKRef.store_refl_statement (only parsing).
Notation compat_lit_statement := JitKRef.JitKRef.compat_lit_statement (only parsing).
Notation compat_var_statement := JitKRef.JitKRef.compat_var_statement (only parsing).
Notation compat_let_statement := JitKRef.JitKRef.compat_let_statement (only parsing).
Notation compat_if_statement := JitKRef.JitKRef.compat_if_statement (only parsing).
Notation compat_and_statement := JitKRef.JitKRef.compat_and_statement (only parsing).
Notation compat_or_statement := JitKRef.JitKRef.compat_or_statement (only parsing).
Notation compat_cond_statement := JitKRef.JitKRef.compat_cond_statement (only parsing).
Notation compat_type_statement := JitKRef.JitKRef.compat_type_statement (only parsing).
Notation compat_trap_statement := JitKRef.JitKRef.compat_trap_statement (only parsing).
Notation compat_lambda_statement := JitKRef.JitKRef.compat_lambda_statement (only parsing).
Notation compat_freeze_statement := JitKRef.JitKRef.compat_freeze_statement (only parsing).
Notation compat_call_statement := JitKRef.JitKRef.compat_call_statement (only parsing).
Notation compat_app_statement := JitKRef.JitKRef.compat_app_statement (only parsing).
Notation compat_defun_statement := JitKRef.JitKRef.compat_defun_statement (only parsing).
Notation KRef_scope_statement := JitKRef.JitKRef.KRef_scope_statement (only parsing).
Notation fo := JitKRef.JitKRef.fo (only parsing).
Notation fo_ind := JitKRef.JitKRef.fo_ind (only parsing).
Notation fo_sind := JitKRef.JitKRef.fo_sind (only parsing).
Notation adequacy_statement := JitKRef.JitKRef.adequacy_statement (only parsing).
Notation srun_nil_Sstar_statement := JitKRef.JitKRef.srun_nil_Sstar_statement (only parsing).
Notation fresh_ok_spec := JitKRefGround.JitKRefGround.fresh_ok_spec (only parsing).
Notation no_keyword_binders_spec := JitKRefGround.JitKRefGround.no_keyword_binders_spec (only parsing).
Notation D_compiled_spec := JitKRefGround.JitKRefGround.D_compiled_spec (only parsing).
Notation runs_srun := JitKRefGround.JitKRefGround.runs_srun (only parsing).
Notation srun_runs := JitKRefGround.JitKRefGround.srun_runs (only parsing).
Notation srun_nil_Sstar := JitKRefGround.JitKRefGround.srun_nil_Sstar (only parsing).
Notation step_from_ret_top := JitKRefGround.JitKRefGround.step_from_ret_top (only parsing).
Notation no_step_from_throw_top := JitKRefGround.JitKRefGround.no_step_from_throw_top (only parsing).
Notation wext_refl := JitKRefGround.JitKRefGround.wext_refl (only parsing).
Notation In_compose := JitKRefGround.JitKRefGround.In_compose (only parsing).
Notation In_compose_inv := JitKRefGround.JitKRefGround.In_compose_inv (only parsing).
Notation nodup_fst_uniq := JitKRefGround.JitKRefGround.nodup_fst_uniq (only parsing).
Notation nodup_snd_uniq := JitKRefGround.JitKRefGround.nodup_snd_uniq (only parsing).
Notation filter_fst_nil := JitKRefGround.JitKRefGround.filter_fst_nil (only parsing).
Notation filter_fst_small := JitKRefGround.JitKRefGround.filter_fst_small (only parsing).
Notation wf_compose := JitKRefGround.JitKRefGround.wf_compose (only parsing).
Notation wext_compose_id := JitKRefGround.JitKRefGround.wext_compose_id (only parsing).
Notation id_world_wf := JitKRefGround.JitKRefGround.id_world_wf (only parsing).
Notation id_world_in := JitKRefGround.JitKRefGround.id_world_in (only parsing).
Notation id_world_inv := JitKRefGround.JitKRefGround.id_world_inv (only parsing).
Notation same_id_trans := JitKRefGround.JitKRefGround.same_id_trans (only parsing).
Notation GVal_partial := JitKRefGround.JitKRefGround.GVal_partial (only parsing).
Notation GVal_trans := JitKRefGround.JitKRefGround.GVal_trans (only parsing).
Notation Forall2_trans_gen := JitKRefGround.JitKRefGround.Forall2_trans_gen (only parsing).
Notation GStore_trans := JitKRefGround.JitKRefGround.GStore_trans (only parsing).
Notation GVal_fo := JitKRefGround.JitKRefGround.GVal_fo (only parsing).
Notation leb_S_false := JitKRefGround.JitKRefGround.leb_S_false (only parsing).
Notation VRel_unfold := JitKRefGround.JitKRefGround.VRel_unfold (only parsing).
Notation VRelF_index := JitKRefGround.JitKRefGround.VRelF_index (only parsing).
Notation VBody_partial := JitKRefGround.JitKRefGround.VBody_partial (only parsing).
Notation VBody_ground := JitKRefGround.JitKRefGround.VBody_ground (only parsing).
Notation VRel_ground := JitKRefGround.JitKRefGround.VRel_ground (only parsing).
Notation SRel_with_ground := JitKRefGround.JitKRefGround.SRel_with_ground (only parsing).
Notation SRel_ground := JitKRefGround.JitKRefGround.SRel_ground (only parsing).
Notation SRel_with_wf := JitKRefGround.JitKRefGround.SRel_with_wf (only parsing).
Notation obs_top_throw := JitKRefGround.JitKRefGround.obs_top_throw (only parsing).
Notation obs_top_ret := JitKRefGround.JitKRefGround.obs_top_ret (only parsing).
Notation KRel_top := JitKRefGround.JitKRefGround.KRel_top (only parsing).
Notation KRel_with_ext := JitKRefGround.JitKRefGround.KRel_with_ext (only parsing).
Notation ERel_with_ext := JitKRefGround.JitKRefGround.ERel_with_ext (only parsing).
Notation same_id_refl := JitKRefGround.JitKRefGround.same_id_refl (only parsing).
Notation Forall2_refl_env := JitKRefGround.JitKRefGround.Forall2_refl_env (only parsing).
Notation vrefl := JitKRefGround.JitKRefGround.vrefl (only parsing).
Notation store_refl_of_fundamental := JitKRefGround.JitKRefGround.store_refl_of_fundamental (only parsing).
Notation fo_vok := JitKRefGround.JitKRefGround.fo_vok (only parsing).
Notation lookup_In := JitKRefGround.JitKRefGround.lookup_In (only parsing).
Notation adequacy_of_fundamental := JitKRefGround.JitKRefGround.adequacy_of_fundamental (only parsing).
Notation EndsSrc_ind := JitKRef.JitKRef.EndsSrc_ind (only parsing).
Notation EndsSrc_sind := JitKRef.JitKRef.EndsSrc_sind (only parsing).
Notation call_preservation_src_statement := JitKRef.JitKRef.call_preservation_src_statement (only parsing).
Notation VR_fo := JitKRefCompose.JitKRefCompose.VR_fo (only parsing).
Notation ArgsAt_fo := JitKRefCompose.JitKRefCompose.ArgsAt_fo (only parsing).
Notation combine_fo := JitKRefCompose.JitKRefCompose.combine_fo (only parsing).
Notation lookup_combine := JitKRefCompose.JitKRefCompose.lookup_combine (only parsing).
Notation call_preservation_src_of_fundamental := JitKRefCompose.JitKRefCompose.call_preservation_src_of_fundamental (only parsing).
Notation runs := JitKRef.JitKRef.runs (only parsing).
Notation runs_0 := JitKRef.JitKRef.runs_0 (only parsing).
Notation runs_S := JitKRef.JitKRef.runs_S (only parsing).
Notation fo_num := JitKRef.JitKRef.fo_num (only parsing).
Notation fo_sym := JitKRef.JitKRef.fo_sym (only parsing).
Notation fo_bool := JitKRef.JitKRef.fo_bool (only parsing).
Notation fo_str := JitKRef.JitKRef.fo_str (only parsing).
Notation fo_nil := JitKRef.JitKRef.fo_nil (only parsing).
Notation fo_cons := JitKRef.JitKRef.fo_cons (only parsing).
Notation EndsSrc := JitKRef.JitKRef.EndsSrc (only parsing).
Notation ES_ok := JitKRef.JitKRef.ES_ok (only parsing).
Notation ES_err := JitKRef.JitKRef.ES_err (only parsing).
End JitLowerEquiv.
