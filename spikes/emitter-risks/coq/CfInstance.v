(** * The theorem for one real function the JIT compiled (Shen/JIT Phase 0, spike 8). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Common Require Import PropExec.
From LinuxProcessSemantics.Examples.emitter_risks_ns Require Import CfDefs CfStep CfRun CfSound CfStepSim CfTop CfCaptured.
Import ListNotations.

(** The bytecode really is what [parse] reads from the words. *)
Lemma cap_parse : exists l, cap_parsed = Some l /\ map fst l = cap_starts.
Proof. eexists. split; vm_compute; reflexivity. Qed.

(** The checker accepts the captured bytes. *)
Lemma cap_accepted : check_all cap_cfg cap_cell_of cap_prog cap_cut cap_inv 64 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cap_wfk : forall i w, ckinds cap_cfg i = Some (KImm w) -> (0 <= w < 2^64)%Z.
Proof.
  intros i w H. cbn [ckinds cap_cfg] in H.
  repeat match type of H with context [Z.eqb i ?k] => destruct (Z.eqb i k) end; try discriminate;
  injection H as <-; lia.
Qed.

(** value.h: [V_TRUE = SPECIAL(2)], [V_FALSE = SPECIAL(1)]. *)
Definition v_true : word := Z_to_bv 64 18.
Definition v_false : word := Z_to_bv 64 10.
Lemma tag_true : tag3 v_true <> 3%Z. Proof. vm_compute. discriminate. Qed.
Lemma tag_false : tag3 v_false <> 3%Z. Proof. vm_compute. discriminate. Qed.

Section Instance.
Context {fx : FPState}.
Variable segs : list Segment.
Variable rom : word -> option byte.
Variable regs0 : bvmap 5 word.
Variables fp vm : word.
Variable keq : word -> word -> bool.
Hypothesis Hkeq : forall x y, identity_tag (tag3 x) = true -> keq x y = bv_eqb x y /\ keq y x = bv_eqb x y.

Theorem cap_run : forall i st j st', bsteps keq v_true v_false cap_prog i st j st' ->
  forall s regs m, cap_inv i = Some s -> Rel cap_cfg segs regs0 fp vm s st regs m -> (i < length cap_prog)%nat ->
  exists ms, steps segs (mkst regs (at_ cap_cfg (cap_cut i)) m rom) ms /\
  (AtNext cap_cfg segs rom regs0 fp vm cap_prog cap_cut cap_inv j st' ms \/
   exists k sk stk words, cap_inv k = Some sk /\ AtAlloc cap_cfg segs rom regs0 fp vm cap_cut sk stk k words ms).
Proof.
  eapply run_sim; try eassumption.
  - exact tag_true.
  - exact tag_false.
  - exact cap_wfk.
  - exact cap_accepted.
Qed.

Theorem cap_step : forall i s st regs m,
  cap_inv i = Some s -> Rel cap_cfg segs regs0 fp vm s st regs m -> (i < length cap_prog)%nat ->
  match bnext keq v_true v_false cap_prog i st with
  | BNext j st' => exists ms, steps segs (mkst regs (at_ cap_cfg (cap_cut i)) m rom) ms /\
      (AtNext cap_cfg segs rom regs0 fp vm cap_prog cap_cut cap_inv j st' ms \/
       exists words, AtAlloc cap_cfg segs rom regs0 fp vm cap_cut s st i words ms)
  | BReturn v st' => exists ms, steps segs (mkst regs (at_ cap_cfg (cap_cut i)) m rom) ms /\
      AtRet cap_cfg segs rom regs0 fp vm v st ms
  | BOther => False
  end.
Proof.
  intros. eapply step_sim; try eassumption.
  - exact tag_true.
  - exact tag_false.
  - exact cap_wfk.
  - exact cap_accepted.
Qed.

End Instance.
