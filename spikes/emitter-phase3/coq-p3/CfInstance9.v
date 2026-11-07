(** * Spike 9: the theorem for one real function the 0.4 JIT compiled, with a sealed call and a kept register. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Common Require Import PropExec.
From LinuxProcessSemantics.Examples.emitter_p3_ns Require Import CfDefs CfStep CfRun CfSound CfStepSim CfCall CfTop CfCaptured9.
Import ListNotations.

(** The bytecode really is what [parse] reads from the words. *)
Lemma sn_parse : exists l, sn_parsed = Some l /\ map fst l = sn_starts.
Proof. eexists. split; vm_compute; reflexivity. Qed.

Lemma sn_prog_is : sn_prog = [IMove 6 (OSlot 2); ICallS 3 4 1 3; IMove 4 (OConst 0);
  ICons 6 (OSlot 4) (OConst 1); ICons 5 (OSlot 3) (OSlot 6); IRet (OSlot 5)].
Proof. vm_compute. reflexivity. Qed.

(** The checker accepts the captured bytes. *)
Lemma sn_accepted : check_all sn_cfg sn_cell_of sn_prog sn_cut sn_inv 64 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sn_wfk : forall i w, ckinds sn_cfg i = Some (KImm w) -> (0 <= w < 2^64)%Z.
Proof.
  intros i w H. cbn [ckinds sn_cfg] in H.
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

Theorem sn_step : forall i s st regs m,
  sn_inv i = Some s -> Rel sn_cfg segs regs0 fp vm s st regs m -> (i < length sn_prog)%nat ->
  match bnext keq v_true v_false sn_prog i st with
  | BNext j st' => exists ms, steps segs (mkst regs (at_ sn_cfg (sn_cut i)) m rom) ms /\
      (AtNext sn_cfg segs rom regs0 fp vm sn_prog sn_cut sn_inv j st' ms \/
       exists words, AtAlloc sn_cfg segs rom regs0 fp vm sn_cut s st i words ms)
  | BReturn v st' => exists ms, steps segs (mkst regs (at_ sn_cfg (sn_cut i)) m rom) ms /\
      AtRet sn_cfg segs rom regs0 fp vm v st ms
  | BCall d a n k _ => exists ms, steps segs (mkst regs (at_ sn_cfg (sn_cut i)) m rom) ms /\
      AtCall sn_cfg segs rom regs0 fp vm sn_prog sn_cut sn_inv s st i d a n k ms
  | BOther => False
  end.
Proof.
  intros. eapply step_sim; try eassumption.
  - exact tag_true.
  - exact tag_false.
  - exact sn_wfk.
  - exact sn_accepted.
Qed.

(** The call, spelled out: from instruction 1, related to [st], the machine reaches the callee's entry
    with the window set up, and every return by the callee's contract reaches instruction 2. *)
Corollary sn_call : forall s st regs m,
  sn_inv 1 = Some s -> Rel sn_cfg segs regs0 fp vm s st regs m ->
  exists ms, steps segs (mkst regs (at_ sn_cfg (sn_cut 1)) m rom) ms /\
    AtCall sn_cfg segs rom regs0 fp vm sn_prog sn_cut sn_inv s st 1 3 4 1 3 ms.
Proof.
  intros s st regs m Hi R.
  pose proof (sn_step 1 s st regs m Hi R ltac:(rewrite sn_prog_is; cbn; lia)) as H.
  unfold bnext, CfDefs.bnext in H. rewrite sn_prog_is in H. exact H.
Qed.
End Instance.
