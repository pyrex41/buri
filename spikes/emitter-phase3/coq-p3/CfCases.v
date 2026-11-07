(** * The per-instruction cases of the simulation (Shen/JIT Phase 0, spike 8). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim WxExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.Examples.emitter_p3_ns Require Import CfDefs CfStep CfRun CfSound CfStepSim.
Import ListNotations.
Open Scope bv_scope.

Section Cases.
Context {fx : FPState}.
Variable c : cfg.
Variable cell_of : Z -> option Z.
Variable segs : list Segment.
Variable rom : word -> option byte.
Variable regs0 : bvmap 5 word.
Variables fp vm : word.
Variable keq : word -> word -> bool.
Variables vtrue vfalse : word.
Hypothesis Htrue : tag3 vtrue <> 3%Z.
Hypothesis Hfalse : tag3 vfalse <> 3%Z.
Hypothesis Hkeq : forall x y, identity_tag (tag3 x) = true -> keq x y = bv_eqb x y /\ keq y x = bv_eqb x y.
Hypothesis WfK : forall i w, ckinds c i = Some (KImm w) -> (0 <= w < 2^64)%Z.
Variable p : list binstr.
Variable cut : nat -> Z.
Variable inv : nat -> option CS.
Variable fuel : nat.
Hypothesis ACC : check_all c cell_of p cut inv fuel = true.

Abbreviation Rel := (Rel c segs regs0 fp vm).
Abbreviation E st := (E fp vm st (Z_to_bv 64 0) (Z_to_bv 64 0)).
Abbreviation AtNext := (AtNext c segs rom regs0 fp vm p cut inv).
Abbreviation AtRet := (AtRet c segs rom regs0 fp vm).
Abbreviation steps := (steps segs).

Lemma wfv_false : forall st, wfv st vfalse.
Proof. intros st H. contradiction. Qed.
Lemma wfv_true : forall st, wfv st vtrue.
Proof. intros st H. contradiction. Qed.

Ltac getacc i ins H := pose proof (acc_at c cell_of rom vfalse p cut inv fuel ACC i ins H) as Hacc; unfold check_at in Hacc.
Abbreviation SIMSET := (sim_set c cell_of segs rom regs0 fp vm vfalse p cut inv fuel ACC).
Abbreviation SIMNONE := (sim_none c cell_of segs rom regs0 fp vm vfalse p cut inv fuel ACC).
Abbreviation RUN := (run_from c cell_of segs rom regs0 fp vm fuel).

Theorem sim_move : forall i s st regs m d o,
  nth_error p i = Some (IMove d o) -> inv i = Some s -> Rel s st regs m ->
  exists ms, steps (mkst regs (at_ c (cut i)) m rom) ms /\ AtNext (S i) (set_slot st d (opval st o)) ms.
Proof.
  intros i s st regs m d o Hn Hi R. getacc i (IMove d o) Hn. rewrite Hi, Hn in Hacc.
  destruct (run c cell_of (sP s) fuel (cut i) (cut (S i)) (y0 s)) as [r|] eqn:Hr; [|discriminate].
  destruct r; try discriminate. apply andb_true_iff in Hacc as [Hk Hp].
  destruct (RUN s st regs m _ _ _ R Hr) as (ms & Hs & Hend).
  cbn [Ends] in Hend. destruct Hend as (regs' & m' & -> & I).
  exists (mkst regs' (at_ c (cut (S i))) m' rom). split; [exact Hs|].
  eapply SIMSET; try eassumption.
  - pose proof (proj1 (nth_error_Some p i) ltac:(rewrite Hn; discriminate)). lia.
  - intros _. eapply abs_op_eval; eassumption.
  - eapply op_wf; eassumption.
  - intros. lia.
Qed.

Lemma i_lt : forall i ins, nth_error p i = Some ins -> (i < length p)%nat.
Proof. intros i ins H. apply nth_error_Some. rewrite H. discriminate. Qed.

Lemma bit_ok : forall x st_P, (Z.leb 0 x && Z.ltb x 64 && Z.testbit st_P x)%bool = true ->
  (0 <= x < 64)%Z /\ Z.testbit st_P x = true.
Proof.
  intros x st_P H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. auto.
Qed.

Definition hd_of (st : bstate) (x : Z) : word :=
  match bheap st (v_addi (bslots st x) (-3)) with Some v => v | None => Z_to_bv 64 0 end.
Definition tl_of (st : bstate) (x : Z) : word :=
  match bheap st (v_addi (bslots st x) 5) with Some v => v | None => Z_to_bv 64 0 end.

Theorem sim_hd : forall i s st regs m d x,
  nth_error p i = Some (IHd d x) -> inv i = Some s -> Rel s st regs m ->
  tag3 (bslots st x) = 3%Z /\ (exists v, bheap st (v_addi (bslots st x) (-3)) = Some v) /\
  exists ms, steps (mkst regs (at_ c (cut i)) m rom) ms /\ AtNext (S i) (set_slot st d (hd_of st x)) ms.
Proof.
  intros i s st regs m d x Hn Hi R. getacc i (IHd d x) Hn. rewrite Hi, Hn in Hacc.
  apply andb_true_iff in Hacc as [Hb Hacc]. destruct (bit_ok _ _ Hb) as (Hx & Hbit).
  pose proof (r_P _ _ _ _ _ _ _ _ _ R x Hx Hbit) as Ht.
  destruct (r_wf _ _ _ _ _ _ _ _ _ R x Ht) as ([v Hv] & _).
  split; [exact Ht|]. split; [eauto|].
  destruct (run c cell_of (sP s) fuel (cut i) (cut (S i)) (y0 s)) as [r|] eqn:Hr; [|discriminate].
  destruct r; try discriminate.
  destruct (RUN s st regs m _ _ _ R Hr) as (ms & Hs & Hend).
  cbn [Ends] in Hend. destruct Hend as (regs' & m' & -> & I).
  exists (mkst regs' (at_ c (cut (S i))) m' rom). split; [exact Hs|].
  eapply SIMSET; try eassumption.
  - pose proof (i_lt _ _ Hn). lia.
  - intros _. cbn [eval base_val CfSound.E e_st]. rewrite v_addi_0. reflexivity.
  - unfold hd_of. rewrite Hv. exact (r_wfh _ _ _ _ _ _ _ _ _ R _ _ Hv).
  - intros. lia.
Qed.

Theorem sim_tl : forall i s st regs m d x,
  nth_error p i = Some (ITl d x) -> inv i = Some s -> Rel s st regs m ->
  tag3 (bslots st x) = 3%Z /\ (exists v, bheap st (v_addi (bslots st x) 5) = Some v) /\
  exists ms, steps (mkst regs (at_ c (cut i)) m rom) ms /\ AtNext (S i) (set_slot st d (tl_of st x)) ms.
Proof.
  intros i s st regs m d x Hn Hi R. getacc i (ITl d x) Hn. rewrite Hi, Hn in Hacc.
  apply andb_true_iff in Hacc as [Hb Hacc]. destruct (bit_ok _ _ Hb) as (Hx & Hbit).
  pose proof (r_P _ _ _ _ _ _ _ _ _ R x Hx Hbit) as Ht.
  destruct (r_wf _ _ _ _ _ _ _ _ _ R x Ht) as (_ & [v Hv]).
  split; [exact Ht|]. split; [eauto|].
  destruct (run c cell_of (sP s) fuel (cut i) (cut (S i)) (y0 s)) as [r|] eqn:Hr; [|discriminate].
  destruct r; try discriminate.
  destruct (RUN s st regs m _ _ _ R Hr) as (ms & Hs & Hend).
  cbn [Ends] in Hend. destruct Hend as (regs' & m' & -> & I).
  exists (mkst regs' (at_ c (cut (S i))) m' rom). split; [exact Hs|].
  eapply SIMSET; try eassumption.
  - pose proof (i_lt _ _ Hn). lia.
  - intros _. cbn [eval base_val CfSound.E e_st]. rewrite v_addi_0. reflexivity.
  - unfold tl_of. rewrite Hv. exact (r_wfh _ _ _ _ _ _ _ _ _ R _ _ Hv).
  - intros. lia.
Qed.

Theorem sim_label : forall i s st regs m l,
  nth_error p i = Some (ILabel l) -> inv i = Some s -> Rel s st regs m ->
  exists ms, steps (mkst regs (at_ c (cut i)) m rom) ms /\ AtNext (S i) st ms.
Proof.
  intros i s st regs m l Hn Hi R. getacc i (ILabel l) Hn. rewrite Hi, Hn in Hacc.
  apply andb_true_iff in Hacc as [He Hp]. apply Z.eqb_eq in He.
  exists (mkst regs (at_ c (cut i)) m rom). split; [constructor|]. rewrite He.
  eapply SIMNONE; try eassumption.
  - pose proof (i_lt _ _ Hn). lia.
  - eapply (rel_inv c segs rom). exact R.
Qed.

Theorem sim_jump : forall i s st regs m l,
  nth_error p i = Some (IJump l) -> inv i = Some s -> Rel s st regs m ->
  exists li, find_label p l 0 = Some li /\
  exists ms, steps (mkst regs (at_ c (cut i)) m rom) ms /\ AtNext li st ms.
Proof.
  intros i s st regs m l Hn Hi R. getacc i (IJump l) Hn. rewrite Hi, Hn in Hacc.
  destruct (run c cell_of (sP s) fuel (cut i) (cut (S i)) (y0 s)) as [r|] eqn:Hr; [|discriminate].
  destruct (RUN s st regs m _ _ _ R Hr) as (ms & Hs & Hend).
  destruct r; try discriminate.
  - destruct (target p cut i l (cut (S i))) as [li|] eqn:Ht; [|discriminate].
    destruct (target_spec rom vfalse p cut i l _ li Ht) as (Hf & Hc & Hl).
    exists li. split; [exact Hf|].
    cbn [Ends] in Hend. destruct Hend as (regs' & m' & -> & I).
    exists (mkst regs' (at_ c (cut (S i))) m' rom). split; [exact Hs|]. rewrite <- Hc.
    eapply SIMNONE; try eassumption. lia.
  - destruct (target p cut i l t) as [li|] eqn:Ht; [|discriminate].
    destruct (target_spec rom vfalse p cut i l _ li Ht) as (Hf & Hc & Hl).
    exists li. split; [exact Hf|].
    cbn [Ends] in Hend. destruct Hend as (regs' & m' & -> & I).
    exists (mkst regs' (at_ c t) m' rom). split; [exact Hs|]. rewrite <- Hc.
    eapply SIMNONE; try eassumption. lia.
Qed.

Theorem sim_ret : forall i s st regs m o,
  nth_error p i = Some (IRet o) -> inv i = Some s -> Rel s st regs m ->
  exists ms, steps (mkst regs (at_ c (cut i)) m rom) ms /\ AtRet (opval st o) st ms.
Proof.
  intros i s st regs m o Hn Hi R. getacc i (IRet o) Hn. rewrite Hi, Hn in Hacc.
  destruct (run c cell_of (sP s) fuel (cut i) (cut (S i)) (y0 s)) as [r|] eqn:Hr; [|discriminate].
  destruct r; try discriminate.
  destruct (RUN s st regs m _ _ _ R Hr) as (ms & Hs & Hend).
  cbn [Ends] in Hend. destruct Hend as (regs' & m' & -> & I).
  repeat (apply andb_true_iff in Hacc as [Hacc ?]).
  rename Hacc into Hk. rename H into H9. rename H0 into H8. rename H1 into H19. rename H2 into H10.
  apply same_eq in H8. apply same_eq in H9. apply same_eq in H10. apply same_eq in H19.
  exists (mkst regs' (jalr_tgt (bslots st 0) 0) m' rom). split; [exact Hs|].
  do 2 eexists. split; [reflexivity|].
  split; [rewrite (A_at c segs regs0 _ _ _ _ 10 10 _ I eq_refl H10 Hk); eapply abs_op_eval; eassumption|].
  split; [rewrite (A_at c segs regs0 _ _ _ _ 8 8 _ I eq_refl H8 eq_refl); cbn [eval base_val CfSound.E e_fp]; apply v_addi_0|].
  split; [rewrite (A_at c segs regs0 _ _ _ _ 9 9 _ I eq_refl H9 eq_refl); cbn [eval base_val CfSound.E e_vm]; apply v_addi_0|].
  split; [rewrite (A_at c segs regs0 _ _ _ _ 19 19 _ I eq_refl H19 eq_refl); cbn [eval base_val CfSound.E e_st]; apply v_addi_0|].
  split; [exact (i_keep _ _ _ _ _ _ _ I)|].
  split; [exact (i_heap _ _ _ _ _ _ _ I)|].
  exact (i_code _ _ _ _ _ _ _ I).
Qed.

Lemma eval_tag : forall st x, eval (E st) (TagOf x) = alu64 ALU_AND (v_addi (bslots st x) (-3)) (sext 64 (7 : bv 12)).
Proof. reflexivity. Qed.

Theorem sim_consp : forall i s st regs m t x l,
  nth_error p i = Some (IConspJf t x l) -> inv i = Some s -> Rel s st regs m ->
  exists ms, steps (mkst regs (at_ c (cut i)) m rom) ms /\
  ((tag3 (bslots st x) = 3%Z /\ AtNext (S i) (set_slot st t vtrue) ms) \/
   (tag3 (bslots st x) <> 3%Z /\ exists li, find_label p l 0 = Some li /\ AtNext li (set_slot st t vfalse) ms)).
Proof.
  intros i s st regs m t x l Hn Hi R. getacc i (IConspJf t x l) Hn. rewrite Hi, Hn in Hacc.
  apply andb_true_iff in Hacc as [Hb Hacc].
  apply andb_true_iff in Hb as [Hx0 Hx1]. apply Z.leb_le in Hx0. apply Z.ltb_lt in Hx1.
  destruct (run c cell_of (sP s) fuel (cut i) (cut (S i)) (y0 s)) as [r|] eqn:Hr; [|discriminate].
  destruct r as [| | | | |cc w z tt y1 rest]; try discriminate.
  destruct cc; try discriminate. destruct rest; try discriminate.
  apply andb_true_iff in Hacc as [Hacc Htg]. apply andb_true_iff in Hacc as [Hw Hz].
  apply same_eq in Hw. apply same_eq in Hz. subst w z.
  destruct (target p cut i l tt) as [li|] eqn:Ht; [|discriminate].
  apply andb_true_iff in Htg as [Hpt Hpf].
  destruct (target_spec rom vfalse p cut i l _ li Ht) as (Hf & Hc & Hl).
  destruct (RUN s st regs m _ _ _ R Hr) as (ms & Hs & Hend).
  cbn [Ends] in Hend.
  rewrite eval_tag, eval_const, tag_taken in Hend.
  destruct (Z.eqb_spec (tag3 (bslots st x)) 3) as [Et|Et]; cbn [negb] in Hend.
  - destruct Hend as [(Hc' & _)|(_ & regs' & m' & -> & I)]; [discriminate|].
    exists (mkst regs' (at_ c (cut (S i))) m' rom). split; [exact Hs|]. left. split; [exact Et|].
    eapply SIMSET; try eassumption.
    + pose proof (i_lt _ _ Hn). lia.
    + intros Hk. discriminate.
    + apply wfv_true.
    + intros _ Hne. cbn [same_opt_d] in Hne. exact Et.
  - destruct Hend as [(_ & regs' & m' & -> & I)|(Hc' & _)]; [|discriminate].
    exists (mkst regs' (at_ c tt) m' rom). split; [exact Hs|]. right. split; [exact Et|].
    exists li. split; [exact Hf|]. rewrite <- Hc.
    eapply SIMSET; try eassumption.
    + lia.
    + intros Hk. discriminate.
    + apply wfv_false.
    + intros. lia.
Qed.

Lemma tag_imm : forall w, (0 <= w < 2^64)%Z -> tag3 (Z_to_bv 64 w) = Z.land w 7.
Proof. intros w Hw. unfold tag3. rewrite Z_to_bv_unsigned. f_equal. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

Lemma identity_keq : forall s st regs m a b, Rel s st regs m ->
  (identity_op c a || identity_op c b)%bool = true ->
  keq (opval st a) (opval st b) = bv_eqb (opval st a) (opval st b).
Proof.
  intros s st regs m a b R H.
  assert (Hid : forall o, identity_op c o = true -> identity_tag (tag3 (opval st o)) = true).
  { intros [n|k] Ho; cbn [identity_op] in Ho; [discriminate|]. cbn [opval].
    destruct (ckinds c k) as [[w|ad tg]|] eqn:Hk; try discriminate.
    - rewrite (r_imm _ _ _ _ _ _ _ _ _ R k w Hk), tag_imm by (eapply WfK; eassumption). exact Ho.
    - rewrite (r_tag _ _ _ _ _ _ _ _ _ R k ad tg Hk). exact Ho. }
  apply orb_true_iff in H as [H|H].
  - apply (Hkeq _ (opval st b) (Hid a H)).
  - rewrite (proj2 (Hkeq _ (opval st a) (Hid b H))). apply bv_eqb_sym.
Qed.

Theorem sim_eq : forall i s st regs m t a b l,
  nth_error p i = Some (IEqJf t a b l) -> inv i = Some s -> Rel s st regs m ->
  exists ms, steps (mkst regs (at_ c (cut i)) m rom) ms /\
  ((keq (opval st a) (opval st b) = true /\ AtNext (S i) (set_slot st t vtrue) ms) \/
   (keq (opval st a) (opval st b) = false /\ exists li, find_label p l 0 = Some li /\ AtNext li (set_slot st t vfalse) ms)).
Proof.
  intros i s st regs m t a b l Hn Hi R. getacc i (IEqJf t a b l) Hn. rewrite Hi, Hn in Hacc.
  apply andb_true_iff in Hacc as [Hid Hacc].
  rewrite (identity_keq s st regs m a b R Hid).
  destruct (run c cell_of (sP s) fuel (cut i) (cut (S i)) (y0 s)) as [r|] eqn:Hr; [|discriminate].
  destruct r as [| | | | |cc x w tt y1 rest]; try discriminate.
  destruct cc; try discriminate. destruct rest; try discriminate.
  apply andb_true_iff in Hacc as [Hsm Htg].
  destruct (target p cut i l tt) as [li|] eqn:Ht; [|discriminate].
  apply andb_true_iff in Htg as [Hpt Hpf].
  destruct (target_spec rom vfalse p cut i l _ li Ht) as (Hf & Hc & Hl).
  assert (Hxw : bv_eqb (eval (E st) x) (eval (E st) w) = bv_eqb (opval st a) (opval st b)).
  { apply orb_true_iff in Hsm as [Hsm|Hsm]; apply andb_true_iff in Hsm as [H1 H2];
      pose proof (same_known _ _ H1) as K1; pose proof (same_known _ _ H2) as K2;
      apply same_eq in H1; apply same_eq in H2; subst x w;
      rewrite !(abs_op_eval c segs regs0 fp vm s st regs m) by assumption; [reflexivity | apply bv_eqb_sym]. }
  destruct (RUN s st regs m _ _ _ R Hr) as (ms & Hs & Hend).
  cbn [Ends branch_taken] in Hend. rewrite Hxw in Hend.
  destruct (bv_eqb (opval st a) (opval st b)) eqn:Eq; cbn [negb] in Hend.
  - destruct Hend as [(Hc' & _)|(_ & regs' & m' & -> & I)]; [discriminate|].
    exists (mkst regs' (at_ c (cut (S i))) m' rom). split; [exact Hs|]. left. split; [reflexivity|].
    eapply SIMSET; try eassumption.
    + pose proof (i_lt _ _ Hn). lia.
    + intros Hk. discriminate.
    + apply wfv_true.
    + intros. lia.
  - destruct Hend as [(_ & regs' & m' & -> & I)|(Hc' & _)]; [|discriminate].
    exists (mkst regs' (at_ c tt) m' rom). split; [exact Hs|]. right. split; [reflexivity|].
    exists li. split; [exact Hf|]. rewrite <- Hc.
    eapply SIMSET; try eassumption.
    + lia.
    + intros Hk. discriminate.
    + apply wfv_false.
    + intros. lia.
Qed.

End Cases.
