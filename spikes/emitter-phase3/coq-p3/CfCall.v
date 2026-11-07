(** * Spike 9: the sealed call, [call-sealed], with its frame window and the callee's contract.

    The call block stores the callee at slot [a + 1] and a return address at slot [a], moves FP up by
    [a] slots, sets a2 to the argument count, and jumps to the entry word of the procedure.  [AtCall]
    says what holds there; for every return by the callee's contract ([AfterCall]), the code at the
    return address reaches the next instruction, related to the state with the result in slot [d].

    Like spike 8's allocator contract, [AfterCall] leaves the bytecode state after the call free:
    that it means the same as before, up to what the collector moved and what the callee did, is the
    callee's and the collector's job, not proved here. *)
From Stdlib Require Import NArith ZArith List Lia Bool Znumtheory.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim WxExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.Examples.emitter_p3_ns Require Import CfDefs CfStep CfRun CfSound CfStepSim CfCases.
Import ListNotations.
Open Scope bv_scope.

Lemma wrap_mod4 : forall z, (z mod 4 = 0)%Z -> (bv_unsigned (Z_to_bv 64 z) mod 4 = 0)%Z.
Proof.
  intros z H. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite <- (Zmod_div_mod 4 (2 ^ Z.of_N 64) z); [exact H | lia | lia |].
  exists (2 ^ 62)%Z. reflexivity.
Qed.

Section Call.
Context {fx : FPState}.
Variable c : cfg.
Variable cell_of : Z -> option Z.
Variable segs : list Segment.
Variable rom : word -> option byte.
Variable regs0 : bvmap 5 word.
Variables fp vm : word.
Variable vfalse : word.
Variable p : list binstr.
Variable cut : nat -> Z.
Variable inv : nat -> option CS.
Variable fuel : nat.
Hypothesis ACC : check_all c cell_of p cut inv fuel = true.

Abbreviation Rel := (Rel c segs regs0 fp vm).
Abbreviation E st := (CfSound.E fp vm st (Z_to_bv 64 0) (Z_to_bv 64 0)).
Abbreviation ER st2 v := (CfSound.E fp vm st2 v (Z_to_bv 64 0)).
Abbreviation AtNext := (AtNext c segs rom regs0 fp vm p cut inv).
Abbreviation steps := (steps segs).
Abbreviation RUN := (run_from c cell_of segs rom regs0 fp vm fuel).

(** The callee's contract on return to [ra]: FP is back at the callee's frame, the result in a0, the
    heap pointer in s3, and the caller's frame below the window holds the state [st2]. *)
Record AfterCall (s : CS) (a : Z) (st : bstate) (v : word) (regs : bvmap 5 word) (m : word -> option byte) : Prop := {
  ac_fp : getr regs 8 = v_addi fp (8 * a);
  ac_vm : getr regs 9 = vm;
  ac_v : getr regs 10 = v;
  ac_hp : getr regs 19 = bhp st;
  ac_keep : forall r : reg, scratch (bv_unsigned r) = false -> getr regs r = getr regs0 r;
  ac_lay : Lay c (E st) st;
  ac_M : forall n, (0 <= n < 64)%Z -> Z.testbit (sM s) n = true ->
    (n < cframe c)%Z /\ rdn segs m (v_addi fp (8 * n)) 8 = Some (le (bslots st n));
  ac_lim : rdn segs m (v_addi vm 8) 8 = Some (le (bhlimit st));
  ac_heap : forall a v, bheap st a = Some v -> rdn segs m a 8 = Some (le v);
  ac_cell : forall i ad t, ckinds c i = Some (KPtr ad t) ->
    rdn segs m (Z_to_bv 64 ad) 8 = Some (le (bconsts st i));
  ac_imm : forall i w, ckinds c i = Some (KImm w) -> bconsts st i = Z_to_bv 64 w;
  ac_tag : forall i ad t, ckinds c i = Some (KPtr ad t) -> tag3 (bconsts st i) = t;
  ac_code : CodeOK c segs m;
  ac_wf : forall n, wfv st (bslots st n);
  ac_wfc : forall i, wfv st (bconsts st i);
  ac_wfh : forall a v, bheap st a = Some v -> wfv st v;
  ac_wr : Wr c segs (E st) st m;
  ac_proc : forall i ad, ckinds c i = Some (KPtr ad 5) -> exists v, bheap st (v_addi (bconsts st i) 3) = Some v;
  ac_wfv : wfv st v
}.

(** At the callee's entry. *)
Definition AtCall (s : CS) (st : bstate) (i : nat) (d a n k : Z) (ms : machine_state) : Prop :=
  exists regs' m' entry ra,
    ms = mkst regs' (jalr_tgt entry 0) m' rom /\
    bheap st (v_addi (bconsts st k) 3) = Some entry /\
    getr regs' 8 = v_addi fp (8 * a) /\ getr regs' 9 = vm /\ getr regs' 19 = bhp st /\
    getr regs' 11 = bconsts st k /\ getr regs' 12 = Z_to_bv 64 n /\
    (n <> 0%Z -> getr regs' 18 = bslots st (a + 2)) /\
    rdn segs m' (v_addi fp (8 * a)) 8 = Some (le ra) /\
    rdn segs m' (v_addi fp (8 * (a + 1))) 8 = Some (le (bconsts st k)) /\
    (forall j, (0 <= j < n)%Z ->
       rdn segs m' (v_addi fp (8 * (a + 2 + j))) 8 = Some (le (bslots st (a + 2 + j)))) /\
    (bv_unsigned ra mod 4 = 0)%Z /\
    (forall r : reg, scratch (bv_unsigned r) = false -> getr regs' r = getr regs0 r) /\
    CodeOK c segs m' /\
    (forall st2 v regs2 m2, AfterCall (after_call s a) a st2 v regs2 m2 ->
       exists ms2, steps (mkst regs2 ra m2 rom) ms2 /\ AtNext (S i) (set_slot st2 d v) ms2).

Lemma inv_ret : forall s a st2 v regs2 m2,
  AfterCall s a st2 v regs2 m2 -> Inv c segs regs0 (ER st2 v) (y_ret s a) regs2 m2.
Proof.
  intros s a st2 v regs2 m2 A. destruct A. constructor; cbn [y_ret yA yF yH yV yroom].
  - intros r Hk.
    assert (Hr : forall k, bv_unsigned r = k -> r = Z_to_bv 5 k) by (intros k Hk'; apply u_eq; exact Hk').
    remember (bv_unsigned r) as rn eqn:Er.
    destruct (Z.eqb_spec rn 0) as [->|E1]; [rewrite (Hr 0%Z eq_refl); rewrite eval_const; reflexivity|].
    destruct (Z.eqb_spec rn 8) as [->|E2]; [rewrite (Hr 8%Z eq_refl); exact ac_fp0|].
    destruct (Z.eqb_spec rn 9) as [->|E3];
      [rewrite (Hr 9%Z eq_refl); cbn [eval base_val CfSound.E e_vm]; rewrite v_addi_0; exact ac_vm0|].
    destruct (Z.eqb_spec rn 10) as [->|E4];
      [rewrite (Hr 10%Z eq_refl); cbn [eval base_val CfSound.E e_status]; rewrite v_addi_0; exact ac_v0|].
    destruct (Z.eqb_spec rn 19) as [->|E5];
      [rewrite (Hr 19%Z eq_refl); cbn [eval base_val CfSound.E e_st]; rewrite v_addi_0; exact ac_hp0|].
    discriminate.
  - exact ac_keep0.
  - intros n Hk Hn. unfold frame0 in *.
    destruct (Z.leb 0 n && Z.ltb n 64 && Z.testbit (sM s) n)%bool eqn:Hb; [|discriminate].
    apply andb_true_iff in Hb as [Hb H3]. apply andb_true_iff in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    destruct (ac_M0 n (conj H1 H2) H3) as (_ & Hd).
    cbn [eval base_val CfSound.E e_st]. rewrite v_addi_0. exact Hd.
  - intros k Hk. discriminate.
  - intros k Hk. destruct (Z.eqb_spec k 8) as [Ek|Ek].
    + subst k. split; [lia|]. cbn [eval base_val CfSound.E e_st]. rewrite v_addi_0. exact ac_lim0.
    + exfalso. revert Hk. destruct (Z.eqb_spec k 8); [contradiction | discriminate].
  - exact ac_heap0.
  - exact ac_cell0.
  - exact ac_code0.
  - cbn [CfSound.E e_st]. pose proof (l_hp _ _ _ ac_lay0). lia.
  - reflexivity.
  - eapply wr_env. exact ac_wr0.
Qed.

Lemma wfv_same_heap : forall st st' x, bheap st' = bheap st -> wfv st x -> wfv st' x.
Proof. intros st st' x H. apply wfv_mono. intros a w. rewrite H. auto. Qed.

(** After the call: the code at the return address, from the callee's contract, to the next instruction. *)
Lemma call_return : forall s i a d o st2 v regs2 m2 y2,
  (i < length p)%nat ->
  AfterCall (after_call s a) a st2 v regs2 m2 ->
  run c cell_of 0 fuel o (cut (S i)) (y_ret (after_call s a) a) = Some (RDone y2) ->
  post_at c inv (after_call s a) y2 (Some d) (Lin KStatus 0) 0 (-1) (S i) = true ->
  exists ms2, steps (mkst regs2 (at_ c o) m2 rom) ms2 /\ AtNext (S i) (set_slot st2 d v) ms2.
Proof.
  intros s i a d o st2 v regs2 m2 y2 Hi A Hr Hp.
  pose proof A as [A8 A9 A10 A19 AK AL AM Alim Aheap Acell Aimm Atag Acode Awf Awfc Awfh Awr Aproc Awfv].
  destruct (run_sound c cell_of 0 segs rom regs0 (ER st2 v) ltac:(eapply lay_env; exact AL)
              ltac:(intros n _ Hb; rewrite Z.testbit_0_l in Hb; discriminate) Awf Aproc
              fuel o (cut (S i)) _ _ regs2 m2 Hr (inv_ret _ _ _ _ _ _ A)) as (ms & Hs & Hend).
  cbn [Ends] in Hend. destruct Hend as (regs3 & m3 & -> & I).
  exists (mkst regs3 (at_ c (cut (S i))) m3 rom). split; [exact Hs|].
  destruct (post_at_inv c inv _ _ _ _ _ _ _ Hp) as (t & Ht & Hpo).
  split; [eapply (at_next_bound c cell_of rom vfalse p cut inv fuel ACC); [exact Ht | lia]|].
  exists t, regs3, m3. split; [exact Ht|]. split; [reflexivity|].
  destruct (set_slot_fields st2 d v) as (F1 & F2 & F3 & F4).
  eapply post_sound with (st := st2) (y := y2) (d := Some d) (v := Lin KStatus 0) (delta := 0%Z) (plus := (-1)%Z)
    (status := v); try eassumption.
  - apply set_slot_other.
  - intros n Hn _. rewrite set_slot_same by exact Hn. cbn [eval base_val CfSound.E e_status]. symmetry. apply v_addi_0.
  - rewrite F2. symmetry. apply v_addi_0.
  - rewrite F2. lia.
  - eapply (lay_env c fp vm _ _ (Z_to_bv 64 0) (Z_to_bv 64 0)). eapply lay_keep; try eassumption.
  - intros a0 x Hx. rewrite F1 in Hx. exact (i_heap _ _ _ _ _ _ _ I a0 x Hx).
  - intros n _ Hb. cbn [after_call sP] in Hb. rewrite Z.testbit_0_l in Hb. discriminate.
  - intros. lia.
  - intros n. apply (wfv_same_heap st2); [exact F1|]. cbn [set_slot bslots]. destruct (Z.eqb n d); [exact Awfv | apply Awf].
  - destruct (i_wr _ _ _ _ _ _ _ I) as [W1 W2 W3]. constructor; cbn [CfSound.E e_fp e_vm e_st set_slot bhp bhlimit] in *; assumption.
Qed.

Lemma nats_in : forall n j, (0 <= j < n)%Z -> In j (nats n).
Proof.
  intros n j Hj. unfold nats. apply in_map_iff. exists (Z.to_nat j). split; [lia|]. apply in_seq. lia.
Qed.

Theorem sim_call : forall i s st regs m d a n k,
  nth_error p i = Some (ICallS d a n k) -> inv i = Some s -> Rel s st regs m ->
  exists ms, steps (mkst regs (at_ c (cut i)) m rom) ms /\ AtCall s st i d a n k ms.
Proof.
  intros i s st regs m d a n k Hn Hi R.
  pose proof (acc_at c cell_of rom vfalse p cut inv fuel ACC i _ Hn) as Hacc; unfold check_at in Hacc.
  rewrite Hi, Hn in Hacc.
  pose proof (proj1 (nth_error_Some p i) ltac:(rewrite Hn; discriminate)) as Hlt.
  apply andb_true_iff in Hacc as [Hacc Hrun]. apply andb_true_iff in Hacc as [Hacc Hargs].
  apply andb_true_iff in Hacc as [Hb Hkind].
  apply andb_true_iff in Hb as [Hb HR]. apply andb_true_iff in Hb as [Hb Hfr].
  apply andb_true_iff in Hb as [Ha2 Hn0].
  apply Z.leb_le in Ha2. apply Z.leb_le in Hn0. apply Z.leb_le in Hfr. apply Z.eqb_eq in HR.
  destruct (ckinds c k) as [[w|ad tg]|] eqn:Hk; try discriminate. apply Z.eqb_eq in Hkind. subst tg.
  destruct (run c cell_of (sP s) fuel (cut i) (-1) (y0 s)) as [r|] eqn:Hr; [|discriminate].
  destruct r as [| | | |ja y|]; try discriminate.
  destruct ja as [b0 k0| |]; try discriminate. destruct b0 as [|x1| | | | |x2|x3|x4| | |k']; try discriminate.
  destruct k0 as [|q|q]; try discriminate.
  apply andb_true_iff in Hrun as [Hrun Hret]. apply andb_true_iff in Hrun as [Hrun Hfk].
  apply andb_true_iff in Hrun as [Hrun H18]. apply andb_true_iff in Hrun as [Hrun H12].
  apply andb_true_iff in Hrun as [Hrun H11]. apply andb_true_iff in Hrun as [Hrun H19].
  apply andb_true_iff in Hrun as [Hrun H9]. apply andb_true_iff in Hrun as [Hrun H8].
  apply andb_true_iff in Hrun as [Hkk Ha1]. apply Z.eqb_eq in Hkk. subst k'.
  apply same_eq in Ha1. apply same_eq in H8. apply same_eq in H9. apply same_eq in H19.
  apply same_eq in H11. apply same_eq in H12.
  destruct (yF y a) as [bra raz| |] eqn:Hra; try discriminate. destruct bra; try discriminate.
  apply andb_true_iff in Hret as [Hret Hpost]. apply andb_true_iff in Hret as [Hmod Hic].
  apply Z.eqb_eq in Hmod.
  destruct (run c cell_of 0 fuel (raz - cbase c) (cut (S i)) (y_ret (after_call s a) a)) as [r2|] eqn:Hr2;
    [|discriminate].
  destruct r2 as [y2| | | | |]; try discriminate.
  destruct (RUN s st regs m _ _ _ R Hr) as (ms & Hs & Hend).
  cbn [Ends] in Hend. destruct Hend as (regs' & m' & -> & I).
  pose proof (r_lay _ _ _ _ _ _ _ _ _ R) as L.
  pose proof (l_F _ _ _ L) as HF.
  destruct (r_proc _ _ _ _ _ _ _ _ _ R k ad Hk) as (entry & Hent).
  assert (Fs : forall x b0 z, yF y x = Lin b0 z -> (0 <= x < cframe c)%Z ->
            rdn segs m' (v_addi fp (8 * x)) 8 = Some (le (eval (E st) (Lin b0 z)))).
  { intros x b0 z Hx Hrx. pose proof (i_F _ _ _ _ _ _ _ I x ltac:(rewrite Hx; reflexivity) Hrx) as Hd.
    unfold slot_at in Hd. cbn [CfSound.E e_fp] in Hd. rewrite Hx in Hd. exact Hd. }
  exists (mkst regs' (jalr_tgt entry 0) m' rom). split.
  { replace (jalr_tgt entry 0) with (jalr_tgt (eval (E st) (Lin (KEnt k) 0)) 0); [exact Hs|].
    cbn [eval base_val CfSound.E e_st]. rewrite v_addi_0, Hent. reflexivity. }
  exists regs', m', entry, (Z_to_bv 64 raz).
  split; [reflexivity|]. split; [exact Hent|].
  split; [rewrite (A_at c segs regs0 _ _ _ _ 8 8 _ I eq_refl H8 eq_refl); reflexivity|].
  split; [rewrite (A_at c segs regs0 _ _ _ _ 9 9 _ I eq_refl H9 eq_refl); cbn [eval base_val CfSound.E e_vm]; apply v_addi_0|].
  split; [rewrite (A_at c segs regs0 _ _ _ _ 19 19 _ I eq_refl H19 eq_refl); cbn [eval base_val CfSound.E e_st]; apply v_addi_0|].
  split; [rewrite (A_at c segs regs0 _ _ _ _ 11 11 _ I eq_refl H11 eq_refl); cbn [eval base_val CfSound.E e_st]; apply v_addi_0|].
  split; [rewrite (A_at c segs regs0 _ _ _ _ 12 12 _ I eq_refl H12 eq_refl); apply eval_mkc|].
  split.
  { intros Hn1. apply orb_true_iff in H18 as [H18|H18]; [apply Z.eqb_eq in H18; contradiction|].
    apply same_eq in H18. rewrite (A_at c segs regs0 _ _ _ _ 18 18 _ I eq_refl H18 eq_refl).
    cbn [eval base_val CfSound.E e_st]. apply v_addi_0. }
  split; [rewrite (Fs a KConst raz Hra ltac:(lia)); rewrite eval_const; reflexivity|].
  split; [rewrite (Fs (a + 1)%Z (KCell k) 0%Z Ha1 ltac:(lia)); cbn [eval base_val CfSound.E e_st]; rewrite v_addi_0; reflexivity|].
  split.
  { intros j Hj. rewrite forallb_forall in Hargs. pose proof (Hargs j (nats_in n j Hj)) as Hb.
    unfold frame_kept_call in Hfk. rewrite forallb_forall in Hfk.
    assert (Hin : In (a + 2 + j)%Z slots64)
      by (unfold slots64; apply in_map_iff; exists (Z.to_nat (a + 2 + j)); split; [lia | apply in_seq; lia]).
    pose proof (Hfk (a + 2 + j)%Z Hin) as Hq. rewrite Hb in Hq. cbn [negb orb] in Hq.
    destruct (Z.eqb_spec (a + 2 + j) a); [lia|]. destruct (Z.eqb_spec (a + 2 + j) (a + 1)); [lia|].
    cbn [orb] in Hq. apply same_eq in Hq.
    rewrite (Fs (a + 2 + j)%Z (KSlot (a + 2 + j)) 0%Z Hq ltac:(lia)).
    cbn [eval base_val CfSound.E e_st]. rewrite v_addi_0. reflexivity. }
  split; [apply wrap_mod4; exact Hmod|].
  split; [exact (i_keep _ _ _ _ _ _ _ I)|].
  split; [exact (i_code _ _ _ _ _ _ _ I)|].
  intros st2 v regs2 m2 A.
  replace (Z_to_bv 64 raz) with (at_ c (raz - cbase c)) by (unfold at_; f_equal; lia).
  exact (call_return s i a d _ st2 v regs2 m2 y2 Hlt A Hr2 Hpost).
Qed.

End Call.
