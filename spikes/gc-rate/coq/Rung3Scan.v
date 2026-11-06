(** * Rung 3: the to-space scan in [drain] (heap.c [scan]), restricted to objects that are
    pairs.  Each slot calls [copy_value] through its contract; the loop follows a relation
    written from the C code.  Objects with headers (vectors, closures, code objects, and
    the rest) go down arms this file doesn't cover. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec StoreOk.
From LinuxProcessSemantics.Examples.gc_rate_ns Require Import gc_rate_code GcStep GcTac GcMem Rung1ObjWords Rung2Frame Rung2Paths Rung2Pointer Rung2ObjSize Rung2Spine.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
Set Default Timeout 60.

Section Scan.
Context {fx : FPState}.

Variables (rom : word -> option byte) (c from fw q0 tohi sp s1v : word).
Let fp : word := at_off sp (-48).
Let fromhi : Z := (bv_unsigned from + 8 * bv_unsigned fw)%Z.
Hypothesis Hfl : (TH <= bv_unsigned from)%Z.
Hypothesis Htl : (TH <= bv_unsigned q0 <= bv_unsigned tohi)%Z.
Hypothesis Hdis : (bv_unsigned tohi <= bv_unsigned from \/ fromhi <= bv_unsigned q0)%Z.
Hypothesis Hfs : (fromhi <= bv_unsigned fp)%Z.
Hypothesis Hsp8 : (TH <= bv_unsigned fp)%Z.
Hypothesis Hts : (bv_unsigned tohi <= bv_unsigned fp)%Z.
Hypothesis Hfc : (bv_unsigned fp + 48 <= bv_unsigned c)%Z.
Hypothesis Hch : (bv_unsigned c + 56 <= 2^63)%Z.
Hypothesis Hst : stack_ok sp.

(** Memory facts the scan keeps. *)
Definition dinv (m : word -> option byte) : Prop :=
  mem_clear m TL TH /\
  writable m (bv_unsigned sp - 48) (bv_unsigned sp) /\
  writable m (bv_unsigned from) fromhi /\
  writable m (bv_unsigned q0) (bv_unsigned tohi) /\
  writable m (bv_unsigned c) (bv_unsigned c + 24) /\
  wat m c from /\ wat m (at_off c 8) fw.

(** One slot: a non-pointer is skipped; a pointer goes through [copy_value], whose result
    replaces it.  [ra] and [s0v] are what the call's frame saves. *)
Inductive slot (ra s0v : word) (m : word -> option byte) (a v : word) : (word -> option byte) -> Prop :=
| slot_skip : non_ptr_tag (tag v) -> slot ra s0v m a v m
| slot_call : forall m0 res,
    is_ptr_tag (tag v) ->
    cv_rel c from fw q0 tohi fp ra s0v s1v c (Z_to_bv 64 7) m v m0 res ->
    slot ra s0v m a v (wbytes m0 a (w8 res)).

(* Register values the loop keeps. *)
Definition sregs (R : bvmap 5 word) (s s0v : word) : Prop :=
  getr R 18 = c /\ getr R 19 = Z_to_bv 64 7 /\ getr R 20 = s /\ getr R 24 = Z_to_bv 64 1 /\
  getr R 8 = s0v /\ getr R 9 = s1v /\ getr R 2 = sp.

Definition skept (R R2 : bvmap 5 word) : Prop :=
  forall x : reg, kept x -> x <> 20 -> getr R2 x = getr R x.

Lemma fp_u : bv_unsigned fp = (bv_unsigned sp - 48)%Z.
Proof.
  destruct Hst as [H1 H2]. pose proof (bv_unsigned_in_range _ sp) as Hr.
  change (bv_modulus 64) with (2^64)%Z in Hr. unfold TH in H1.
  unfold fp. apply u_at_off. lia.
Qed.

Lemma call_pre : forall (R : bvmap 5 word) m s v s0v (ra : word),
  dinv m -> sregs R s s0v -> getr R 1 = ra -> getr R 10 = c -> getr R 11 = v ->
  (bv_unsigned ra mod 2 = 0)%Z ->
  cv_pre c from fw q0 tohi fp ra s0v s1v c (Z_to_bv 64 7) R m sp v.
Proof.
  intros R m s v s0v ra [Hc [W0 [W1 [W2 [W3 [H1 H2]]]]]] [A18 [A19 [A20 [A24 [A8 [A9 A2]]]]]] A1 A10 A11 Hev.
  unfold cv_pre.
  repeat (split; [first [exact Hc|exact A2|reflexivity|exact Hst|exact W0|exact A1|exact A8|exact A9|exact A18|exact A19
                        |exact Hev|exact A10|exact A11|exact W1|exact W2|exact W3|exact H1]|]).
  exact H2.
Qed.

Lemma do_call : forall (Rc : bvmap 5 word) m s v s0v (ra : word) m0 res,
  dinv m -> sregs Rc s s0v -> getr Rc 1 = ra -> getr Rc 10 = c -> getr Rc 11 = v ->
  (bv_unsigned ra mod 2 = 0)%Z ->
  cv_rel c from fw q0 tohi fp ra s0v s1v c (Z_to_bv 64 7) m v m0 res ->
  exists R',
    msteps source_segs (mkst Rc (0x11bc0 : word) m rom) (mkst R' ra m0 rom) /\
    getr R' 10 = res /\ sregs R' s s0v /\ skept Rc R' /\ dinv m0.
Proof.
  intros Rc m s v s0v ra m0 res Hd Hs A1 A10 A11 Hev Hr.
  pose proof (call_pre Rc m s v s0v ra Hd Hs A1 A10 A11 Hev) as Hpre.
  destruct (copy_value_contract rom c from fw q0 tohi fp ra s0v s1v c (Z_to_bv 64 7)
              Hfl Htl Hdis Hfs Hsp8 Hts Hfc Hch Rc m sp v m0 res Hpre Hr)
    as [(R' & Hm & B10 & B1 & B2 & B8 & B9 & B18 & B19 & Bk) [I Hg]].
  pose proof Hs as [A18 [A19 [A20 [A24 [A8 [A9 A2]]]]]].
  pose proof Hd as [_ [W0 _]].
  destruct I as [Ic [I1 [I2 [I3 [I4 [I5 _]]]]]].
  exists R'. split; [rewrite A1 in Hm; exact Hm|].
  split; [exact B10|]. split; [|split].
  - unfold sregs.
    assert (K20 : kept 20) by (unfold kept; repeat split; reg_neq_tac).
    assert (K24 : kept 24) by (unfold kept; repeat split; reg_neq_tac).
    rewrite B18, B19, B8, B9, B2, (Bk 20 K20), (Bk 24 K24).
    repeat (split; [assumption|]). exact A2.
  - intros x Hx _. apply Bk. exact Hx.
  - unfold dinv. repeat (split; [first [exact Ic|exact I1|exact I2|exact I3|exact I4|exact I5
      |eapply writable_grows; [exact Hg|exact W0]]|]). exact I5.
Qed.

Lemma dinv_slot : forall m (a res : word),
  dinv m -> (bv_unsigned q0 <= bv_unsigned a)%Z -> (bv_unsigned a + 8 <= bv_unsigned tohi)%Z ->
  dinv (wbytes m a (w8 res)) /\ store_ok source_segs m a 8%nat = true.
Proof.
  intros m a res [Hc [W0 [W1 [W2 [W3 [H1 H2]]]]]] Ha1 Ha2.
  pose proof fp_u as Hf.
  destruct Hst as [S1 S2].
  pose proof (bv_unsigned_in_range _ c) as Rc. pose proof (bv_unsigned_in_range _ a) as Ra.
  pose proof (bv_unsigned_in_range _ sp) as Rs.
  change (bv_modulus 64) with (2^64)%Z in Rc, Ra, Rs. unfold TH in *.
  split.
  - unfold dinv. split; [apply clear_store; [exact Hc|unfold TH; lia|lia]|].
    split; [apply writable_store; exact W0|].
    split; [apply writable_store; exact W1|].
    split; [apply writable_store; exact W2|].
    split; [apply writable_store; exact W3|].
    split.
    + apply wat_other; [exact H1|lia|lia|lia].
    + apply wat_other; [exact H2|rewrite u_at_off by lia; lia|lia|rewrite u_at_off by lia; lia].
  - eapply writable_store_ok; [exact W2|lia|cbn [Z.of_nat]; lia|lia].
Qed.

(** The call and store at 119e6. *)
Lemma site0 : forall R m s v s0v m0 res,
  dinv m -> sregs R s s0v -> getr R 11 = v ->
  (bv_unsigned q0 <= bv_unsigned s)%Z -> (bv_unsigned s + 8 <= bv_unsigned tohi)%Z ->
  cv_rel c from fw q0 tohi fp (0x119f0 : word) s0v s1v c (Z_to_bv 64 7) m v m0 res ->
  exists R2,
    msteps source_segs (mkst R (0x119e6 : word) m rom)
      (mkst R2 (0x119f4 : word) (wbytes m0 s (w8 res)) rom) /\
    sregs R2 s s0v /\ skept R R2 /\ dinv (wbytes m0 s (w8 res)).
Proof.
  intros R m s v s0v m0 res Hd Hs A11 Hq1 Hq2 Hr.
  pose proof Hs as [A18 [A19 [A20 [A24 [A8 [A9 A2]]]]]].
  pose proof Hd as [Hc _].
  destruct Hst as [S1 S2].
  pose proof (bv_unsigned_in_range _ s) as Rs. change (bv_modulus 64) with (2^64)%Z in Rs.
  pose proof fp_u as Hf.
  assert (Hpre : exists Rc,
     msteps source_segs (mkst R (0x119e6 : word) m rom) (mkst Rc (0x11bc0 : word) m rom) /\
     sregs Rc s s0v /\ getr Rc 1 = (0x119f0 : word) /\ getr Rc 10 = c /\ getr Rc 11 = v /\ skept R Rc).
  { eexists. split.
    - wsv Hc SF_119e6 SD_119e6 c ltac:(rewrite A18; apply v_add_zero_l).
      ws Hc SF_119e8 SD_119e8.
      eapply mst_step;
      [ reflexivity
      | eapply z_call with (tgt := (0x11bc0 : word)) (link := (0x119f0 : word));
        [ wxf_with Hc SF_119ec | reflexivity | exact SD_119ec | reflexivity
        | gres; imm_norm; bveq | bveq ]
      | apply mst_refl ].
    - split; [unfold sregs; gres; repeat split; assumption|].
      split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; exact A11|].
      unfold skept. intros x Hx Hn. pose proof Hx as Hy. unfold kept in Hy. decompose [and] Hy.
      rewrite !getr_other by assumption. reflexivity. }
  destruct Hpre as (Rc & Hm & Hs2 & B1 & B10 & B11 & Bk).
  destruct (do_call Rc m s v s0v (0x119f0 : word) m0 res Hd Hs2 B1 B10 B11 ltac:(vm_compute; reflexivity) Hr)
    as (R' & Hm2 & C10 & Hs3 & Ck & Hd0).
  pose proof Hs3 as [_ [_ [C20 _]]].
  pose proof Hd0 as [Hc0 _].
  destruct (dinv_slot m0 s res Hd0 ltac:(lia) ltac:(lia)) as [Hd1 Hok].
  exists R'. split; [|split; [exact Hs3|split; [|exact Hd1]]].
  - eapply msteps_trans; [exact Hm|]. eapply msteps_trans; [exact Hm2|].
    wsd Hc0 SF_119f0 SD_119f0 s res ltac:(rewrite C20; apply v_addi_zero) ltac:(exact Hok).
    apply mst_refl.
  - intros x Hx Hn. rewrite Ck, Bk by assumption. reflexivity.
Qed.

(** The call and store at 11982. *)
Lemma site1 : forall R m s v s0v m0 res,
  dinv m -> sregs R s s0v -> getr R 11 = v ->
  (bv_unsigned q0 <= bv_unsigned s)%Z -> (bv_unsigned s + 16 <= bv_unsigned tohi)%Z ->
  cv_rel c from fw q0 tohi fp (0x1198c : word) s0v s1v c (Z_to_bv 64 7) m v m0 res ->
  exists R2,
    msteps source_segs (mkst R (0x11982 : word) m rom)
      (mkst R2 (0x11990 : word) (wbytes m0 (at_off s 8) (w8 res)) rom) /\
    sregs R2 s s0v /\ skept R R2 /\ dinv (wbytes m0 (at_off s 8) (w8 res)).
Proof.
  intros R m s v s0v m0 res Hd Hs A11 Hq1 Hq2 Hr.
  pose proof Hs as [A18 [A19 [A20 [A24 [A8 [A9 A2]]]]]].
  pose proof Hd as [Hc _].
  destruct Hst as [S1 S2].
  pose proof (bv_unsigned_in_range _ s) as Rs. change (bv_modulus 64) with (2^64)%Z in Rs.
  pose proof fp_u as Hf.
  assert (Hpre : exists Rc,
     msteps source_segs (mkst R (0x11982 : word) m rom) (mkst Rc (0x11bc0 : word) m rom) /\
     sregs Rc s s0v /\ getr Rc 1 = (0x1198c : word) /\ getr Rc 10 = c /\ getr Rc 11 = v /\ skept R Rc).
  { eexists. split.
    - wsv Hc SF_11982 SD_11982 c ltac:(rewrite A18; apply v_add_zero_l).
      ws Hc SF_11984 SD_11984.
      eapply mst_step;
      [ reflexivity
      | eapply z_call with (tgt := (0x11bc0 : word)) (link := (0x1198c : word));
        [ wxf_with Hc SF_11988 | reflexivity | exact SD_11988 | reflexivity
        | gres; imm_norm; bveq | bveq ]
      | apply mst_refl ].
    - split; [unfold sregs; gres; repeat split; assumption|].
      split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; exact A11|].
      unfold skept. intros x Hx Hn. pose proof Hx as Hy. unfold kept in Hy. decompose [and] Hy.
      rewrite !getr_other by assumption. reflexivity. }
  destruct Hpre as (Rc & Hm & Hs2 & B1 & B10 & B11 & Bk).
  destruct (do_call Rc m s v s0v (0x1198c : word) m0 res Hd Hs2 B1 B10 B11 ltac:(vm_compute; reflexivity) Hr)
    as (R' & Hm2 & C10 & Hs3 & Ck & Hd0).
  pose proof Hs3 as [_ [_ [C20 _]]].
  pose proof Hd0 as [Hc0 _].
  destruct (dinv_slot m0 (at_off s 8) res Hd0 ltac:((rewrite u_at_off by lia; lia)) ltac:((rewrite u_at_off by lia; lia))) as [Hd1 Hok].
  exists R'. split; [|split; [exact Hs3|split; [|exact Hd1]]].
  - eapply msteps_trans; [exact Hm|]. eapply msteps_trans; [exact Hm2|].
    wsd Hc0 SF_1198c SD_1198c (at_off s 8) res ltac:(rewrite C20; reflexivity) ltac:(exact Hok).
    apply mst_refl.
  - intros x Hx Hn. rewrite Ck, Bk by assumption. reflexivity.
Qed.

Ltac sk :=
  unfold skept; intros ?x ?Hx ?Hn;
  match goal with H : kept ?x |- _ =>
    let Hy := fresh in pose proof H as Hy; unfold kept in Hy; decompose [and] Hy;
    rewrite !getr_other by assumption; reflexivity end.

(** The first slot of a pair. *)
Ltac slot_post Hs := split; [unfold sregs; gres; destruct Hs as [?A [?B [?C [?D [?E [?F ?G]]]]]]; repeat split; assumption|].

Lemma slot0 : forall R m s v s0v m',
  dinv m -> sregs R s s0v -> getr R 11 = v -> getr R 10 = Z_to_bv 64 (tag v) -> tag v <> 7%Z ->
  (bv_unsigned q0 <= bv_unsigned s)%Z -> (bv_unsigned s + 8 <= bv_unsigned tohi)%Z ->
  slot (0x119f0 : word) s0v m s v m' ->
  exists R2,
    msteps source_segs (mkst R (0x119d8 : word) m rom) (mkst R2 (0x119f4 : word) m' rom) /\
    sregs R2 s s0v /\ skept R R2 /\ dinv m'.
Proof.
  intros R m s v s0v m' Hd Hs A11 A10 Ht7 Hq1 Hq2 Hr.
  pose proof Hs as [A18 [A19 [A20 [A24 [A8 [A9 A2]]]]]].
  pose proof Hd as [Hc _].
  pose proof (andi5 v) as H5.
  destruct Hr as [Hn|m0 res Hp Hcv].
  - assert (Hk : tag v = 0%Z \/ tag v = 2%Z \/ tag v = 4%Z).
    { destruct Hn as [E|[E|[E|E]]]; lia. }
    destruct Hk as [E|[E|E]]; rewrite E in A10; eexists; split.
    all: try (wsv Hc SF_119d8 SD_119d8 (Z_to_bv 64 (Z.land (tag v) 5)) ltac:(rewrite A11, H5; reflexivity);
      wbr_ft Hc SF_119dc SD_119dc ltac:(rewrite A24, E; vm_compute; reflexivity);
      ws Hc SF_119e0 SD_119e0;
      wbr_tk Hc SF_119e2 SD_119e2 ltac:(rewrite A24, A10; vm_compute; reflexivity);
      apply mst_refl).
    all: slot_post Hs; split; [sk|exact Hd].
  - assert (Hpre : exists R0,
       msteps source_segs (mkst R (0x119d8 : word) m rom) (mkst R0 (0x119e6 : word) m rom) /\
       sregs R0 s s0v /\ getr R0 11 = v /\ skept R R0).
    { destruct Hp as [E|[E|[E|E]]]; rewrite E in A10; eexists; split.
      - wsv Hc SF_119d8 SD_119d8 (Z_to_bv 64 (Z.land (tag v) 5)) ltac:(rewrite A11, H5; reflexivity).
        wbr_tk Hc SF_119dc SD_119dc ltac:(rewrite A24, E; vm_compute; reflexivity). apply mst_refl.
      - slot_post Hs. split; [gres; exact A11|sk].
      - wsv Hc SF_119d8 SD_119d8 (Z_to_bv 64 (Z.land (tag v) 5)) ltac:(rewrite A11, H5; reflexivity).
        wbr_tk Hc SF_119dc SD_119dc ltac:(rewrite A24, E; vm_compute; reflexivity). apply mst_refl.
      - slot_post Hs. split; [gres; exact A11|sk].
      - wsv Hc SF_119d8 SD_119d8 (Z_to_bv 64 (Z.land (tag v) 5)) ltac:(rewrite A11, H5; reflexivity).
        wbr_ft Hc SF_119dc SD_119dc ltac:(rewrite A24, E; vm_compute; reflexivity).
        ws Hc SF_119e0 SD_119e0.
        wbr_ft Hc SF_119e2 SD_119e2 ltac:(rewrite A24, A10; vm_compute; reflexivity). apply mst_refl.
      - slot_post Hs. split; [gres; exact A11|sk].
      - wsv Hc SF_119d8 SD_119d8 (Z_to_bv 64 (Z.land (tag v) 5)) ltac:(rewrite A11, H5; reflexivity).
        wbr_ft Hc SF_119dc SD_119dc ltac:(rewrite A24, E; vm_compute; reflexivity).
        ws Hc SF_119e0 SD_119e0.
        wbr_ft Hc SF_119e2 SD_119e2 ltac:(rewrite A24, A10; vm_compute; reflexivity). apply mst_refl.
      - slot_post Hs. split; [gres; exact A11|sk]. }
    destruct Hpre as (R0 & Hm & Hs0 & B11 & Bk).
    destruct (site0 R0 m s v s0v m0 res Hd Hs0 B11 Hq1 Hq2 Hcv) as (R2 & Hm2 & Hs2 & Ck & Hd2).
    exists R2. split; [eapply msteps_trans; [exact Hm|exact Hm2]|].
    split; [exact Hs2|]. split; [|exact Hd2].
    intros x Hx Hn. rewrite Ck, Bk by assumption. reflexivity.
Qed.

(** The second slot of a pair. *)
Lemma slot1 : forall R m s v s0v m',
  dinv m -> sregs R s s0v -> wat m (at_off s 8) v ->
  (bv_unsigned q0 <= bv_unsigned s)%Z -> (bv_unsigned s + 16 <= bv_unsigned tohi)%Z ->
  slot (0x1198c : word) (Z_to_bv 64 2) m (at_off s 8) v m' ->
  exists R2,
    msteps source_segs (mkst R (0x119f4 : word) m rom) (mkst R2 (0x11990 : word) m' rom) /\
    sregs R2 s (Z_to_bv 64 2) /\ skept R R2 /\ dinv m'.
Proof.
  intros R m s v s0v m' Hd Hs Hw Hq1 Hq2 Hr.
  pose proof Hs as [A18 [A19 [A20 [A24 [A8 [A9 A2]]]]]].
  pose proof Hd as [Hc _].
  pose proof (andi5 v) as H5. pose proof (andi7 v) as H7.
  destruct Hr as [Hn|m0 res Hp Hcv].
  - destruct Hn as [E|[E|[E|E]]]; eexists; split.
    all: try (wld Hc SF_119f4 SD_119f4 (at_off s 8) v ltac:(rewrite A20; reflexivity) Hw;
      wsv Hc SF_119f8 SD_119f8 (Z_to_bv 64 (Z.land (tag v) 5)) ltac:(exact H5);
      wsv Hc SF_119fc SD_119fc (Z_to_bv 64 2) ltac:(bveq);
      wbr_ft Hc SF_119fe SD_119fe ltac:(rewrite A24, E; vm_compute; reflexivity);
      wsv Hc SF_11a02 SD_11a02 (Z_to_bv 64 (tag v)) ltac:(exact H7);
      ws Hc SF_11a06 SD_11a06;
      wbr_tk Hc SF_11a08 SD_11a08 ltac:(rewrite A24, E; vm_compute; reflexivity);
      apply mst_refl).
    all: split; [unfold sregs; gres; repeat split; assumption|]; split; [sk|exact Hd].
  - assert (Hpre : exists R0,
       msteps source_segs (mkst R (0x119f4 : word) m rom) (mkst R0 (0x11982 : word) m rom) /\
       sregs R0 s (Z_to_bv 64 2) /\ getr R0 11 = v /\ skept R R0).
    { destruct Hp as [E|[E|[E|E]]]; eexists; split.
      - wld Hc SF_119f4 SD_119f4 (at_off s 8) v ltac:(rewrite A20; reflexivity) Hw.
        wsv Hc SF_119f8 SD_119f8 (Z_to_bv 64 (Z.land (tag v) 5)) ltac:(exact H5).
        wsv Hc SF_119fc SD_119fc (Z_to_bv 64 2) ltac:(bveq).
        wbr_tk Hc SF_119fe SD_119fe ltac:(rewrite A24, E; vm_compute; reflexivity). apply mst_refl.
      - split; [unfold sregs; gres; repeat split; assumption|]. split; [gres; reflexivity|sk].
      - wld Hc SF_119f4 SD_119f4 (at_off s 8) v ltac:(rewrite A20; reflexivity) Hw.
        wsv Hc SF_119f8 SD_119f8 (Z_to_bv 64 (Z.land (tag v) 5)) ltac:(exact H5).
        wsv Hc SF_119fc SD_119fc (Z_to_bv 64 2) ltac:(bveq).
        wbr_tk Hc SF_119fe SD_119fe ltac:(rewrite A24, E; vm_compute; reflexivity). apply mst_refl.
      - split; [unfold sregs; gres; repeat split; assumption|]. split; [gres; reflexivity|sk].
      - wld Hc SF_119f4 SD_119f4 (at_off s 8) v ltac:(rewrite A20; reflexivity) Hw.
        wsv Hc SF_119f8 SD_119f8 (Z_to_bv 64 (Z.land (tag v) 5)) ltac:(exact H5).
        wsv Hc SF_119fc SD_119fc (Z_to_bv 64 2) ltac:(bveq).
        wbr_ft Hc SF_119fe SD_119fe ltac:(rewrite A24, E; vm_compute; reflexivity).
        wsv Hc SF_11a02 SD_11a02 (Z_to_bv 64 (tag v)) ltac:(exact H7).
        ws Hc SF_11a06 SD_11a06.
        wbr_ft Hc SF_11a08 SD_11a08 ltac:(rewrite A24, E; vm_compute; reflexivity).
        wj Hc SF_11a0c SD_11a0c (0x11982 : word). apply mst_refl.
      - split; [unfold sregs; gres; repeat split; assumption|]. split; [gres; reflexivity|sk].
      - wld Hc SF_119f4 SD_119f4 (at_off s 8) v ltac:(rewrite A20; reflexivity) Hw.
        wsv Hc SF_119f8 SD_119f8 (Z_to_bv 64 (Z.land (tag v) 5)) ltac:(exact H5).
        wsv Hc SF_119fc SD_119fc (Z_to_bv 64 2) ltac:(bveq).
        wbr_ft Hc SF_119fe SD_119fe ltac:(rewrite A24, E; vm_compute; reflexivity).
        wsv Hc SF_11a02 SD_11a02 (Z_to_bv 64 (tag v)) ltac:(exact H7).
        ws Hc SF_11a06 SD_11a06.
        wbr_ft Hc SF_11a08 SD_11a08 ltac:(rewrite A24, E; vm_compute; reflexivity).
        wj Hc SF_11a0c SD_11a0c (0x11982 : word). apply mst_refl.
      - split; [unfold sregs; gres; repeat split; assumption|]. split; [gres; reflexivity|sk]. }
    destruct Hpre as (R0 & Hm & Hs0 & B11 & Bk).
    destruct (site1 R0 m s v (Z_to_bv 64 2) m0 res Hd Hs0 B11 Hq1 Hq2 Hcv) as (R2 & Hm2 & Hs2 & Ck & Hd2).
    exists R2. split; [eapply msteps_trans; [exact Hm|exact Hm2]|].
    split; [exact Hs2|]. split; [|exact Hd2].
    intros x Hx Hn. rewrite Ck, Bk by assumption. reflexivity.
Qed.

(** One pair, per the C code: scan_values's two slots. *)
Definition pair_body (m : word -> option byte) (s s0v : word) (m2 : word -> option byte) : Prop :=
  exists a0 a1 m1,
    wat m s a0 /\ tag a0 <> 7%Z /\ slot (0x119f0 : word) s0v m s a0 m1 /\
    wat m1 (at_off s 8) a1 /\ slot (0x1198c : word) (Z_to_bv 64 2) m1 (at_off s 8) a1 m2.

Lemma pair_iter : forall R m s s0v m2,
  dinv m -> sregs R s s0v -> pair_body m s s0v m2 ->
  (bv_unsigned q0 <= bv_unsigned s)%Z -> (bv_unsigned s + 16 <= bv_unsigned tohi)%Z ->
  exists R2,
    msteps source_segs (mkst R (0x1199c : word) m rom) (mkst R2 (0x11990 : word) m2 rom) /\
    sregs R2 s (Z_to_bv 64 2) /\ skept R R2 /\ dinv m2.
Proof.
  intros R m s s0v m2 Hd Hs (a0 & a1 & m1 & W0 & Ht7 & Sl0 & W1 & Sl1) Hq1 Hq2.
  pose proof Hs as [A18 [A19 [A20 [A24 [A8 [A9 A2]]]]]].
  pose proof Hd as [Hc _].
  pose proof (andi7 a0) as H7. pose proof (tag_range a0) as Htr.
  assert (Hpre : exists R0,
     msteps source_segs (mkst R (0x1199c : word) m rom) (mkst R0 (0x119d8 : word) m rom) /\
     sregs R0 s s0v /\ getr R0 11 = a0 /\ getr R0 10 = Z_to_bv 64 (tag a0) /\ skept R R0).
  { eexists. split.
    - wld Hc SF_1199c SD_1199c s a0 ltac:(rewrite A20; apply v_addi_zero) W0.
      wsv Hc SF_119a0 SD_119a0 (Z_to_bv 64 (tag a0)) ltac:(exact H7).
      wbr_tk Hc SF_119a4 SD_119a4 ltac:(rewrite A19; apply ne_true; rewrite !u_Z2bv by lia; exact Ht7).
      apply mst_refl.
    - split; [unfold sregs; gres; repeat split; assumption|].
      split; [gres; reflexivity|]. split; [gres; reflexivity|sk]. }
  destruct Hpre as (R0 & Hm & Hs0 & B11 & B10 & Bk).
  destruct (slot0 R0 m s a0 s0v m1 Hd Hs0 B11 B10 Ht7 Hq1 ltac:(lia) Sl0) as (R1 & Hm1 & Hs1 & Ck & Hd1).
  destruct (slot1 R1 m1 s a1 s0v m2 Hd1 Hs1 W1 Hq1 Hq2 Sl1) as (R2 & Hm2 & Hs2 & Dk & Hd2).
  exists R2. split.
  - eapply msteps_trans; [exact Hm|]. eapply msteps_trans; [exact Hm1|exact Hm2].
  - split; [exact Hs2|]. split; [|exact Hd2].
    intros x Hx Hn. rewrite Dk, Ck, Bk by assumption. reflexivity.
Qed.

(** The scan loop over a run of pairs. [s0v] is what register s0 holds on entry. *)
Inductive scan_pairs : (word -> option byte) -> word -> word -> (word -> option byte) -> word -> Prop :=
| sp_last : forall m s s0v m2 nx,
    pair_body m s s0v m2 ->
    (bv_unsigned q0 <= bv_unsigned s)%Z -> (bv_unsigned s + 16 <= bv_unsigned tohi)%Z ->
    wat m2 (at_off c 16) nx -> (bv_unsigned nx <= bv_unsigned s + 16)%Z ->
    scan_pairs m s s0v m2 (at_off s 16)
| sp_more : forall m s s0v m2 nx m' s',
    pair_body m s s0v m2 ->
    (bv_unsigned q0 <= bv_unsigned s)%Z -> (bv_unsigned s + 16 <= bv_unsigned tohi)%Z ->
    wat m2 (at_off c 16) nx -> (bv_unsigned s + 16 < bv_unsigned nx)%Z ->
    scan_pairs m2 (at_off s 16) (Z_to_bv 64 16) m' s' ->
    scan_pairs m s s0v m' s'.

(** THEOREM: the loop runs as the relation says, and exits at its next test. *)
Theorem scan_contract : forall m s s0v m' s',
  scan_pairs m s s0v m' s' ->
  forall R, dinv m -> sregs R s s0v ->
  exists R2,
    msteps source_segs (mkst R (0x1199c : word) m rom) (mkst R2 (0x11922 : word) m' rom) /\
    sregs R2 s' (Z_to_bv 64 16) /\ skept R R2 /\ dinv m'.
Proof.
  assert (Head : forall R2 m2 s nx,
     dinv m2 -> sregs R2 s (Z_to_bv 64 2) -> wat m2 (at_off c 16) nx ->
     (bv_unsigned s + 16 <= bv_unsigned tohi)%Z ->
     exists R3,
       msteps source_segs (mkst R2 (0x11990 : word) m2 rom)
         (mkst R3 (if (bv_unsigned nx <=? bv_unsigned s + 16)%Z then (0x11922 : word) else (0x1199c : word)) m2 rom) /\
       sregs R3 (at_off s 16) (Z_to_bv 64 16) /\ skept R2 R3).
  { intros R2 m2 s nx Hd Hs Hw Hb.
    pose proof Hs as [A18 [A19 [A20 [A24 [A8 [A9 A2]]]]]]. pose proof Hd as [Hc _].
    pose proof (bv_unsigned_in_range _ s) as Rs. change (bv_modulus 64) with (2^64)%Z in Rs.
    pose proof fp_u as Hf. pose proof (bv_unsigned_in_range _ sp) as Rp.
    change (bv_modulus 64) with (2^64)%Z in Rp.
    assert (Add : v_add s (Z_to_bv 64 16) = at_off s 16).
    { unfold v_add, at_off. rewrite (u_Z2bv 16) by lia. reflexivity. }
    assert (Us : bv_unsigned (at_off s 16) = (bv_unsigned s + 16)%Z) by (apply u_at_off; lia).
    destruct (Z.leb_spec (bv_unsigned nx) (bv_unsigned s + 16)) as [Hl|Hg]; eexists; split.
    - wld Hc SF_11990 SD_11990 (at_off c 16) nx ltac:(rewrite A18; reflexivity) Hw.
      wsv Hc SF_11994 SD_11994 (Z_to_bv 64 16) ltac:(rewrite A8; bveq).
      wsv Hc SF_11996 SD_11996 (at_off s 16) ltac:(rewrite A20; exact Add).
      wbr_tk Hc SF_11998 SD_11998 ltac:(apply geu_true; rewrite Us; exact Hl).
      apply mst_refl.
    - split; [unfold sregs; gres; repeat split; assumption|sk].
    - wld Hc SF_11990 SD_11990 (at_off c 16) nx ltac:(rewrite A18; reflexivity) Hw.
      wsv Hc SF_11994 SD_11994 (Z_to_bv 64 16) ltac:(rewrite A8; bveq).
      wsv Hc SF_11996 SD_11996 (at_off s 16) ltac:(rewrite A20; exact Add).
      wbr_ft Hc SF_11998 SD_11998 ltac:(apply geu_false; rewrite Us; exact Hg).
      apply mst_refl.
    - split; [unfold sregs; gres; repeat split; assumption|sk]. }
  induction 1; intros R Hd Hs.
  - destruct (pair_iter R m s s0v m2 Hd Hs H H0 H1) as (R2 & Hm & Hs2 & Bk & Hd2).
    destruct (Head R2 m2 s nx Hd2 Hs2 H2 H1) as (R3 & Hm2 & Hs3 & Ck).
    rewrite (proj2 (Z.leb_le _ _) H3) in Hm2.
    exists R3. split; [eapply msteps_trans; [exact Hm|exact Hm2]|].
    split; [exact Hs3|]. split; [|exact Hd2].
    intros x Hx Hn. rewrite Ck, Bk by assumption. reflexivity.
  - destruct (pair_iter R m s s0v m2 Hd Hs H H0 H1) as (R2 & Hm & Hs2 & Bk & Hd2).
    destruct (Head R2 m2 s nx Hd2 Hs2 H2 H1) as (R3 & Hm2 & Hs3 & Ck).
    rewrite (proj2 (Z.leb_gt _ _) H3) in Hm2.
    destruct (IHscan_pairs R3 Hd2 Hs3) as (R4 & Hm3 & Hs4 & Dk & Hd4).
    exists R4. split.
    + eapply msteps_trans; [exact Hm|]. eapply msteps_trans; [exact Hm2|exact Hm3].
    + split; [exact Hs4|]. split; [|exact Hd4].
      intros x Hx Hn. 
      assert (K : getr R3 x = getr R2 x) by (apply Ck; assumption).
      rewrite Dk, K, Bk by assumption. reflexivity.
Qed.

End Scan.
