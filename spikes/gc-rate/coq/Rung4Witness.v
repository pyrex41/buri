(** * The premises of the scan theorems can all hold at once: a one-cell heap whose cell
    has a non-pointer head and a tail pointing to itself.  Without this, the theorems
    could be vacuous. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec StoreOk.
From LinuxProcessSemantics.Examples.gc_rate_ns Require Import gc_rate_code GcStep GcTac GcMem Rung1ObjWords Rung2Frame Rung2Paths Rung2Pointer Rung2ObjSize Rung2Spine Rung3Scan Rung4Graph.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope Z_scope.
Set Default Timeout 60.

Definition cW : word := Z_to_bv 64 0x300200.
Definition fromW : word := Z_to_bv 64 0x100000.
Definition fwW : word := Z_to_bv 64 2.
Definition toW : word := Z_to_bv 64 0x200000.
Definition tohiW : word := Z_to_bv 64 0x200020.
Definition spW : word := Z_to_bv 64 0x300100.
Definition s1W : word := Z_to_bv 64 0.
Definition fpW : word := at_off spW (-48).

Definition headW : word := Z_to_bv 64 4.          (* a fixnum *)
Definition tailW : word := Z_to_bv 64 0x100003.   (* a pair pointer to the cell itself *)
Definition movedW : word := pair_moved toW.

(* The mapped memory: the frame, the Copy struct, both semispaces. *)
Definition base : word -> option byte := fun a =>
  let u := bv_unsigned a in
  if ((0x100000 <=? u) && (u <? 0x100010)) || ((0x200000 <=? u) && (u <? 0x200020)) ||
     ((0x300000 <=? u) && (u <? 0x300300))
  then Some (Z_to_bv 8 0) else None.

Definition m0 : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes base
    cW (word_to_le_bytes 8 fromW))
    (at_off cW 8) (word_to_le_bytes 8 fwW))
    (at_off cW 16) (word_to_le_bytes 8 (at_off toW 16)))
    fromW (word_to_le_bytes 8 V_FORWARD))
    (at_off fromW 8) (word_to_le_bytes 8 movedW))
    toW (word_to_le_bytes 8 headW))
    (at_off toW 8) (word_to_le_bytes 8 tailW).

Definition cellW (p : word) : Prop := p = fromW.
Definition o0W (_ : word) : word := headW.
Definition o1W (_ : word) : word := tailW.
Definition phiW (x : word) : option word := if bv_eqb x fromW then Some toW else None.

Ltac cl := first [vm_compute; reflexivity | vm_compute; lia | vm_refl_bv].

Lemma wat_c : wat m0 cW fromW. Proof. unfold wat. vm_refl_bv. Qed.
Lemma wat_c8 : wat m0 (at_off cW 8) fwW. Proof. unfold wat. vm_refl_bv. Qed.
Lemma wat_c16 : wat m0 (at_off cW 16) (at_off toW 16). Proof. unfold wat. vm_refl_bv. Qed.
Lemma wat_f : wat m0 fromW V_FORWARD. Proof. unfold wat. vm_refl_bv. Qed.
Lemma wat_f8 : wat m0 (at_off fromW 8) movedW. Proof. unfold wat. vm_refl_bv. Qed.
Lemma wat_t : wat m0 toW headW. Proof. unfold wat. vm_refl_bv. Qed.
Lemma wat_t8 : wat m0 (at_off toW 8) tailW. Proof. unfold wat. vm_refl_bv. Qed.

Lemma Tcell : to_cell toW toW. Proof. split; vm_compute; [discriminate|reflexivity]. Qed.

Lemma tail_ptr : ptr_of tailW = fromW. Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(** The invariant holds at the start of the scan. *)
Lemma witness_inv : Inv cW toW tohiW cellW o0W o1W phiW m0 toW (at_off toW 16).
Proof.
  constructor.
  - exact wat_c16.
  - split; [split; vm_compute|vm_compute]; try discriminate; reflexivity.
  - split; vm_compute; discriminate.
  - intros p Hc Hn. unfold cellW in Hc. subst p. vm_compute in Hn. discriminate Hn.
  - intros p q Hp. unfold phiW in Hp.
    destruct (w_dec p fromW) as [->|Hne].
    + rewrite bv_eqb_true in Hp by reflexivity. injection Hp as <-.
      assert (L : (bv_unsigned (at_off toW 8) <? bv_unsigned toW) = false) by (vm_compute; reflexivity).
      assert (L0 : (bv_unsigned toW <? bv_unsigned toW) = false) by (vm_compute; reflexivity).
      split; [reflexivity|]. split; [exact wat_f|]. split; [exact wat_f8|]. split; [exact Tcell|].
      split; [vm_compute; discriminate|].
      split; [unfold show; rewrite L0; exact wat_t|].
      split; [unfold show; rewrite L; exact wat_t8|].
      split; intros H; vm_compute in H; discriminate H.
    + rewrite bv_eqb_false in Hp by exact Hne. discriminate Hp.
  - intros p p' q H1 H2. unfold phiW in H1, H2.
    destruct (w_dec p fromW) as [->|N1]; [|rewrite bv_eqb_false in H1 by exact N1; discriminate H1].
    destruct (w_dec p' fromW) as [->|N2]; [reflexivity|rewrite bv_eqb_false in H2 by exact N2; discriminate H2].
  - intros q [T1 T2] Lq.
    assert (U : bv_unsigned (at_off toW 16) = 0x200010) by (vm_compute; reflexivity).
    assert (U2 : bv_unsigned toW = 0x200000) by (vm_compute; reflexivity).
    rewrite U in Lq. rewrite U2 in T1, T2.
    pose proof (Z_div_mod_eq_full (bv_unsigned q - 0x200000) 16) as D. rewrite T2 in D.
    assert (E : q = toW).
    { apply bv_eq. rewrite U2. lia. }
    exists fromW. rewrite E. vm_compute. reflexivity.
Qed.

Definition ra1W : word := Z_to_bv 64 0x1198c.
Definition ra0W : word := Z_to_bv 64 0x119f0.
Definition two : word := Z_to_bv 64 2.
Definition seven : word := Z_to_bv 64 7.

Lemma tag_head : tag headW = 4. Proof. vm_compute. reflexivity. Qed.
Lemma tag_tail : tag tailW = 3. Proof. vm_compute. reflexivity. Qed.

Lemma cv_tail :
  cv_rel cW fromW fwW toW tohiW fpW ra1W two s1W cW seven m0 tailW
    (M fpW ra1W two s1W cW seven m0) movedW.
Proof.
  eapply cv_forwarded.
  - rewrite tag_tail. right. left. reflexivity.
  - rewrite tail_ptr. split; [split|]; vm_compute; first [discriminate|reflexivity].
  - rewrite tail_ptr. vm_compute. discriminate.
  - rewrite tail_ptr. exact wat_f.
  - rewrite tail_ptr. exact wat_f8.
Qed.

Definition m2 : word -> option byte :=
  wbytes (M fpW ra1W two s1W cW seven m0) (at_off toW 8) (word_to_le_bytes 8 movedW).

Lemma witness_body : pair_body cW fromW fwW toW tohiW spW s1W m0 toW two m2.
Proof.
  exists headW, tailW, m0. split; [exact wat_t|]. split; [rewrite tag_head; discriminate|].
  split.
  - apply slot_skip. rewrite tag_head. right. right. left. reflexivity.
  - split; [exact wat_t8|].
    assert (Hr : (0x1198c%bv : word) = ra1W) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hr. unfold m2.
    apply slot_call with (m0 := M fpW ra1W two s1W cW seven m0) (res := movedW).
    + rewrite tag_tail. right. left. reflexivity.
    + exact cv_tail.
Qed.

Lemma witness_scan : scan_pairs cW fromW fwW toW tohiW spW s1W m0 toW two m2 (at_off toW 16).
Proof.
  apply sp_last with (nx := at_off toW 16).
  - exact witness_body.
  - vm_compute. discriminate.
  - vm_compute. discriminate.
  - unfold wat. vm_refl_bv.
  - vm_compute. discriminate.
Qed.

(** The graph premises for this heap, and the theorem applied to it. *)
Lemma w_fl : TH <= bv_unsigned fromW. Proof. vm_compute. discriminate. Qed.
Lemma w_tl : TH <= bv_unsigned toW <= bv_unsigned tohiW. Proof. split; vm_compute; discriminate. Qed.
Lemma w_dis : bv_unsigned tohiW <= bv_unsigned fromW \/ bv_unsigned fromW + 8 * bv_unsigned fwW <= bv_unsigned toW.
Proof. right. vm_compute. discriminate. Qed.
Lemma w_fs : bv_unsigned fromW + 8 * bv_unsigned fwW <= bv_unsigned fpW. Proof. vm_compute. discriminate. Qed.
Lemma w_s8 : TH <= bv_unsigned fpW. Proof. vm_compute. discriminate. Qed.
Lemma w_ts : bv_unsigned tohiW <= bv_unsigned fpW. Proof. vm_compute. discriminate. Qed.
Lemma w_fc : bv_unsigned fpW + 48 <= bv_unsigned cW. Proof. vm_compute. discriminate. Qed.
Lemma w_ch : bv_unsigned cW + 56 <= 2^63. Proof. vm_compute. discriminate. Qed.

Lemma w_cell_from : forall p, cellW p ->
  bv_unsigned fromW <= bv_unsigned p /\ bv_unsigned p + 16 <= bv_unsigned fromW + 8 * bv_unsigned fwW.
Proof. intros p ->. split; vm_compute; discriminate. Qed.

Lemma w_cell_disj : forall p p', cellW p -> cellW p' -> p <> p' ->
  bv_unsigned p + 16 <= bv_unsigned p' \/ bv_unsigned p' + 16 <= bv_unsigned p.
Proof. intros p p' -> -> H. contradiction. Qed.

Lemma w_cell_vals : forall p, cellW p -> val_ok cellW (o0W p) /\ val_ok cellW (o1W p).
Proof.
  intros p _. split.
  - left. unfold o0W. rewrite tag_head. right. right. left. reflexivity.
  - right. unfold o1W. split; [exact tag_tail|unfold cellW; exact tail_ptr].
Qed.

Lemma w_cell_head : forall p, cellW p -> o0W p <> V_FORWARD.
Proof.
  intros p _ E. assert (H : bv_unsigned (o0W p) = bv_unsigned V_FORWARD) by (rewrite E; reflexivity).
  vm_compute in H. discriminate H.
Qed.

(** The conclusion on the concrete heap, which also confirms the theorem's arguments line up. *)
Definition witness_iso :=
  scan_iso cW fromW fwW toW tohiW spW s1W w_tl w_dis w_fs w_ts w_fc w_ch
    cellW o0W o1W w_cell_from w_cell_disj w_cell_vals w_cell_head
    phiW m0 toW two m2 (at_off toW 16) (at_off toW 16) witness_scan witness_inv Tcell
    ltac:(vm_compute; reflexivity).

(** The machine theorem's memory premise holds here too, and it applies. *)
Lemma base_writable : forall lo hi,
  (0x100000 <= lo /\ hi <= 0x100010) \/ (0x200000 <= lo /\ hi <= 0x200020) \/ (0x300000 <= lo /\ hi <= 0x300300) ->
  writable base lo hi.
Proof.
  intros lo hi Hr a Ha. unfold wview, base.
  assert (Hb : (((0x100000 <=? bv_unsigned a) && (bv_unsigned a <? 0x100010)) ||
     ((0x200000 <=? bv_unsigned a) && (bv_unsigned a <? 0x200020)) ||
     ((0x300000 <=? bv_unsigned a) && (bv_unsigned a <? 0x300300)))%bool = true).
  { destruct Hr as [H|[H|H]].
    - rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
    - rewrite (proj2 (Z.leb_le 0x200000 _)) by lia. rewrite (proj2 (Z.ltb_lt _ 0x200020)) by lia.
      rewrite orb_true_r. reflexivity.
    - rewrite (proj2 (Z.leb_le 0x300000 _)) by lia. rewrite (proj2 (Z.ltb_lt _ 0x300300)) by lia.
      rewrite orb_true_r. reflexivity. }
  cbv zeta. rewrite Hb. discriminate.
Qed.

Lemma base_clear : mem_clear base TL TH.
Proof.
  intros a Ha. unfold base. cbv zeta. unfold TL, TH in Ha.
  rewrite (proj2 (Z.leb_gt 0x100000 _)) by lia.
  rewrite (proj2 (Z.leb_gt 0x200000 _)) by lia.
  rewrite (proj2 (Z.leb_gt 0x300000 _)) by lia. reflexivity.
Qed.

Lemma m0_grows : mem_grows base m0.
Proof.
  intros x Hx. unfold m0.
  do 7 refine (wbytes_grows _ _ _ x _). exact Hx.
Qed.

Lemma m0_clear : mem_clear m0 TL TH.
Proof.
  unfold m0.
  repeat (apply clear_store; [|vm_compute; discriminate|vm_compute; discriminate]). exact base_clear.
Qed.

Lemma witness_dinv : dinv cW fromW fwW toW tohiW spW m0.
Proof.
  unfold dinv.
  split; [exact m0_clear|].
  split; [eapply writable_grows; [exact m0_grows|apply base_writable; right; right; split; vm_compute; discriminate]|].
  split; [eapply writable_grows; [exact m0_grows|apply base_writable; left; split; vm_compute; discriminate]|].
  split; [eapply writable_grows; [exact m0_grows|apply base_writable; right; left; split; vm_compute; discriminate]|].
  split; [eapply writable_grows; [exact m0_grows|apply base_writable; right; right; split; vm_compute; discriminate]|].
  split; [exact wat_c|exact wat_c8].
Qed.

Lemma w_st : stack_ok spW. Proof. split; vm_compute; discriminate. Qed.

(** The machine theorem, on this heap: from the loop's entry state the binary reaches the
    loop's exit with exactly the memory the relation describes. *)
Theorem witness_machine : forall {fx : FPState} rom (R : bvmap 5 word),
  sregs cW spW s1W R toW two ->
  exists R2,
    msteps source_segs (mkst R (0x1199c%bv : word) m0 rom) (mkst R2 (0x11922%bv : word) m2 rom) /\
    sregs cW spW s1W R2 (at_off toW 16) (Z_to_bv 64 16).
Proof.
  intros fx rom R Hs.
  assert (T : exists R2,
    msteps source_segs (mkst R (0x1199c%bv : word) m0 rom) (mkst R2 (0x11922%bv : word) m2 rom) /\
    sregs cW spW s1W R2 (at_off toW 16) (Z_to_bv 64 16) /\
    skept R R2 /\ dinv cW fromW fwW toW tohiW spW m2).
  { eapply (scan_contract rom cW fromW fwW toW tohiW spW s1W).
    all: first [exact w_fl | exact w_tl | exact w_dis | exact w_fs | exact w_s8 | exact w_ts
               | exact w_fc | exact w_ch | exact w_st | exact witness_scan | exact witness_dinv | exact Hs]. }
  destruct T as (R2 & Hm & Hs2 & _ & _).
  exists R2. split; [exact Hm|exact Hs2].
Qed.
