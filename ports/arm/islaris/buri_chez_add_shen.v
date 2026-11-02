(* E2E-21: the Islaris fast-path theorem of buri_chez_add.v restated about
   Shen integers.

   Separate toolchain: Coq 8.19.0 + Iris/Lithium/Islaris (nix/arm/islaris.nix),
   checked by ports/arm/islaris/check-islaris-shen.sh. NOT a scripts/prove
   module. The same rocq/ChezLayout.v and rocq/ChezWord.v sources that
   scripts/prove compiles with Coq 8.18 are compiled here (logical path Buri),
   so `fx_enc`/`fx_range` are literally the definitions that rocq/ChezRepr.v
   uses in `rv` (RFix) and in `shen_int_add_fast_path`. The two kernels are not
   connected by a proof; the link is that both check the same source text.

   Statement (buri_chez_add_shen): if X0 and X1 hold the Chez fixnum words of
   Shen integers x and y with x, y and x + y in the fixnum range, X23 = 2
   (argument count, %ac0) and X20 (%sfp) points at the return-address frame
   slot, then the code reaches the return address with X23 holding the fixnum
   word of x + y. The premises `(a|b)&7 = 0` and `no signed overflow` of
   buri_chez_add_fast_path are discharged from the Shen-level premises:
   `fxw_tag_test` and `fxw_no_overflow_iff` (the overflow premise holds iff
   x + y is a fixnum). What remains assumed is everything buri_chez_add.v
   assumes: Islaris's EL2/MMU-off register constraints (sys_regs), the
   isla/Armv8.5-IR traces, the captured base address, and the continuation
   instr_pre at ra. The frame-slot premises on X20 are representation facts
   of Chez stack frames (E2E-21 frames / E2E-22 calling convention); they are
   kept as premises, not discharged. *)
Require Import isla.aarch64.aarch64.
From isla.instructions.buri_chez_add Require Import instrs.
From isla.examples Require Import buri_chez_add.
From Buri Require ChezLayout ChezWord.

Definition fxw (z : Z) : bv 64 := Z_to_bv 64 (ChezWord.ChezWord.fx_enc z).

Lemma chez_regs_match :
  ChezLayout.ChezLayout.reg_ac0 = 23 ∧ ChezLayout.ChezLayout.reg_sfp = 20 ∧
  ChezLayout.ChezLayout.reg_arg1 = 0 ∧ ChezLayout.ChezLayout.reg_arg2 = 1 ∧
  ChezLayout.ChezLayout.reg_lr = 30 ∧ ChezLayout.ChezLayout.reg_jmptmp = 10 ∧
  ChezLayout.ChezLayout.mask_fixnum = 7.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma fxw_unsigned z : bv_unsigned (fxw z) = ChezWord.ChezWord.fx_enc z.
Proof.
  unfold fxw. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  pose proof (ChezWord.ChezWord.fx_enc_word z) as W.
  destruct ChezWord.ChezWord.chez_word_layout as (HM & _).
  unfold ChezWord.ChezWord.word_ok in W. rewrite HM in W.
  change (bv_modulus 64) with 18446744073709551616. lia.
Qed.

Lemma swrap_match z : bv_swrap 64 z = ChezWord.ChezWord.swrap z.
Proof.
  destruct ChezWord.ChezWord.chez_word_layout as (HM & HH & _).
  cbv [bv_swrap bv_wrap ChezWord.ChezWord.swrap]. rewrite HM HH.
  change (bv_modulus 64) with 18446744073709551616.
  change (bv_half_modulus 64) with 9223372036854775808. reflexivity.
Qed.

Lemma fxw_tag_test x y : bv_and (bv_or (fxw x) (fxw y)) (BV 64 7) = BV 64 0.
Proof.
  apply bv_eq. rewrite bv_and_unsigned bv_or_unsigned !fxw_unsigned.
  pose proof (ChezWord.ChezWord.fx_or_tag x y) as T.
  destruct chez_regs_match as (_ & _ & _ & _ & _ & _ & HK). rewrite HK in T. exact T.
Qed.

Lemma fxw_no_overflow_iff x y :
  ChezWord.ChezWord.fx_range x → ChezWord.ChezWord.fx_range y →
  (- 2 ^ 63 ≤ bv_signed (fxw x) + bv_signed (fxw y) < 2 ^ 63 ↔ ChezWord.ChezWord.fx_range (x + y)).
Proof.
  intros Hx Hy. unfold fxw. rewrite !Z_to_bv_signed !swrap_match.
  pose proof (ChezWord.ChezWord.fx_add_no_overflow_iff x y Hx Hy) as E.
  destruct ChezWord.ChezWord.chez_word_layout as (_ & HH & _). rewrite HH in E.
  change (2 ^ 63) with 9223372036854775808. exact E.
Qed.

Lemma fxw_add x y : bv_add (fxw x) (fxw y) = fxw (x + y).
Proof.
  apply bv_eq. rewrite bv_add_unsigned !fxw_unsigned.
  rewrite -ChezWord.ChezWord.fx_add_wrap.
  destruct ChezWord.ChezWord.chez_word_layout as (HM & _).
  unfold bv_wrap, ChezWord.ChezWord.wrap. rewrite HM.
  change (bv_modulus 64) with 18446744073709551616. reflexivity.
Qed.

Definition buri_add_shen_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∃ (x y : Z) (fp ra r10 r30 : bv 64),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  "R23" ↦ᵣ RVal_Bits (BV 64 2) ∗
  "R0" ↦ᵣ RVal_Bits (fxw x) ∗ "R1" ↦ᵣ RVal_Bits (fxw y) ∗
  "R30" ↦ᵣ RVal_Bits r30 ∗ "R10" ↦ᵣ RVal_Bits r10 ∗
  "R20" ↦ᵣ RVal_Bits fp ∗
  "InGuardedPage" ↦ᵣ RVal_Bool false ∗
  bv_unsigned fp ↦ₘ ra ∗
  ⌜bv_unsigned fp < 2 ^ 52⌝ ∗ ⌜bv_unsigned fp `mod` 8 = 0⌝ ∗
  ⌜ChezWord.ChezWord.fx_range x⌝ ∗ ⌜ChezWord.ChezWord.fx_range y⌝ ∗
  ⌜ChezWord.ChezWord.fx_range (x + y)⌝ ∗
  instr_pre (bv_unsigned ra) (
    reg_col sys_regs ∗
    reg_col CNVZ_regs ∗
    "R23" ↦ᵣ RVal_Bits (fxw (x + y)) ∗
    "R0" ↦ᵣ RVal_Bits (fxw x) ∗ "R1" ↦ᵣ RVal_Bits (fxw y) ∗
    "R30" ↦ᵣ RVal_Bits (bv_or (fxw x) (fxw y)) ∗ "R10" ↦ᵣ RVal_Bits ra ∗
    "R20" ↦ᵣ RVal_Bits fp ∗
    "InGuardedPage" ↦ᵣ RVal_Bool false ∗
    bv_unsigned fp ↦ₘ ra ∗
    True).

Lemma buri_chez_add_shen `{!islaG Σ} `{!threadG} :
  instr 0x00007f8d409bcb50 (Some a0) -∗
  instr 0x00007f8d409bcb54 (Some a4) -∗
  instr 0x00007f8d409bcb58 (Some a8) -∗
  instr 0x00007f8d409bcb5c (Some ac) -∗
  instr 0x00007f8d409bcb60 (Some a10) -∗
  instr 0x00007f8d409bcb64 (Some a14) -∗
  instr 0x00007f8d409bcb68 (Some a18) -∗
  instr 0x00007f8d409bcb6c (Some a1c) -∗
  instr 0x00007f8d409bcb70 (Some a20) -∗
  instr 0x00007f8d409bcb74 None -∗
  instr 0x00007f8d409bcbd4 None -∗
  instr_body 0x00007f8d409bcb50 buri_add_shen_spec.
Proof.
  iIntros "I0 I4 I8 Ic I10 I14 I18 I1c I20 I24 I84".
  iPoseProof (buri_chez_add_fast_path with "I0 I4 I8 Ic I10 I14 I18 I1c I20 I24 I84") as "B".
  iApply (instr_pre_wand with "B"); [done|done|].
  iIntros "S".
  iDestruct "S" as (x y fp ra r10 r30)
    "(Hs & Hc & R23 & R0 & R1 & R30 & R10 & R20 & G & M & %F1 & %F2 & %Hx & %Hy & %Hxy & K)".
  iExists (fxw x), (fxw y), fp, ra, r10, r30.
  iFrame "Hs Hc R23 R0 R1 R30 R10 R20 G M".
  iSplitR; [iPureIntro; exact F1|].
  iSplitR; [iPureIntro; exact F2|].
  iSplitR; [iPureIntro; apply fxw_tag_test|].
  iSplitR; [iPureIntro; apply (fxw_no_overflow_iff x y Hx Hy); exact Hxy|].
  iApply (instr_pre_wand with "K"); [done|done|].
  rewrite fxw_add. iIntros "P". iExact "P".
Qed.
