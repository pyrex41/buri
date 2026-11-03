(* E2E-20 Wave D: shared definitions for the trace-to-model bridges.

   NOT a scripts/prove module (docs/ARM-FOUNDATION.md section 12; checked
   by scripts/check-arm.sh Part B).

   Trace side.  `mrun mem t regs r` is a complete, never-blocking run of the
   isla trace t under Islaris's own small-step relation `seq_step`
   (isla.opsem), from register map regs to tnil with map r, with no
   instruction table and the fixed byte memory mem (no labels are emitted, so
   every memory read is served by mem).  `run_to_end` of BuriArmBridge.v is
   `mrun ∅` (run_to_end_mrun).  mrun_invert computes, from the head of the
   trace, what the first step of any such run must have been; it is the
   inversion principle used for the "every run" (converse) theorems.

   The register correspondence.  `agree rs regs` relates the model's register
   record rs (sail-arm armv9_types.regstate) and an isla register map regs on
   the registers the fast-path traces touch: the 31 general-purpose
   registers (Sail R0..R30 = isla "R0".."R30"), the program counter (Sail
   _PC = isla "_PC") and PSTATE.{N,Z,C,V} (isla "PSTATE" a struct whose
   first four fields are N, Z, C, V, the rest unconstrained).  It says
   nothing about other registers.

   Everything here is closed under the global context. *)
From isla Require Import opsem automation.
Require Import SailStdpp.Base.
Require Import armv9_types armv9.
Require Import BuriArm.BuriArmAdds BuriArm.BuriArmBridge BuriArm.BuriArmSeq.
Import Defs.
Open Scope Z.

(* ---------------------------------------------------------------- *)
(* Runs with a fixed memory. *)
Definition σm (mem : mem_map) : seq_global_state := {| seq_instrs := ∅; seq_mem := mem |}.

Inductive mrun (mem : mem_map) : isla_trace → reg_map → reg_map → Prop :=
| MEnd regs : mrun mem tnil regs regs
| MStep t regs t' regs' r :
    seq_step (lst t regs) (σm mem) [] (lst t' regs') (σm mem) [] →
    mrun mem t' regs' r → mrun mem t regs r.

Lemma run_to_end_mrun t regs r : run_to_end t regs r ↔ mrun ∅ t regs r.
Proof.
  split; induction 1; econstructor; eauto.
Qed.

Definition mrun_inv (mem : mem_map) (t : isla_trace) (regs r : reg_map) : Prop :=
  match t with
  | tnil => r = regs
  | tcases ts => ∃ t', t' ∈ ts ∧ mrun mem t' regs r
  | tcons e t' =>
      match e with
      | Smt (DeclareConst x (Ty_BitVec n)) _ =>
          ∃ b : bv n, mrun mem (subst_trace (Val_Bits b) x t') regs r
      | Smt (DeclareConst x Ty_Bool) _ => ∃ b, mrun mem (subst_trace (Val_Bool b) x t') regs r
      | Smt (DefineConst x e) _ => ∃ v, eval_exp e = Some v ∧ mrun mem (subst_trace v x t') regs r
      | Smt (Assert e) _ => eval_exp e = Some (Val_Bool true) ∧ mrun mem t' regs r
      | ReadReg reg al v _ =>
          ∃ v' vr, regs !! reg = Some v' ∧ read_accessor al v' = Some vr ∧
                   read_accessor al v = Some vr ∧ mrun mem t' regs r
      | WriteReg reg al v _ =>
          ∃ v' vnew v'', regs !! reg = Some v' ∧ read_accessor al v = Some vnew ∧
                   write_accessor al v' vnew = Some v'' ∧ mrun mem t' (<[reg := v'']> regs) r
      | AssumeReg reg al v _ =>
          ∃ v', regs !! reg = Some v' ∧ read_accessor al v' = Some v ∧ mrun mem t' regs r
      | Assume e _ => eval_a_exp regs e = Some (Val_Bool true) ∧ mrun mem t' regs r
      | ReadMem data kind addr len tag _ =>
          ∃ (a : bv 64) (d : bv (8 * len)),
            addr = RVal_Bits (bv_to_bvn a) ∧ data = RVal_Bits (bv_to_bvn d) ∧
            opsem.read_mem mem (bv_unsigned a) len = Some (bv_to_bvn d) ∧ mrun mem t' regs r
      | BranchAddress _ _ => mrun mem t' regs r
      | _ => True
      end
  end.

Lemma mrun_invert mem t regs r : mrun mem t regs r → mrun_inv mem t regs r.
Proof.
  destruct 1 as [regs|t regs t' regs' r Hs Hr]; [reflexivity|].
  inversion Hs as [σ θ κ t'' κ' θ' σ' Hnb Ht Hk]; subst. cbn in Ht, Hk.
  destruct Ht; cbn; try exact I.
  all: repeat match goal with
       | H : _ ∧ _ |- _ => destruct H
       | H : ∃ _, _ |- _ => destruct H
       | H : _ ∨ _ |- _ => destruct H
       end; unfold lst in *; simplify_eq/=; eauto 10.
  - match goal with b : bool |- _ => destruct b end; [|discriminate]. eauto.
  - match goal with H : match opsem.read_mem _ _ _ with _ => _ end |- _ => revert H end.
    case_match.
    + intros (? & -> & _ & [[? ->]|?]); simplify_eq; try done; eexists _, _; split_and!; done.
    + intros (_ & _ & -> & _). discriminate.
  - match goal with H : match ∅ !! _ with _ => _ end |- _ => rewrite lookup_empty in H; destruct H end.
    simplify_eq.
Qed.

(* ---------------------------------------------------------------- *)
(* Forward steps beyond BuriArmBridge.v's (now with memory). *)
Lemma mstep_none mem t regs t' :
  trace_step t regs None t' → seq_step (lst t regs) (σm mem) [] (lst t' regs) (σm mem) [].
Proof.
  intros H. refine (SeqStep (σm mem) (lst t regs) None t' None (lst t' regs) (σm mem) _ _ _); done.
Qed.

Lemma mstep_read mem t regs t' r al v v' vr :
  trace_step t regs (Some (LReadReg r al v)) t' →
  regs !! r = Some v' → read_accessor al v' = Some vr → read_accessor al v = Some vr →
  seq_step (lst t regs) (σm mem) [] (lst t' regs) (σm mem) [].
Proof.
  intros H ???.
  refine (SeqStep (σm mem) (lst t regs) (Some (LReadReg r al v)) t' None (lst t' regs) (σm mem) _ _ _);
    [done|done|].
  eexists _, _, _. split_and!; [done|done|done|done|done|]. left. done.
Qed.

Lemma mstep_write mem t regs t' r al v v' vnew v'' :
  trace_step t regs (Some (LWriteReg r al v)) t' →
  regs !! r = Some v' → read_accessor al v = Some vnew → write_accessor al v' vnew = Some v'' →
  seq_step (lst t regs) (σm mem) [] (lst t' (<[r := v'']> regs)) (σm mem) [].
Proof.
  intros H ???.
  refine (SeqStep (σm mem) (lst t regs) (Some (LWriteReg r al v)) t' None
            (lst t' (<[r := v'']> regs)) (σm mem) _ _ _); [done|done|].
  eexists _, _, _. split_and!; done.
Qed.

Lemma mstep_assume_reg mem t regs t' r al v v' :
  trace_step t regs (Some (LAssumeReg r al v)) t' →
  regs !! r = Some v' → read_accessor al v' = Some v →
  seq_step (lst t regs) (σm mem) [] (lst t' regs) (σm mem) [].
Proof.
  intros H ??.
  refine (SeqStep (σm mem) (lst t regs) (Some (LAssumeReg r al v)) t' None (lst t' regs) (σm mem) _ _ _);
    [done|done|].
  eexists _. split_and!; done.
Qed.

Lemma mstep_assert mem e ann t regs :
  eval_exp e = Some (Val_Bool true) →
  seq_step (lst (Smt (Assert e) ann :t: t) regs) (σm mem) [] (lst t regs) (σm mem) [].
Proof.
  intros H.
  refine (SeqStep (σm mem) (lst _ regs) (Some (LAssert true)) t None (lst t regs) (σm mem) _ _ _);
    [done|by constructor|]. done.
Qed.

Lemma mstep_assume mem e ann t regs :
  eval_a_exp regs e = Some (Val_Bool true) →
  seq_step (lst (Assume e ann :t: t) regs) (σm mem) [] (lst t regs) (σm mem) [].
Proof.
  intros H.
  refine (SeqStep (σm mem) (lst _ regs) (Some (LAssume true)) t None (lst t regs) (σm mem) _ _ _);
    [done|by constructor|]. done.
Qed.

Lemma mstep_branch_address mem v ann t regs :
  seq_step (lst (BranchAddress v ann :t: t) regs) (σm mem) [] (lst t regs) (σm mem) [].
Proof.
  refine (SeqStep (σm mem) (lst _ regs) (Some (LBranchAddress v)) t None (lst t regs) (σm mem) _ _ _);
    [done|by constructor|]. done.
Qed.

Lemma mstep_read_mem mem (a : bv 64) len (d : bv (8 * len)) kind tag ann t regs :
  0 < Z.of_N len →
  opsem.read_mem mem (bv_unsigned a) len = Some (bv_to_bvn d) →
  seq_step (lst (ReadMem (RVal_Bits (bv_to_bvn d)) kind (RVal_Bits (bv_to_bvn a)) len tag ann :t: t) regs)
    (σm mem) [] (lst t regs) (σm mem) [].
Proof.
  intros Hl H.
  refine (SeqStep (σm mem) (lst _ regs) (Some (LReadMem _ kind _ len tag)) t None (lst t regs) (σm mem) _ _ _);
    [done|by constructor|].
  exists a, d, d. split_and!; [done|done|done|]. cbn. rewrite H. split_and!; [done|done|done|]. left. done.
Qed.

Ltac mdecl v := eapply MStep; [apply mstep_none; apply (DeclareConstBitVecS' v)|]; norm.
Ltac mdefc := eapply MStep;
  [apply mstep_none; eapply DefineConstS; apply eval_exp'_sound; evlazy; reflexivity|]; norm.
Ltac mrd := eapply MStep;
  [eapply mstep_read; [econstructor | by simplify_map_eq | reflexivity | reflexivity] |]; norm.
Ltac mwr := eapply MStep;
  [eapply mstep_write; [econstructor | by simplify_map_eq | reflexivity | reflexivity] |]; norm.
Ltac masm := eapply MStep;
  [eapply mstep_assume_reg; [econstructor | by simplify_map_eq | reflexivity] |]; norm.
Ltac massert := eapply MStep;
  [apply mstep_assert; apply eval_exp'_sound; evlazy; reflexivity |]; norm.
Ltac mcase n := eapply MStep;
  [apply mstep_none; apply CasesES; cbn [fmap list_fmap]; repeat (first [ (do n right); left | left | right ])|]; norm.
Ltac mba := eapply MStep; [apply mstep_branch_address|]; norm.

(* ---------------------------------------------------------------- *)
(* The register correspondence. *)
Definition gprs : list (string * register (mword 64)) :=
  [ ("R0", (R0 : register (mword 64))); ("R1", (R1 : register (mword 64))); ("R2", (R2 : register (mword 64))); ("R3", (R3 : register (mword 64)));
   ("R4", (R4 : register (mword 64))); ("R5", (R5 : register (mword 64))); ("R6", (R6 : register (mword 64))); ("R7", (R7 : register (mword 64)));
   ("R8", (R8 : register (mword 64))); ("R9", (R9 : register (mword 64))); ("R10", (R10 : register (mword 64))); ("R11", (R11 : register (mword 64)));
   ("R12", (R12 : register (mword 64))); ("R13", (R13 : register (mword 64))); ("R14", (R14 : register (mword 64))); ("R15", (R15 : register (mword 64)));
   ("R16", (R16 : register (mword 64))); ("R17", (R17 : register (mword 64))); ("R18", (R18 : register (mword 64))); ("R19", (R19 : register (mword 64)));
   ("R20", (R20 : register (mword 64))); ("R21", (R21 : register (mword 64))); ("R22", (R22 : register (mword 64))); ("R23", (R23 : register (mword 64)));
   ("R24", (R24 : register (mword 64))); ("R25", (R25 : register (mword 64))); ("R26", (R26 : register (mword 64))); ("R27", (R27 : register (mword 64)));
   ("R28", (R28 : register (mword 64))); ("R29", (R29 : register (mword 64))); ("R30", (R30 : register (mword 64))) ].

Definition agree_gprs (rs : regstate) (regs : reg_map) : Prop :=
  ∀ s r, In (s, r) gprs → regs !! s = Some (RVal_Bits (register_lookup r rs : bv 64)).

Definition agree (rs : regstate) (regs : reg_map) : Prop :=
  agree_gprs rs regs ∧
  regs !! "_PC" = Some (RVal_Bits (register_lookup _PC rs : bv 64)) ∧
  ∃ rest, let p := register_lookup PSTATE rs in
    regs !! "PSTATE" = Some (pstate_isla (ProcState_N p) (ProcState_Z p) (ProcState_C p) (ProcState_V p) rest).

Lemma nodup_fst_unique {A B} (l : list (A * B)) x y1 y2 :
  base.NoDup (l.*1) → (x, y1) ∈ l → (x, y2) ∈ l → y1 = y2.
Proof.
  revert x y1 y2. induction l as [|[a b] l IH]; intros x y1 y2 Hnd H1 H2; [by apply elem_of_nil in H1|].
  cbn in Hnd. pose proof (NoDup_cons_1_1 _ _ Hnd) as Hni. pose proof (NoDup_cons_1_2 _ _ Hnd) as Hnd'.
  apply elem_of_cons in H1. apply elem_of_cons in H2.
  destruct H1 as [H1|H1], H2 as [H2|H2].
  - injection H1 as -> ->. injection H2 as ->. reflexivity.
  - injection H1 as -> ->. exfalso. apply Hni, elem_of_list_fmap. exists (a, y2). split; [reflexivity|exact H2].
  - injection H2 as -> ->. exfalso. apply Hni, elem_of_list_fmap. exists (a, y1). split; [reflexivity|exact H1].
  - eapply IH; eauto.
Qed.

Lemma gprs_nodup : base.NoDup (gprs.*1).
Proof. apply (bool_decide_unpack _). vm_compute. reflexivity. Qed.

(* A model-side register write that is not a general-purpose register. *)
Lemma agree_gprs_model_other {T} rs regs (X : register T) v :
  forallb (λ sr, negb (register_beq sr.2 X)) gprs = true →
  agree_gprs rs regs → agree_gprs (register_set X v rs) regs.
Proof.
  unfold agree_gprs. intros Hb H s r Hin. specialize (H _ _ Hin).
  rewrite forallb_forall in Hb. specialize (Hb _ Hin). cbn in Hb.
  rewrite irrelevant_register_set; [exact H|]. destruct (register_beq r X); [discriminate|reflexivity].
Qed.

(* An isla-side write to a name that is not a general-purpose register. *)
Lemma agree_gprs_isla_other rs regs s w :
  forallb (λ sr, negb (bool_decide (sr.1 = s))) gprs = true →
  agree_gprs rs regs → agree_gprs rs (<[s := w]> regs).
Proof.
  unfold agree_gprs. intros Hb H s' r Hin. specialize (H _ _ Hin).
  rewrite forallb_forall in Hb. specialize (Hb _ Hin). cbn in Hb.
  rewrite lookup_insert_ne; [exact H|]. intros ->. rewrite bool_decide_true in Hb; done.
Qed.

(* A write of one general-purpose register on both sides. *)
Lemma agree_gprs_write rs regs s (r : register (mword 64)) v :
  In (s, r) gprs →
  forallb (λ sr, bool_decide (sr.1 = s) || negb (register_beq sr.2 r)) gprs = true →
  agree_gprs rs regs → agree_gprs (register_set r v rs) (<[s := RVal_Bits v]> regs).
Proof.
  unfold agree_gprs. intros Hsr Hb H s' r' Hin. specialize (H _ _ Hin).
  rewrite forallb_forall in Hb. specialize (Hb _ Hin). cbn in Hb.
  destruct (decide (s' = s)) as [->|Hs].
  - rewrite lookup_insert.
    assert (r' = r) as ->.
    { eapply nodup_fst_unique; [apply gprs_nodup | apply elem_of_list_In, Hin | apply elem_of_list_In, Hsr]. }
    rewrite register_lookup_set. done.
  - rewrite lookup_insert_ne; [|congruence]. rewrite bool_decide_false in Hb; [|exact Hs]. cbn in Hb.
    rewrite irrelevant_register_set; [exact H|].
    destruct (register_beq r' r); [discriminate|reflexivity].
Qed.

(* ---------------------------------------------------------------- *)
(* Backward (every-run) tactics. *)
Lemma RVal_Bits_inj {n} (a b : bv n) : RVal_Bits a = RVal_Bits b → a = b.
Proof.
  intros H. apply bv_eq.
  exact (f_equal (λ v : valu, match v with RegVal_Base (Val_Bits w) => bvn_unsigned w | _ => 0 end) H).
Qed.

Ltac mb_eval :=
  repeat match goal with
  | H : eval_exp ?e = Some ?v |- _ =>
      let Hd := fresh in
      eassert (Hd : eval_exp e = Some _) by (apply eval_exp'_sound; evlazy; reflexivity);
      rewrite Hd in H; injection H as H; try subst v; clear Hd
  end.
Ltac mb_side :=
  repeat match goal with
  | H : read_accessor _ _ = Some _ |- _ => unfold read_accessor in H; cbn in H
  | H : write_accessor _ _ _ = Some _ |- _ => unfold write_accessor in H; cbn in H
  | H : Some _ = Some _ |- _ => injection H as H
  | H : RegVal_Base (Val_Bits _) = RegVal_Base (Val_Bits _) |- _ => apply RVal_Bits_inj in H
  | H : RegVal_Struct _ = RegVal_Struct _ |- _ => injection H as H
  | H : Val_Bool _ = Val_Bool _ |- _ => injection H as H
  | H : _ ∈ _ :: _ |- _ => apply elem_of_cons in H; destruct H as [H|H]
  | H : _ ∈ [] |- _ => apply elem_of_nil in H; destruct H
  | H : ?x = ?y |- _ => is_var x; subst x
  | H : ?x = ?y |- _ => is_var y; subst y
  end.

(* Backward: peel one step off a run hypothesis H and solve the side facts
   (lookups, accessors, evaluated SMT expressions) it carries. *)
Ltac mb H :=
  apply mrun_invert in H; cbn [mrun_inv] in H;
  repeat match type of H with
  | ∃ _, _ => let x := fresh "x" in destruct H as [x H]
  | _ ∧ _ => let x := fresh "E" in destruct H as [x H]
  end;
  cbn [subst_trace subst_val_event subst_val_smt subst_val_valu subst_val_exp subst_val_base_val eq_var_name Z.eqb Pos.eqb List.map fst snd] in H; mb_eval; simplify_map_eq; mb_side.


Print Assumptions run_to_end_mrun.
Print Assumptions mrun_invert.
Print Assumptions agree_gprs_model_other.
Print Assumptions agree_gprs_isla_other.
Print Assumptions agree_gprs_write.
Print Assumptions RVal_Bits_inj.
