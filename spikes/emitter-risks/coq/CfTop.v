(** * The theorem: accepted bytes refine their bytecode on all paths (Shen/JIT Phase 0, spike 8).

    [step_sim]: from any accepted point, one bytecode instruction.
    [run_sim]: any bytecode run from an accepted point, composed.
    Both are about every function [check_all] accepts, up to:
    - the allocator's contract ([After], at its call), and what the kernel's [=] does (Hkeq);
    - the bytecode semantics here, which is a spike artifact, not connected to Búri's KLambda. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim WxExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.Examples.emitter_risks_ns Require Import CfDefs CfStep CfRun CfSound CfStepSim CfCases CfCons.
Import ListNotations.
Open Scope bv_scope.

Section Top.
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
Abbreviation AtNext := (AtNext c segs rom regs0 fp vm p cut inv).
Abbreviation AtRet := (AtRet c segs rom regs0 fp vm).
Abbreviation AtAlloc := (AtAlloc c segs rom regs0 fp vm cut).
Abbreviation steps := (steps segs).
Abbreviation bnext := (bnext keq vtrue vfalse p).

Theorem step_sim : forall i s st regs m,
  inv i = Some s -> Rel s st regs m -> (i < length p)%nat ->
  match bnext i st with
  | BNext j st' => exists ms, steps (mkst regs (at_ c (cut i)) m rom) ms /\
      (AtNext j st' ms \/ exists words, AtAlloc s st i words ms)
  | BReturn v st' => exists ms, steps (mkst regs (at_ c (cut i)) m rom) ms /\ AtRet v st ms
  | BOther => False
  end.
Proof.
  intros i s st regs m Hi R Hlt.
  destruct (nth_error p i) as [ins|] eqn:Hn; [|apply nth_error_None in Hn; lia].
  unfold bnext, CfDefs.bnext. rewrite Hn.
  destruct ins as [d o|d a b|d x|d x|t a b l|t x l|l|l|o].
  - destruct (sim_move c cell_of segs rom regs0 fp vm vfalse p cut inv fuel ACC i s st regs m d o Hn Hi R) as (ms & H1 & H2).
    eauto.
  - destruct (sim_cons c cell_of segs rom regs0 fp vm keq vfalse p cut inv fuel ACC i s st regs m d a b Hn Hi R) as (ms & H1 & H2).
    eauto.
  - destruct (sim_hd c cell_of segs rom regs0 fp vm vfalse p cut inv fuel ACC i s st regs m d x Hn Hi R)
      as (Ht & (v & Hv) & ms & H1 & H2).
    rewrite Ht, Z.eqb_refl, Hv. exists ms. split; [exact H1|]. left. unfold hd_of in H2. rewrite Hv in H2. exact H2.
  - destruct (sim_tl c cell_of segs rom regs0 fp vm vfalse p cut inv fuel ACC i s st regs m d x Hn Hi R)
      as (Ht & (v & Hv) & ms & H1 & H2).
    rewrite Ht, Z.eqb_refl, Hv. exists ms. split; [exact H1|]. left. unfold tl_of in H2. rewrite Hv in H2. exact H2.
  - destruct (sim_eq c cell_of segs rom regs0 fp vm keq vtrue vfalse Htrue Hfalse Hkeq WfK p cut inv fuel ACC i s st regs m t a b l Hn Hi R)
      as (ms & H1 & [(Hk & H2)|(Hk & li & Hf & H2)]); rewrite Hk.
    + eauto.
    + rewrite Hf. eauto.
  - destruct (sim_consp c cell_of segs rom regs0 fp vm vtrue vfalse Htrue Hfalse p cut inv fuel ACC i s st regs m t x l Hn Hi R)
      as (ms & H1 & [(Ht & H2)|(Ht & li & Hf & H2)]).
    + rewrite Ht, Z.eqb_refl. eauto.
    + apply Z.eqb_neq in Ht. rewrite Ht, Hf. eauto.
  - destruct (sim_label c cell_of segs rom regs0 fp vm vfalse p cut inv fuel ACC i s st regs m l Hn Hi R) as (ms & H1 & H2).
    eauto.
  - destruct (sim_jump c cell_of segs rom regs0 fp vm vfalse p cut inv fuel ACC i s st regs m l Hn Hi R) as (li & Hf & ms & H1 & H2).
    rewrite Hf. eauto.
  - destruct (sim_ret c cell_of segs rom regs0 fp vm vfalse p cut inv fuel ACC i s st regs m o Hn Hi R) as (ms & H1 & H2).
    eauto.
Qed.

(** Bytecode runs. *)
Inductive bsteps : nat -> bstate -> nat -> bstate -> Prop :=
| bs_refl : forall i st, bsteps i st i st
| bs_step : forall i st j st' k st'', bnext i st = BNext j st' -> bsteps j st' k st'' -> bsteps i st k st''.

Theorem run_sim : forall i st j st', bsteps i st j st' ->
  forall s regs m, inv i = Some s -> Rel s st regs m -> (i < length p)%nat ->
  exists ms, steps (mkst regs (at_ c (cut i)) m rom) ms /\
  (AtNext j st' ms \/ exists k sk stk words, inv k = Some sk /\ AtAlloc sk stk k words ms).
Proof.
  intros i st j st' H. induction H as [i st|i st j st' k st'' Hb Hrest IH]; intros s regs m Hi R Hlt.
  - exists (mkst regs (at_ c (cut i)) m rom). split; [constructor|]. left.
    split; [exact Hlt|]. exists s, regs, m. auto.
  - pose proof (step_sim i s st regs m Hi R Hlt) as Hs. rewrite Hb in Hs.
    destruct Hs as (ms & H1 & [(Hj & s' & regs' & m' & Hs' & -> & R')|(w & Ha)]).
    + destruct (IH s' regs' m' Hs' R' Hj) as (ms2 & H2 & H3).
      exists ms2. split; [eapply steps_trans; eassumption | exact H3].
    + exists ms. split; [exact H1|]. right. exists i, s, st, w. auto.
Qed.

End Top.
