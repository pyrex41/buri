(* Shen/JIT Phase 2: primitive parametricity (kref-prim). Proves JitKTerm.prim_compat_statement: every
   table primitive under jit_rules_nr, and every port primitive jit_rules_nr gives, maps VRel-related
   arguments and SRel-related stores to PrimOutRel-related results. It re-opens Section Equiv with
   JitKTerm.v's Variables and the abbreviations of JitKTermGround.v / JitKTermBase.v. No Definition here
   changes a JitKTerm statement; the helper Definitions (vsize, pargs, pclauses, shape, prim_param,
   rule_param, the family lists) are used by lemma statements only.

   What is proved (every Theorem is in Audit_Jit and prints "Closed under the global context"):
   - One lemma per family, each `forall k w p, In p fam_X -> prim_param k w p`:
     (a) prim_param_arith: + - * / > < >= <= number? string->n (first order: equal numbers in, equal
         results out; the integer range and the profile's inexact slots see the same numbers);
     (b) prim_param_data: cons hd tl cons? pos tlstr cn str string? n->string intern (str of a
         closure or a vector is a constant text, '#<procedure>' or '#<absvector>': jit_str_other
         reads no location and no body);
     (c) prim_param_vector: absvector (the world grows by the pair of new locations, which are fresh on
         both sides because SRel allocates every world location), address-> (the replaced cell's
         partner is the one the bijection gives; every other pair keeps its cells), <-address,
         absvector?;
     (d) prim_param_globals: value (gvals are Forall2-positional, so lookup finds partners), set (a
         new head entry on both sides);
     (e) prim_param_io: read-byte write-byte open close get-time (the same request, and for every
         response outcomes related at w, the store unchanged);
     (f) prim_param_error: simple-error error-to-string (exceptions are equal under VRel);
     (g) prim_param_eq: =, from prim_param_eq_from, which takes
         JitEqBudgetCore.eq_budget_closed_statement (jit_rules_nr sealed) as its only hypothesis and is
         instantiated with JitEqBudgetCore.eq_budget_closed. On each side S is the world's side
         (map fst w, map snd w): closed in its heap, duplicate-free and of the world's length
         (JitKTermBase.world_closed / world_closed_alloc), and at most that heap's length, so each
         side's budget S (length heap) moves to the common budget S (length w); the operands point
         into S (JitKTermBase.VRel_ptrs). Then eq_lock walks the two comparisons at that one budget in
         lockstep: vectors by the bijection (Nat.eqb of partners agrees, cells are GVal-related),
         closures by same_id, numbers equal under GVal. jit_eq_per gives eq_budget_closed's two
         hypotheses on number equality; the lockstep itself does not need it. eq_budget_statement
         (with its global lok, which SRel does not give: JitKTermBase.SRel_lok_refuted) is not used.
     (h) prim_param_eval_kl: eval-kl's PRIMITIVE step, parse [] of related data, gives the same
         expression on both sides (parse_sk: parse reads only the first-order skeleton, and rejects a
         vector, stream, closure, partial application or exception wherever it reads one; the
         second slot of (type X T) is not read). Running that expression in the empty environment
         is the fundamental property's job (kref-fund), not this file's.
   - prim_compat_table: the first conjunct, for every prim (all_prims_complete partitions them).
   - port_compat_of: the second conjunct, for ANY port_prim table, from the parametricity of each
     rule it returns (rule_param). jit_rules_nr gives none (JitKTermBase.jit_port_prim_none), so for it
     the hypothesis is vacuous; if Reuben approves a table (JitProfile.jit_port_prims_proposed or
     jit_port_prims_core), wiring it in needs rule_param for each of its rules and nothing else here.
   - prim_compat: JitKTerm.prim_compat_statement, with no hypothesis.

   Does NOT prove: rule_param for any proposed port rule (OB-JIT-PORT-PRIMS). Those that hash a key
   (shen-jit.hash, dict-find, dict-put, dict-remove) take the environment's hash of the heap and a
   value, so their proof would need that hash invariant under the world's bijection (not proved; no
   counterexample is checked here). Nor eval-kl's evaluation of the parsed expression (kref-fund). *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitProfile JitKTerm JitKTermGround
 JitKTermBase JitLowerEquiv JitEqBudget JitEqBudgetStep JitEqBudgetCore.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitKTermPrim.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitKTerm.JitKTerm.
Module St := JitEqBudgetStep.JitEqBudgetStep.
Module Core := JitEqBudgetCore.JitEqBudgetCore.
Module G := JitKTermGround.JitKTermGround.
Module Bs := JitKTermBase.JitKTermBase.

(* ======================= = in lockstep, at one budget, on the ground relation ======================= *)
Lemma eq_cons_unfold : forall R P H d a1 a2 b1 b2, eq_depth_r R P H (S d) (VCons a1 a2) (VCons b1 b2) =
 match eq_depth_r R P H (S d) a1 b1 with Some true => eq_depth_r R P H (S d) a2 b2 | r => r end.
Proof. reflexivity. Qed.

Lemma eq_vec_unfold : forall R P H d l1 l2, eq_depth_r R P H (S d) (VVec l1) (VVec l2) =
 if Nat.eqb l1 l2 then Some true else match nth_error H l1, nth_error H l2 with
 | Some xs, Some ys => list_eq (eq_depth_r R P H d) xs ys | _, _ => None end.
Proof. reflexivity. Qed.

Section Lock.
Variable sealed : list name.
Notation R := (jit_rules_nr sealed).
Notation P := jit_profile.
Variables (w : world) (h0 h : list (list value)).
Hypothesis W : wf_world w.
Hypothesis Hc : forall l0 l, In (l0, l) w -> exists c0 c, nth_error h0 l0 = Some c0 /\
 nth_error h l = Some c /\ Forall2 (GVal w) c0 c.

Lemma eqb_bij : forall a0 a b0 b, In (a0, a) w -> In (b0, b) w -> Nat.eqb a0 b0 = Nat.eqb a b.
Proof.
 intros a0 a b0 b Ia Ib. destruct W as [F1 F2].
 destruct (Nat.eqb_spec a0 b0) as [E|E]; destruct (Nat.eqb_spec a b) as [E'|E']; auto; subst.
 - exfalso. apply E'. eapply G.nodup_fst_uniq; eauto.
 - exfalso. apply E. eapply G.nodup_snd_uniq; eauto.
Qed.

#[local] Arguments eq_opaque_r : simpl never.
Lemma opaque_rel : forall a0 a b0 b, GVal w a0 a -> GVal w b0 b -> eq_opaque_r R a0 b0 = eq_opaque_r R a b.
Proof.
 intros a0 a b0 b Ha Hb. unfold eq_opaque_r. cbn [object_identity jit_rules_nr].
 destruct a0, a; cbn in Ha; try contradiction; destruct b0, b; cbn in Hb; try contradiction; cbn; try reflexivity.
 all: revert Ha Hb; unfold same_id; cbn.
 all: repeat match goal with |- context [closure_id ?r] => destruct (closure_id r) end; intros; try contradiction; try reflexivity.
 all: f_equal; apply eqb_bij; assumption.
Qed.

Lemma list_eq_rel : forall (f g : value -> value -> option bool) xs0 xs ys0 ys,
 Forall2 (GVal w) xs0 xs -> Forall2 (GVal w) ys0 ys ->
 (forall a0 a b0 b, GVal w a0 a -> GVal w b0 b -> f a0 b0 = g a b) ->
 list_eq f xs0 ys0 = list_eq g xs ys.
Proof.
 intros f g xs0 xs ys0 ys F1. revert ys0 ys.
 induction F1 as [|x0 x xs0 xs Hx F IH]; intros ys0 ys F2 E; destruct F2 as [|y0 y ys0 ys Hy F2']; cbn; try reflexivity.
 rewrite (E x0 x y0 y Hx Hy). destruct (g x y) as [[|]|]; try reflexivity. apply IH; assumption.
Qed.

(* The lockstep walk: at any one budget, = on GVal-related operands answers alike on the two heaps. *)
Theorem eq_lock : forall d a0 a b0 b, GVal w a0 a -> GVal w b0 b ->
 eq_depth_r R P h0 d a0 b0 = eq_depth_r R P h d a b.
Proof.
 induction d as [|d IHd]; [reflexivity|].
 intro a0. induction a0 as [n|x|bb|t| |a1 IH1 a2 IH2|l|st|x0 e0 r0|e1 r1|f0 as0|ex];
  intros a b0 b Ha Hb; destruct a; cbn in Ha; try contradiction;
  destruct b0; destruct b; cbn in Hb; try contradiction; subst; try reflexivity;
  try (cbn; apply opaque_rel; cbn; first [assumption | split; assumption]; fail).
 - rewrite !eq_cons_unfold. destruct Ha as [Ha1 Ha2]. destruct Hb as [Hb1 Hb2].
   rewrite (IH1 _ _ _ Ha1 Hb1).
   match goal with |- match ?x with _ => _ end = _ => destruct x as [[|]|] end; try reflexivity.
   apply IH2; assumption.
 - rewrite !eq_vec_unfold. rewrite (eqb_bij _ _ _ _ Ha Hb). destruct (Nat.eqb l0 l2); [reflexivity|].
   destruct (Hc _ _ Ha) as (c0 & c & N0 & N & F). destruct (Hc _ _ Hb) as (d0 & d1 & M0 & M & F').
   rewrite N0, N, M0, M. apply list_eq_rel; auto.
Qed.
End Lock.

(* ======================= eval-kl's primitive step: parse reads the first-order skeleton ======================= *)
(* parse's two local helpers, as top-level functions over the same parse. *)
Definition pargs (scope : list name) : value -> option (list expr) :=
 fix args (v : value) : option (list expr) := match v with
 | VNil => Some []
 | VCons a d => match parse scope a, args d with Some e, Some es => Some (e :: es) | _, _ => None end
 | _ => None end.
Definition pclauses (scope : list name) : value -> option (list (expr * expr)) :=
 fix clauses (v : value) : option (list (expr * expr)) := match v with
 | VNil => Some []
 | VCons (VCons c (VCons b VNil)) more => match parse scope c, parse scope b, clauses more with
   | Some ec, Some eb, Some cs => Some ((ec, eb) :: cs) | _, _, _ => None end
 | _ => None end.
Lemma pargs_cons : forall scope a d, pargs scope (VCons a d) =
 match parse scope a, pargs scope d with Some e, Some es => Some (e :: es) | _, _ => None end.
Proof. reflexivity. Qed.
Lemma pclauses_cons : forall scope a d, pclauses scope (VCons a d) =
 match a with
 | VCons c (VCons b VNil) => match parse scope c, parse scope b, pclauses scope d with
   | Some ec, Some eb, Some cs => Some ((ec, eb) :: cs) | _, _, _ => None end
 | _ => None end.
Proof. reflexivity. Qed.

Lemma parse_cons_unfold : forall scope h t, parse scope (VCons h t) =
   match h with
   | VSym s =>
     if text_eqb s (kw "lambda") then match t with
       | VCons (VSym x) (VCons b VNil) => option_map (ELam x) (parse (x :: scope) b) | _ => None end
     else if text_eqb s (kw "let") then match t with
       | VCons (VSym x) (VCons a (VCons b VNil)) => match parse scope a, parse (x :: scope) b with
         | Some ea, Some eb => Some (ELet x ea eb) | _, _ => None end
       | _ => None end
     else if text_eqb s (kw "if") then match t with
       | VCons c (VCons a (VCons b VNil)) => match parse scope c, parse scope a, parse scope b with
         | Some ec, Some ea, Some eb => Some (EIf ec ea eb) | _, _, _ => None end
       | _ => None end
     else if text_eqb s (kw "and") then match t with
       | VCons a (VCons b VNil) => match parse scope a, parse scope b with
         | Some ea, Some eb => Some (EAnd ea eb) | _, _ => None end
       | _ => None end
     else if text_eqb s (kw "or") then match t with
       | VCons a (VCons b VNil) => match parse scope a, parse scope b with
         | Some ea, Some eb => Some (EOr ea eb) | _, _ => None end
       | _ => None end
     else if text_eqb s (kw "cond") then option_map ECond (pclauses scope t)
     else if text_eqb s (kw "trap-error") then match t with
       | VCons a (VCons b VNil) => match parse scope a, parse scope b with
         | Some ea, Some eb => Some (ETrap ea eb) | _, _ => None end
       | _ => None end
     else if text_eqb s (kw "defun") then match t with
       | VCons (VSym f) (VCons ps (VCons b VNil)) => match symbols ps with
         | Some xs => option_map (EDefun f xs) (parse xs b) | None => None end
       | _ => None end
     else if text_eqb s (kw "freeze") then match t with
       | VCons a VNil => option_map EFreeze (parse scope a) | _ => None end
     else if text_eqb s (kw "type") then match t with
       | VCons a (VCons _ VNil) => option_map EType (parse scope a) | _ => None end
     else if bound scope s then option_map (EApp (EVar s)) (pargs scope t)
     else option_map (ECall s) (pargs scope t)
   | _ => match parse scope h, pargs scope t with Some eh, Some es => Some (EApp eh es) | _, _ => None end
   end.
Proof. reflexivity. Qed.

Fixpoint vsize (v : value) : nat := match v with VCons a d => S (vsize a + vsize d) | _ => 1 end.

Section Parse.
Variable w : world.

(* Destruct a source value a match is blocked on, with what GVal says of its partner. *)
Ltac gsync := match goal with |- context [match ?t with _ => _ end] => is_var t;
 match goal with H : GVal w t ?t' |- _ =>
   destruct t; destruct t'; cbn in H; try contradiction;
   repeat match type of H with _ /\ _ => let H1 := fresh "H" in destruct H as [H1 H] end; subst end end.
Ltac bmatch := match goal with |- context [match ?x with _ => _ end] =>
 lazymatch x with context [match _ with _ => _ end] => fail | _ =>
 lazymatch type of x with bool => destruct x end end end.

Lemma symbols_sk : forall v0 v, GVal w v0 v -> symbols v0 = symbols v.
Proof.
 induction v0 as [n|x|bb|t| |a1 IH1 a2 IH2|l|st|x0 e0 r0|e1 r1|f0 as0|ex]; intros v H; destruct v; cbn in H;
  try contradiction; subst; try reflexivity.
 destruct H as [Ha Hd]. destruct a1; destruct v1; cbn in Ha; try contradiction; subst; try reflexivity.
 cbn. rewrite (IH2 _ Hd). reflexivity.
Qed.

Section Sized.
Variable n : nat.
Hypothesis IHp : forall u0 u sc, (vsize u0 <= n)%nat -> GVal w u0 u -> parse sc u0 = parse sc u.

Ltac rparse := match goal with
 | |- context [parse ?sc ?b] => match goal with H : GVal w b ?b' |- _ =>
     rewrite (IHp b b' sc ltac:(cbn [vsize] in *; lia) H) end
 | |- context [symbols ?p] => match goal with H : GVal w p ?p' |- _ => rewrite (symbols_sk p p' H); destruct (symbols p') end
 end.

Lemma pargs_sk : forall t0 t sc, (vsize t0 <= n)%nat -> GVal w t0 t -> pargs sc t0 = pargs sc t.
Proof.
 induction t0 as [n0|x|bb|tt| |a1 IH1 a2 IH2|l|st|x0 e0 r0|e1 r1|f0 as0|ex]; intros t sc Hs Ht; destruct t; cbn in Ht;
  try contradiction; subst; try reflexivity.
 destruct Ht as [H1 H2]. rewrite !pargs_cons. cbn [vsize] in Hs.
 rewrite (IHp a1 t1 sc ltac:(lia) H1), (IH2 t2 sc ltac:(lia) H2). reflexivity.
Qed.

Lemma pclauses_sk : forall t0 t sc, (vsize t0 <= n)%nat -> GVal w t0 t -> pclauses sc t0 = pclauses sc t.
Proof.
 induction t0 as [n0|x|bb|tt| |a1 IH1 a2 IH2|l|st|x0 e0 r0|e1 r1|f0 as0|ex]; intros t sc Hs Ht; destruct t; cbn in Ht;
  try contradiction; subst; try reflexivity.
 destruct Ht as [H1 H2]. cbn [vsize] in Hs.
 assert (Hm : pclauses sc a2 = pclauses sc t2) by (apply IH2; [lia|exact H2]).
 rewrite !pclauses_cons, Hm.
 repeat (cbn [vsize] in *; first [ reflexivity | gsync | rparse ]).
Qed.
End Sized.

Lemma parse_sk_n : forall n v0 v sc, (vsize v0 <= n)%nat -> GVal w v0 v -> parse sc v0 = parse sc v.
Proof.
 induction n as [|n IHn]; intros v0 v sc Hs Hv; [destruct v0; cbn in Hs; lia|].
 destruct v0; destruct v; cbn in Hv; try contradiction; subst; try reflexivity.
 destruct Hv as [Hh Ht]. cbn [vsize] in Hs. rewrite !parse_cons_unfold.
 rewrite (pargs_sk n IHn v0_2 v2 sc ltac:(lia) Ht), (pclauses_sk n IHn v0_2 v2 sc ltac:(lia) Ht).
 rewrite (IHn v0_1 v1 sc ltac:(lia) Hh).
 repeat (cbn [vsize] in *; first [ reflexivity | bmatch | gsync |
   match goal with
   | |- context [parse ?sc' ?b] => match goal with H : GVal w b ?b' |- _ =>
       rewrite (IHn b b' sc' ltac:(cbn [vsize] in *; lia) H) end
   | |- context [symbols ?p] => match goal with H : GVal w p ?p' |- _ => rewrite (symbols_sk p p' H); destruct (symbols p') end
   end ]).
Qed.

Theorem parse_sk : forall v0 v sc, GVal w v0 v -> parse sc v0 = parse sc v.
Proof. intros v0 v sc H. exact (parse_sk_n (vsize v0) v0 v sc (le_n _) H). Qed.
End Parse.

(* ======================= the relation at a primitive ======================= *)
Section Equiv.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules_nr sealed).
Notation P := jit_profile.
Notation VBody := (JitKTerm.JitKTerm.VBody sealed D).
Notation VRel := (JitKTerm.JitKTerm.VRel sealed D).
Notation SRel := (JitKTerm.JitKTerm.SRel sealed D).
Notation StoreHas := (JitKTerm.JitKTerm.StoreHas D).
Notation PoutRel := (JitKTerm.JitKTerm.PoutRel sealed D).
Notation PrimOutRel := (JitKTerm.JitKTerm.PrimOutRel sealed D).
Notation prim_compat_statement := (JitKTerm.JitKTerm.prim_compat_statement sealed D).
Notation VRel_unfold := (G.VRel_unfold sealed D).

#[local] Arguments JitKTerm.JitKTerm.VRel : simpl never.
#[local] Arguments JitKTerm.JitKTerm.SRel : simpl never.
#[local] Arguments jit_profile : simpl never.
#[local] Arguments jit_char_text : simpl never.
#[local] Arguments kl_eq_r : simpl never.
#[local] Arguments Z.eqb : simpl never.
#[local] Arguments Z.leb : simpl never.
#[local] Arguments Z.ltb : simpl never.
#[local] Arguments Z.geb : simpl never.
#[local] Arguments Z.gtb : simpl never.
#[local] Arguments Z.rem : simpl never.
#[local] Arguments Z.quot : simpl never.
#[local] Arguments Z.add : simpl never.
#[local] Arguments Z.sub : simpl never.
#[local] Arguments Z.mul : simpl never.
#[local] Arguments N.eqb : simpl never.
#[local] Arguments N.ltb : simpl never.

(* What VRel says of a value by its source constructor. *)
Definition shape (k : nat) (w : world) (v0 v : value) : Prop := match v0 with
 | VNum n => v = VNum n | VSym x => v = VSym x | VBool b => v = VBool b | VStr t => v = VStr t
 | VNil => v = VNil | VStream x => v = VStream x | VExn x => v = VExn x
 | VCons a0 d0 => exists a d, v = VCons a d /\ VRel k w a0 a /\ VRel k w d0 d
 | VVec l0 => exists l, v = VVec l /\ In (l0, l) w
 | VLam _ _ r0 => exists x b r, v = VLam x b r /\ same_id w r0 r
 | VFrozen _ r0 => exists b r, v = VFrozen b r /\ same_id w r0 r
 | VPartial f as0 => exists as1, v = VPartial f as1 /\ Forall2 (VRel k w) as0 as1 end.

Lemma VRel_shape : forall k w v0 v, VRel k w v0 v -> shape k w v0 v.
Proof.
 intros k w v0 v H. rewrite VRel_unfold in H.
 destruct v0; destruct v; cbn in H; try contradiction; cbn [shape]; subst; try reflexivity.
 - destruct H as [H1 H2]. do 2 eexists. split; [reflexivity|]. rewrite !VRel_unfold. split; assumption.
 - eexists; split; [reflexivity|assumption].
 - do 3 eexists; split; [reflexivity|]. exact (proj1 H).
 - do 2 eexists; split; [reflexivity|]. exact (proj1 H).
 - apply (G.VBody_partial sealed D) in H as [E F]. subst. eexists; split; [reflexivity|]. rewrite VRel_unfold. exact F.
Qed.

Ltac vinv H := apply VRel_shape in H; cbn [shape] in H;
 repeat match type of H with
 | ex _ => let x := fresh "x" in destruct H as [x H]
 | _ /\ _ => let E := fresh "E" in destruct H as [E H]
 end; subst.

Lemma VRel_num : forall k w n, VRel k w (VNum n) (VNum n).
Proof. intros. rewrite VRel_unfold. reflexivity. Qed.
Lemma VRel_sym : forall k w x, VRel k w (VSym x) (VSym x).
Proof. intros. rewrite VRel_unfold. reflexivity. Qed.
Lemma VRel_bool : forall k w b, VRel k w (VBool b) (VBool b).
Proof. intros. rewrite VRel_unfold. reflexivity. Qed.
Lemma VRel_str : forall k w t, VRel k w (VStr t) (VStr t).
Proof. intros. rewrite VRel_unfold. reflexivity. Qed.
Lemma VRel_nil : forall k w, VRel k w VNil VNil.
Proof. intros. rewrite VRel_unfold. exact I. Qed.
Lemma VRel_stream : forall k w x, VRel k w (VStream x) (VStream x).
Proof. intros. rewrite VRel_unfold. reflexivity. Qed.
Lemma VRel_exn : forall k w x, VRel k w (VExn x) (VExn x).
Proof. intros. rewrite VRel_unfold. reflexivity. Qed.
Lemma VRel_cons : forall k w a0 a d0 d, VRel k w a0 a -> VRel k w d0 d -> VRel k w (VCons a0 d0) (VCons a d).
Proof. intros k w a0 a d0 d A B. rewrite VRel_unfold in A, B |- *. split; assumption. Qed.
Lemma VRel_vec : forall k w l0 l, In (l0, l) w -> VRel k w (VVec l0) (VVec l).
Proof. intros. rewrite VRel_unfold. exact H. Qed.

Lemma str_other_jit : str_other jit_profile = jit_str_other.
Proof. reflexivity. Qed.

Ltac vrel := first [ assumption | apply VRel_num | apply VRel_sym | apply VRel_bool | apply VRel_str
 | apply VRel_nil | apply VRel_stream | apply VRel_exn | apply VRel_cons; vrel ].

(* A goal that is closed outright: the same exception, both wrong, or a value at the same world. *)
Ltac close := first [ lazymatch goal with |- True => exact I end | lazymatch goal with |- _ = _ => reflexivity end
 | match goal with HS : SRel ?k ?w ?s0 ?s |- exists w', _ =>
     exists w; split; [eapply Bs.wext_self; exact HS | split; [vrel | exact HS]] end ].
(* An IO result: the same request, then every response. *)
Ltac io_step := match goal with |- _ = _ /\ forall r, _ => split; [reflexivity|intro] end.
Ltac dmatch := match goal with |- context [match ?x with _ => _ end] =>
 lazymatch x with context [match _ with _ => _ end] => fail | _ =>
 lazymatch type of x with positive => fail | N => fail | _ => destruct x end end end.
(* Destruct a source argument the goal still mentions, with what VRel says of its target partner. *)
Ltac dv := match goal with Ha : VRel _ _ ?v0 _ |- _ => is_var v0;
 lazymatch goal with |- context [v0] => idtac end; destruct v0; vinv Ha end.
Ltac spine n F := lazymatch n with
 | O => idtac
 | S ?m => let a0 := fresh "a0" in let a := fresh "a" in let l0 := fresh "l0" in let l := fresh "l" in
     let H := fresh "Ha" in let F' := fresh "F" in
     destruct F as [|a0 a l0 l H F']; [|spine m F'] end.
Ltac crunch := repeat (cbn; rewrite ?str_other_jit; first [ close | io_step | dv | dmatch ]).

(* The parametricity of one primitive at k and w. *)
Definition prim_param (k : nat) (w : world) (p : prim) : Prop := forall args0 args s0 s,
 Forall2 (VRel k w) args0 args -> SRel k w s0 s ->
 PrimOutRel k w (prim_rule_r R P p args0 s0) (prim_rule_r R P p args s).

Ltac fo_rule := intros args0 args s0 s F HS; spine 4%nat F; crunch.

(* ---------- (a) arithmetic, comparisons and conversions ---------- *)
Definition fam_arith : list prim := [PAdd; PSub; PMul; PDiv; PGt; PLt; PGe; PLe; PNumberP; PStringToN].

Theorem prim_param_arith : forall k w p, In p fam_arith -> prim_param k w p.
Proof.
 intros k w p I. cbn in I. repeat destruct I as [<-|I]; try destruct I.
 all: fo_rule.
Qed.

(* ---------- (b) lists, strings, symbols ---------- *)
Definition fam_data : list prim := [PCons; PHd; PTl; PConsP; PPos; PTlstr; PCn; PStr; PStringP; PNToString; PIntern].

Theorem prim_param_data : forall k w p, In p fam_data -> prim_param k w p.
Proof.
 intros k w p I. cbn in I. repeat destruct I as [<-|I]; try destruct I.
 all: fo_rule.
Qed.

(* ---------- (e) IO ---------- *)
Definition fam_io : list prim := [PReadByte; PWriteByte; POpen; PClose; PGetTime].

Theorem prim_param_io : forall k w p, In p fam_io -> prim_param k w p.
Proof.
 intros k w p I. cbn in I. repeat destruct I as [<-|I]; try destruct I.
 all: fo_rule.
Qed.

(* ---------- (f) errors ---------- *)
Definition fam_error : list prim := [PSimpleError; PErrorToString].

Theorem prim_param_error : forall k w p, In p fam_error -> prim_param k w p.
Proof.
 intros k w p I. cbn in I. repeat destruct I as [<-|I]; try destruct I.
 all: fo_rule.
Qed.

Lemma absvectorp_param : forall k w, prim_param k w PAbsvectorP.
Proof. intros k w. fo_rule. Qed.

(* ---------- stores ---------- *)
Lemma SRel_cells : forall k w s0 s l0 l, SRel k w s0 s -> In (l0, l) w ->
 exists c0 c, nth_error (heap s0) l0 = Some c0 /\ nth_error (heap s) l = Some c /\ Forall2 (VRel k w) c0 c.
Proof. intros k w s0 s l0 l (W & H0 & H1 & Gf & Gv & Hp) I. exact (Hp _ _ I). Qed.

Lemma Forall2_nth : forall {A B} (Q : A -> B -> Prop) l0 l n, Forall2 Q l0 l ->
 match nth_error l0 n, nth_error l n with Some a, Some b => Q a b | None, None => True | _, _ => False end.
Proof.
 intros A B Q l0 l n F. revert n. induction F as [|a b l0 l Qab F IH]; intros [|n].
 - exact I.
 - exact I.
 - exact Qab.
 - exact (IH n).
Qed.

Lemma lookup_rel : forall k w x g0 g, Forall2 (fun p0 p => fst p0 = fst p /\ VRel k w (snd p0) (snd p)) g0 g ->
 match lookup x g0, lookup x g with Some a, Some b => VRel k w a b | None, None => True | _, _ => False end.
Proof.
 intros k w x g0 g F. induction F as [|[y0 a0] [y a] g0 g [E V] F IH]; cbn; [exact I|].
 cbn in E, V. subst. destruct (text_eqb x y); assumption.
Qed.

Lemma SRel_set : forall k w s0 s x v0 v, SRel k w s0 s -> VRel k w v0 v ->
 SRel k w (Store (heap s0) ((x, v0) :: gvals s0) (gfuns s0)) (Store (heap s) ((x, v) :: gvals s) (gfuns s)).
Proof.
 intros k w s0 s x v0 v (W & H0 & H1 & Gf & Gv & Hp) V.
 split; [exact W|split; [exact H0|split; [exact H1|split; [exact Gf|split; [|exact Hp]]]]].
 constructor; [split; [reflexivity|exact V]|exact Gv].
Qed.

Lemma nth_replace_eq : forall {A} n (x : A) l, (n < List.length l)%nat -> nth_error (replace_nth n x l) n = Some x.
Proof. intros A n x l. revert n. induction l as [|y l IH]; intros [|n] L; cbn in *; try lia; auto. apply IH. lia. Qed.

Lemma nth_replace_neq : forall {A} n m (x : A) l, n <> m -> nth_error (replace_nth n x l) m = nth_error l m.
Proof.
 intros A n m x l. revert n m. induction l as [|y l IH]; intros [|n] [|m] Dnm; cbn; auto; try lia.
Qed.

Lemma Forall2_replace : forall {A B} (Q : A -> B -> Prop) i x0 x c0 c, Forall2 Q c0 c -> Q x0 x ->
 Forall2 Q (replace_nth i x0 c0) (replace_nth i x c).
Proof.
 intros A B Q i x0 x c0 c F. revert i. induction F as [|a b c0 c Qab F IH]; intros [|i] Qx; cbn; constructor; auto.
Qed.

Lemma Forall2_repeat : forall {A B} (Q : A -> B -> Prop) a b n, Q a b -> Forall2 Q (repeat a n) (repeat b n).
Proof. intros A B Q a b n H. induction n; cbn; constructor; auto. Qed.

(* address->: the replaced cell's partner is the one the bijection gives; other pairs keep their cells. *)
Lemma SRel_replace : forall k w s0 s l0 l o0 o c0 c, SRel k w s0 s -> In (l0, l) w ->
 nth_error (heap s0) l0 = Some o0 -> nth_error (heap s) l = Some o -> Forall2 (VRel k w) c0 c ->
 SRel k w (Store (replace_nth l0 c0 (heap s0)) (gvals s0) (gfuns s0)) (Store (replace_nth l c (heap s)) (gvals s) (gfuns s)).
Proof.
 intros k w s0 s l0 l o0 o c0 c (W & H0 & H1 & Gf & Gv & Hp) I N0 N F.
 split; [exact W|split; [exact H0|split; [exact H1|split; [exact Gf|split; [exact Gv|]]]]].
 intros m0 m Im. cbn [heap]. destruct W as [W1 W2].
 destruct (Nat.eq_dec l0 m0) as [<-|D0].
 - assert (m = l) by (eapply G.nodup_fst_uniq; eauto). subst m.
   exists c0, c. rewrite !nth_replace_eq; [auto| |]; apply nth_error_Some; congruence.
 - assert (Dl : l <> m) by (intro E; subst m; apply D0; eapply G.nodup_snd_uniq; eauto).
   rewrite !nth_replace_neq by assumption. exact (Hp _ _ Im).
Qed.

Lemma alloc_ok_jit : forall h n, alloc_ok jit_profile h n = true.
Proof. reflexivity. Qed.

Lemma VRel_fill : forall k w, VRel k w (absvector_fill jit_profile) (absvector_fill jit_profile).
Proof. intros. rewrite VRel_unfold. reflexivity. Qed.

(* absvector: the new locations are fresh on both sides, since SRel allocates every world location. *)
Lemma wext_alloc : forall k w s0 s, SRel k w s0 s ->
 wext w ((List.length (heap s0), List.length (heap s)) :: w).
Proof.
 intros k w s0 s HS. destruct (Bs.world_closed sealed D k w s0 s HS) as (_ & _ & F0 & F1 & _ & A0 & A1 & _).
 split; [intros a I; right; exact I|split; cbn; constructor; try assumption].
 - intro I. specialize (A0 _ I). lia.
 - intro I. specialize (A1 _ I). lia.
Qed.

Lemma SRel_alloc : forall k w s0 s c0 c, SRel k w s0 s ->
 Forall2 (VRel k ((List.length (heap s0), List.length (heap s)) :: w)) c0 c ->
 SRel k ((List.length (heap s0), List.length (heap s)) :: w)
  (Store (heap s0 ++ [c0]) (gvals s0) (gfuns s0)) (Store (heap s ++ [c]) (gvals s) (gfuns s)).
Proof.
 intros k w s0 s c0 c HS F. pose proof (wext_alloc k w s0 s HS) as Wx.
 assert (HS' : SRel k w (Store (heap s0 ++ [c0]) (gvals s0) (gfuns s0)) (Store (heap s ++ [c]) (gvals s) (gfuns s))).
 { destruct HS as (W & H0 & H1 & Gf & Gv & Hp).
   split; [exact W|split; [exact H0|split; [exact H1|split; [exact Gf|split; [exact Gv|]]]]].
   intros l0 l I. destruct (Hp _ _ I) as (d0 & d & N0 & N & Fd). exists d0, d. cbn [heap].
   rewrite !nth_error_app1 by (apply nth_error_Some; congruence). auto. }
 apply (Bs.SRel_wext_cells sealed D k w _ _ _ HS' Wx).
 intros l0 l [E|I]; [|left; exact I]. right. injection E as <- <-. exists c0, c. cbn [heap].
 rewrite !nth_error_app2 by lia. rewrite !Nat.sub_diag. auto.
Qed.

(* Destruct a source argument a match is blocked on, with what VRel says of its target partner. *)
Ltac dvm := match goal with |- context [match ?v0 with _ => _ end] => is_var v0;
 match goal with Ha : VRel _ _ v0 _ |- _ => destruct v0; vinv Ha end end.
Ltac crunch_with t := repeat (cbn; first [ close | t | io_step | dvm | dmatch ]).
Ltac rules := unfold prim_rule_r, prim_rule, rule_absvector, rule_address_set, rule_address_get, rule_value,
 rule_set, rule_equal_r, rule_eval_kl, ret, throw, dom.

(* The cells of a world location, on both sides. *)
Ltac t_heap := match goal with
 | HS : SRel ?k ?w ?s0 ?s, I : In (?l0, ?l) ?w |- context [nth_error (heap ?s0) ?l0] =>
   let c0 := fresh "c0" in let c := fresh "c" in let N0 := fresh "N0" in let N := fresh "N" in let Fc := fresh "Fc" in
   destruct (SRel_cells _ _ _ _ _ _ HS I) as (c0 & c & N0 & N & Fc); rewrite N0, N; try rewrite (Forall2_length Fc)
 end.
Ltac t_nth := match goal with
 | Fc : Forall2 _ ?c0 ?c |- context [nth_error ?c0 ?n] =>
   let Q := fresh "Q" in pose proof (Forall2_nth _ c0 c n Fc) as Q;
   destruct (nth_error c0 n), (nth_error c n); try contradiction
 end.

(* ---------- (c) vectors ---------- *)
Definition fam_vector : list prim := [PAbsvector; PAddressSet; PAddressGet; PAbsvectorP].

Lemma absvector_param : forall k w, prim_param k w PAbsvector.
Proof.
 intros k w args0 args s0 s F HS. rules. spine 2%nat F.
 all: crunch_with ltac:(idtac; first [ rewrite !alloc_ok_jit
   | exists ((List.length (heap s0), List.length (heap s)) :: w);
     split; [exact (wext_alloc k w s0 s HS)|split; [apply VRel_vec; left; reflexivity|]];
     apply SRel_alloc; [exact HS|apply Forall2_repeat, VRel_fill] ]).
Qed.

Lemma address_set_param : forall k w, prim_param k w PAddressSet.
Proof.
 intros k w args0 args s0 s F HS. rules. spine 4%nat F.
 all: crunch_with ltac:(idtac; first [ t_heap
   | exists w; split; [eapply Bs.wext_self; exact HS|split; [apply VRel_vec; assumption|]];
     eapply SRel_replace; [exact HS|eassumption|eassumption|eassumption|];
     apply Forall2_replace; assumption ]).
Qed.

Lemma address_get_param : forall k w, prim_param k w PAddressGet.
Proof.
 intros k w args0 args s0 s F HS. rules. spine 3%nat F.
 all: crunch_with ltac:(idtac; first [ t_heap | t_nth ]).
Qed.

Theorem prim_param_vector : forall k w p, In p fam_vector -> prim_param k w p.
Proof.
 intros k w p I. cbn in I. repeat destruct I as [<-|I]; try destruct I.
 - apply absvector_param.
 - apply address_set_param.
 - apply address_get_param.
 - apply absvectorp_param.
Qed.

(* ---------- (d) globals ---------- *)
Definition fam_globals : list prim := [PValue; PSet].

Ltac t_lookup := match goal with
 | HS : SRel ?k ?w ?s0 ?s |- context [lookup ?x (gvals ?s0)] =>
   let L := fresh "L" in
   pose proof (lookup_rel k w x (gvals s0) (gvals s) (proj1 (proj2 (proj2 (proj2 (proj2 HS)))))) as L;
   destruct (lookup x (gvals s0)), (lookup x (gvals s)); try contradiction
 end.

Theorem prim_param_globals : forall k w p, In p fam_globals -> prim_param k w p.
Proof.
 intros k w p I. cbn in I. repeat destruct I as [<-|I]; try destruct I.
 all: intros args0 args s0 s F HS; rules; spine 3%nat F.
 all: crunch_with ltac:(idtac; first [ t_lookup
   | exists w; split; [eapply Bs.wext_self; exact HS|split; [assumption|]]; apply SRel_set; assumption ]).
Qed.

(* ---------- (g) = ---------- *)
Lemma dptr_din : forall (A : nat -> Prop) v, Bs.dptr A v -> St.din A v.
Proof. intros A v. induction v; cbn; tauto. Qed.

Lemma closed_bridge : forall h cs, Bs.closed_alloc h cs -> St.closed_in h cs.
Proof.
 intros h cs C p I. destruct (C p I) as [xs [E F]]. exists xs. split; [exact E|].
 eapply Forall_impl; [|exact F]. apply dptr_din.
Qed.

Lemma din_vptrs : forall (A : nat -> Prop) v, (forall l, In l (Bs.vptrs v) -> A l) -> St.din A v.
Proof.
 intros A v. induction v; intro H; cbn [Bs.vptrs St.din] in *; try exact I.
 - split; [apply IHv1|apply IHv2]; intros l I; apply H; apply in_or_app; auto.
 - apply H. left. reflexivity.
Qed.

Lemma din_src : forall k w v0 v, VRel k w v0 v -> St.din (fun l => In l (map fst w)) v0.
Proof.
 intros k w v0 v H. apply din_vptrs. intros l I.
 destruct (Bs.Forall2_in_l _ _ _ _ (Bs.VRel_ptrs sealed D k w v0 v H) I) as (l' & _ & Iw).
 apply in_map_iff. exists (l, l'). auto.
Qed.

Lemma din_tgt : forall k w v0 v, VRel k w v0 v -> St.din (fun l => In l (map snd w)) v.
Proof.
 intros k w v0 v H. apply din_vptrs. intros l I.
 destruct (Bs.Forall2_in_r _ _ _ _ (Bs.VRel_ptrs sealed D k w v0 v H) I) as (l' & _ & Iw).
 apply in_map_iff. exists (l', l). auto.
Qed.

(* = on related operands and stores: each side's budget S (length heap) moves to S (length w) by
   eq_budget_closed (the world's side is closed, duplicate-free, and no longer than the heap), and
   eq_lock walks the two at that one budget. *)
Theorem kl_eq_rel_from : Core.eq_budget_closed_statement R -> forall k w a0 a b0 b s0 s,
 VRel k w a0 a -> VRel k w b0 b -> SRel k w s0 s -> kl_eq_r R P (heap s0) a0 b0 = kl_eq_r R P (heap s) a b.
Proof.
 intros EBC k w a0 a b0 b s0 s Ha Hb HS.
 destruct (Bs.world_closed sealed D k w s0 s HS) as (_ & _ & N0 & N1 & L & _ & _ & L0 & L1).
 destruct (Bs.world_closed_alloc sealed D k w s0 s HS) as [C0 C1].
 destruct JitEqBudget.JitEqBudget.jit_eq_per as [Sy Tr].
 unfold kl_eq_r.
 rewrite (EBC P (heap s0) (map fst w) Sy Tr N0 (closed_bridge _ _ C0) a0 b0 (din_src _ _ _ _ Ha) (din_src _ _ _ _ Hb)
   (S (List.length (heap s0)))) by (rewrite Bs.len_map; lia).
 rewrite (EBC P (heap s) (map snd w) Sy Tr N1 (closed_bridge _ _ C1) a b (din_tgt _ _ _ _ Ha) (din_tgt _ _ _ _ Hb)
   (S (List.length (heap s)))) by (rewrite Bs.len_map; lia).
 rewrite L. apply (eq_lock sealed w).
 - exact (Bs.SRel_wf sealed D k w s0 s HS).
 - intros l0 l I. destruct (SRel_cells _ _ _ _ _ _ HS I) as (c0 & c & E0 & E & F).
   exists c0, c. split; [exact E0|split; [exact E|]]. eapply Forall2_impl; [|exact F].
   intros x y. apply (G.VRel_ground sealed D k).
 - exact (G.VRel_ground sealed D k w a0 a Ha).
 - exact (G.VRel_ground sealed D k w b0 b Hb).
Qed.

Definition fam_eq : list prim := [PEqual].

Theorem prim_param_eq_from : Core.eq_budget_closed_statement R -> forall k w p, In p fam_eq -> prim_param k w p.
Proof.
 intros EBC k w p I. cbn in I. destruct I as [<-|[]].
 intros args0 args s0 s F HS. rules. spine 3%nat F.
 all: crunch_with ltac:(idtac; match goal with
   | HS' : SRel ?k' ?w' ?t0 ?t, Ha : VRel _ _ ?a0 ?a, Hb : VRel _ _ ?b0 ?b |- context [kl_eq_r _ _ (heap ?t0) ?a0 ?b0] =>
     rewrite (kl_eq_rel_from EBC k' w' a0 a b0 b t0 t Ha Hb HS'); destruct (kl_eq_r (jit_rules_nr sealed) jit_profile (heap t) a b) end).
Qed.

Theorem prim_param_eq : forall k w p, In p fam_eq -> prim_param k w p.
Proof. exact (prim_param_eq_from (Core.eq_budget_closed R)). Qed.

(* ---------- (h) eval-kl's primitive step ---------- *)
Definition fam_eval : list prim := [PEvalKL].

Theorem prim_param_eval_kl : forall k w p, In p fam_eval -> prim_param k w p.
Proof.
 intros k w p I. cbn in I. destruct I as [<-|[]].
 intros args0 args s0 s F HS. rules. spine 2%nat F; cbn; try close.
 match goal with Ha : VRel _ _ ?d0 ?d |- _ =>
   rewrite (parse_sk w d0 d [] (G.VRel_ground sealed D k w d0 d Ha)); destruct (parse [] d); cbn; reflexivity end.
Qed.

(* ---------- the table ---------- *)
Theorem prim_compat_table : forall k w p, prim_param k w p.
Proof.
 intros k w p. destruct p.
 all: first
  [ apply prim_param_arith; cbn; tauto | apply prim_param_data; cbn; tauto | apply prim_param_vector; cbn; tauto
  | apply prim_param_globals; cbn; tauto | apply prim_param_io; cbn; tauto | apply prim_param_error; cbn; tauto
  | apply prim_param_eq; cbn; tauto | apply prim_param_eval_kl; cbn; tauto ].
Qed.

(* ---------- port primitives ---------- *)
(* A port rule is parametric when it maps related arguments and stores to related results. *)
Definition rule_param (rule : profile -> list value -> store -> presult) : Prop := forall k w args0 args s0 s,
 Forall2 (VRel k w) args0 args -> SRel k w s0 s -> PrimOutRel k w (rule P args0 s0) (rule P args s).

(* For ANY port primitive table: the second conjunct of prim_compat_statement holds once each rule the table
   gives is parametric. Stated for a table pp, so that a table Reuben approves (OB-JIT-PORT-PRIMS) needs only
   rule_param of its rules. *)
Theorem port_compat_of : forall (pp : name -> option (nat * (profile -> list value -> store -> presult))),
 (forall g n rule, pp g = Some (n, rule) -> rule_param rule) ->
 forall k w g n rule args0 args s0 s, pp g = Some (n, rule) ->
 Forall2 (VRel k w) args0 args -> SRel k w s0 s -> PrimOutRel k w (rule P args0 s0) (rule P args s).
Proof. intros pp Hpp k w g n rule args0 args s0 s E F HS. exact (Hpp g n rule E k w args0 args s0 s F HS). Qed.

(* jit_rules_nr gives no port primitive, so the hypothesis of port_compat_of holds vacuously. *)
Theorem port_param_jit : forall g n rule, port_prim R g = Some (n, rule) -> rule_param rule.
Proof. intros g n rule E. rewrite (Bs.jit_port_prim_none sealed g) in E. discriminate E. Qed.

(* JitKTerm.prim_compat_statement, with no hypothesis. *)
Theorem prim_compat : prim_compat_statement.
Proof.
 intros k w. split.
 - intros p args0 args s0 s F HS. exact (prim_compat_table k w p args0 args s0 s F HS).
 - intros g n rule args0 args s0 s E F HS. exact (port_compat_of (port_prim R) port_param_jit k w g n rule args0 args s0 s E F HS).
Qed.

End Equiv.
End JitKTermPrim.
