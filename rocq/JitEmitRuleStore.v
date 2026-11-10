(* Shen/JIT Phase 2, emission family Store: value/set on globals and <-address/address->/absvector on vectors (Rule_Store).
   This file owns the family's three hooks into JitEmitRel's mutual Comp block: Rule_Store (a Comp
   judgement), RuleT_Store (a CompT judgement) and RuleO_Store (a CompOp judgement). Each is an
   inductive over relation VARIABLES, one for each of the six relations of the block (Comp, CompT,
   CompOp, CompOps, CompW, CompTA), each in that relation's index shape: the code object and its
   capture names, then the indices of JitLowerRel's relation of the same name. JitEmitRel nests
   them; the six relations occur strictly positively.
   All three start EMPTY (task emit-spec). A family task adds constructors here and re-proves only
   the map and all lemmas of this file, which must stay TRANSPARENT (a `match` term, or `Defined`):
   JitEmitRel.Comp_ind' recurses through the *_all lemmas, and the guard checker unfolds them.
   Downstream proofs use Comp_ind' and never invert these inductives outside this file. *)
From Coq Require Import List NArith.
From Buri Require Import KLSyntax KLValue JitBytecode JitLowerRel.
Import ListNotations.
Module JitEmitRuleStore.
Import KLSyntax.KLSyntax KLValue.KLValue JitLowerRel.JitLowerRel.
Module B := JitBytecode.JitBytecode.

(* The six index shapes. *)
Local Notation RelC := (B.code -> list name -> env -> N -> expr -> dest -> list B.instr -> list B.instr -> Prop).
Local Notation RelT := (B.code -> list name -> env -> N -> expr -> N -> list B.instr -> list B.instr -> Prop).
Local Notation RelO := (B.code -> list name -> env -> N -> expr -> B.operand -> N -> list B.instr -> list B.instr -> Prop).
Local Notation RelS := (B.code -> list name -> env -> N -> list expr -> list B.operand -> list B.instr -> list B.instr -> Prop).
Local Notation RelW := (B.code -> list name -> env -> N -> list expr -> list B.instr -> list B.instr -> Prop).
Local Notation RelA := (B.code -> list name -> env -> N -> N -> list expr -> list (N * N) -> list B.instr -> list B.instr -> Prop).
(* Pointwise inclusion, and the IH-carrying relation (fun i => P i /\ Q i), per shape. *)
Local Notation subC P Q := (forall (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (d : dest) (r r' : list B.instr), P c cv g top e d r r' -> Q c cv g top e d r r').
Local Notation subT P Q := (forall (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (l : N) (r r' : list B.instr), P c cv g top e l r r' -> Q c cv g top e l r r').
Local Notation subO P Q := (forall (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (o : B.operand) (top2 : N) (r r' : list B.instr), P c cv g top e o top2 r r' -> Q c cv g top e o top2 r r').
Local Notation subS P Q := (forall (c : B.code) (cv : list name) (g : env) (top : N) (es : list expr) (os : list B.operand) (r r' : list B.instr), P c cv g top es os r r' -> Q c cv g top es os r r').
Local Notation subW P Q := (forall (c : B.code) (cv : list name) (g : env) (s : N) (es : list expr) (r r' : list B.instr), P c cv g s es r r' -> Q c cv g s es r r').
Local Notation subA P Q := (forall (c : B.code) (cv : list name) (g : env) (s t : N) (es : list expr) (ms : list (N * N)) (r r' : list B.instr), P c cv g s t es ms r r' -> Q c cv g s t es ms r r').
Local Notation andC P Q := (fun (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (d : dest) (r r' : list B.instr) => P c cv g top e d r r' /\ Q c cv g top e d r r').
Local Notation andT P Q := (fun (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (l : N) (r r' : list B.instr) => P c cv g top e l r r' /\ Q c cv g top e l r r').
Local Notation andO P Q := (fun (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (o : B.operand) (top2 : N) (r r' : list B.instr) => P c cv g top e o top2 r r' /\ Q c cv g top e o top2 r r').
Local Notation andS P Q := (fun (c : B.code) (cv : list name) (g : env) (top : N) (es : list expr) (os : list B.operand) (r r' : list B.instr) => P c cv g top es os r r' /\ Q c cv g top es os r r').
Local Notation andW P Q := (fun (c : B.code) (cv : list name) (g : env) (s : N) (es : list expr) (r r' : list B.instr) => P c cv g s es r r' /\ Q c cv g s es r r').
Local Notation andA P Q := (fun (c : B.code) (cv : list name) (g : env) (s t : N) (es : list expr) (ms : list (N * N)) (r r' : list B.instr) => P c cv g s t es ms r r' /\ Q c cv g s t es ms r r').

Inductive Rule_Store (Cp : RelC) (Ct : RelT) (Co : RelO) (Cs : RelS) (Cw : RelW) (Ca : RelA) : RelC := .
Inductive RuleT_Store (Cp : RelC) (Ct : RelT) (Co : RelO) (Cs : RelS) (Cw : RelW) (Ca : RelA) : RelT := .
Inductive RuleO_Store (Cp : RelC) (Ct : RelT) (Co : RelO) (Cs : RelS) (Cw : RelW) (Ca : RelA) : RelO := .

(* Pointwise inclusion of the six relations lifts to Rule_Store. *)
Definition Rule_Store_map (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA) (HC : subC PC QC) (HT : subT PT QT) (HO : subO PO QO) (HS : subS PS QS) (HW : subW PW QW) (HA : subA PA QA)
  (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (d : dest) (r r' : list B.instr) (H : Rule_Store PC PT PO PS PW PA c cv g top e d r r') : Rule_Store QC QT QO QS QW QA c cv g top e d r r' :=
 match H with end.

(* Rule_Store_All P Q: Rule_Store over the IH-carrying relations, so a derivation of it is a Rule_Store
   derivation over P each of whose nested P-premises also satisfies Q. *)
Definition Rule_Store_All (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA) : RelC :=
 Rule_Store (andC PC QC) (andT PT QT) (andO PO QO) (andS PS QS) (andW PW QW) (andA PA QA).

(* From a Rule_Store derivation over P and Q for every P-derivation, the IH-carrying derivation. *)
Definition Rule_Store_all (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA) (HC : subC PC QC) (HT : subT PT QT) (HO : subO PO QO) (HS : subS PS QS) (HW : subW PW QW) (HA : subA PA QA)
  (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (d : dest) (r r' : list B.instr) (H : Rule_Store PC PT PO PS PW PA c cv g top e d r r') : Rule_Store_All PC QC PT QT PO QO PS QS PW QW PA QA c cv g top e d r r' :=
 match H with end.

(* Pointwise inclusion of the six relations lifts to RuleT_Store. *)
Definition RuleT_Store_map (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA) (HC : subC PC QC) (HT : subT PT QT) (HO : subO PO QO) (HS : subS PS QS) (HW : subW PW QW) (HA : subA PA QA)
  (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (l : N) (r r' : list B.instr) (H : RuleT_Store PC PT PO PS PW PA c cv g top e l r r') : RuleT_Store QC QT QO QS QW QA c cv g top e l r r' :=
 match H with end.

(* RuleT_Store_All P Q: RuleT_Store over the IH-carrying relations, so a derivation of it is a RuleT_Store
   derivation over P each of whose nested P-premises also satisfies Q. *)
Definition RuleT_Store_All (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA) : RelT :=
 RuleT_Store (andC PC QC) (andT PT QT) (andO PO QO) (andS PS QS) (andW PW QW) (andA PA QA).

(* From a RuleT_Store derivation over P and Q for every P-derivation, the IH-carrying derivation. *)
Definition RuleT_Store_all (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA) (HC : subC PC QC) (HT : subT PT QT) (HO : subO PO QO) (HS : subS PS QS) (HW : subW PW QW) (HA : subA PA QA)
  (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (l : N) (r r' : list B.instr) (H : RuleT_Store PC PT PO PS PW PA c cv g top e l r r') : RuleT_Store_All PC QC PT QT PO QO PS QS PW QW PA QA c cv g top e l r r' :=
 match H with end.

(* Pointwise inclusion of the six relations lifts to RuleO_Store. *)
Definition RuleO_Store_map (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA) (HC : subC PC QC) (HT : subT PT QT) (HO : subO PO QO) (HS : subS PS QS) (HW : subW PW QW) (HA : subA PA QA)
  (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (o : B.operand) (top2 : N) (r r' : list B.instr) (H : RuleO_Store PC PT PO PS PW PA c cv g top e o top2 r r') : RuleO_Store QC QT QO QS QW QA c cv g top e o top2 r r' :=
 match H with end.

(* RuleO_Store_All P Q: RuleO_Store over the IH-carrying relations, so a derivation of it is a RuleO_Store
   derivation over P each of whose nested P-premises also satisfies Q. *)
Definition RuleO_Store_All (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA) : RelO :=
 RuleO_Store (andC PC QC) (andT PT QT) (andO PO QO) (andS PS QS) (andW PW QW) (andA PA QA).

(* From a RuleO_Store derivation over P and Q for every P-derivation, the IH-carrying derivation. *)
Definition RuleO_Store_all (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA) (HC : subC PC QC) (HT : subT PT QT) (HO : subO PO QO) (HS : subS PS QS) (HW : subW PW QW) (HA : subA PA QA)
  (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (o : B.operand) (top2 : N) (r r' : list B.instr) (H : RuleO_Store PC PT PO PS PW PA c cv g top e o top2 r r') : RuleO_Store_All PC QC PT QT PO QO PS QS PW QW PA QA c cv g top e o top2 r r' :=
 match H with end.
End JitEmitRuleStore.
