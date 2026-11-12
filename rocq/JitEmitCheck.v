(* Shen/JIT Phase 2, task emit-check: a checker for JitEmitRel's extended emission relation Comp'
   (JitEmitRel.Comp, indexed by the code object c and its capture names cv), with soundness.

   Shape. The checker is JitLowerCheck's six functions, ported one for one (stepC .. stepA) with c
   and cv as arguments instead of a Section variable, and with each recursive call made through a
   callback (rc, rt, ro, rs, rw, ra: one per judgement of the block). The fuel-indexed chk .. chkTA
   tie the knot: chk (S n) is stepC on the six functions at n, OR ELSE (only when stepC gives None)
   the Comp hook hC at the same six functions; chkT and chkOp likewise with hT and hO. With the base
   hooks (every family None) acceptance is JitLowerCheck's, definition for definition: the step
   functions are JitLowerCheck's bodies, and the fallback is never taken to Some.

   Families. A family X supplies, IN ITS OWN rocq/JitEmitRule<X>.v (the only file allowed to name
   Rule_X's constructors), hook functions of types HkC, HkT, HkO and their soundness in the graph
   form HookC_ok Rule_X h (HookT_ok, HookO_ok): from callbacks that keep code suffixes, an accepted
   hook gives a Rule_X derivation over the callbacks' GRAPHS (GC rc: "rc maps r to r' and r is a
   suffix of the code"), and a suffix after. Nothing here mentions Comp, so a rule file can state
   it before JitEmitRel exists; the types below unfold to plain Pi-types (no record), so a family
   writes them out by hand and they are convertible. This file lifts such a derivation to Comp
   with the family's Rule_X_all (each nested graph premise gets the fuel IH: the Comp derivation
   and the suffix after) and Rule_X_map (keeping the Comp part), then Comp's hook constructor
   (lift_famC .. lift_famO). It never inverts a Rule_X and never uses Comp_ind' or a generated
   scheme of the block: soundness BUILDS derivations, by induction on fuel.

   Soundness is proved in Section Chk under hypotheses: LiftC hC, LiftT hT, LiftO hO (an accepted
   hook is sound whenever its callbacks are). It is then instantiated (check_emit_sound_hooks) for
   any Hooks record (seven families, each with its graph-form proofs), and for the base hooks
   (check_emit_sound). All closed.

   The stage 0 judge over a Hooks record (judge_emit, tally_emit) is JitLowerStage0.judge with
   check_emit_with in place of JitLowerCheck.check_fn; tests/shen-jit/judge_hooks.sh runs it with
   a hook module given as an argument, and compares it with JitLowerStage0's judge per definition.
   Does NOT say: that the checker accepts every lowering (rejection proves nothing), or anything
   about the semantics of accepted code (JitEmitInv's business). *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitProfile JitLowerRel JitLowerCheck JitLowerStage0
 JitEmitRuleEq JitEmitRuleStore JitEmitRulePrim JitEmitRuleDoFold JitEmitRuleClo JitEmitRuleApp JitEmitRuleTrap JitEmitRel.
Import ListNotations.
Module JitEmitCheck.
Import KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics JitLowerRel.JitLowerRel JitLowerCheck.JitLowerCheck JitEmitRel.JitEmitRel.
Module B := JitBytecode.JitBytecode.
Local Open Scope N_scope.

(* ---------- callbacks, hooks, graphs ---------- *)
Definition FC := B.code -> list name -> env -> N -> expr -> dest -> list B.instr -> option (list B.instr).
Definition FT := B.code -> list name -> env -> N -> expr -> list B.instr -> option (N * list B.instr).
Definition FO := B.code -> list name -> env -> N -> expr -> list B.instr -> option (B.operand * N * list B.instr).
Definition FS := B.code -> list name -> env -> N -> list expr -> list B.instr -> option (list B.operand * list B.instr).
Definition FW := B.code -> list name -> env -> N -> list expr -> list B.instr -> option (list B.instr).
Definition FA := B.code -> list name -> env -> N -> N -> list expr -> list (N * N) -> list B.instr -> option (list B.instr).
Definition HkC := FC -> FT -> FO -> FS -> FW -> FA -> FC.
Definition HkT := FC -> FT -> FO -> FS -> FW -> FA -> FT.
Definition HkO := FC -> FT -> FO -> FS -> FW -> FA -> FO.

Local Notation RelC := (B.code -> list name -> env -> N -> expr -> dest -> list B.instr -> list B.instr -> Prop).
Local Notation RelT := (B.code -> list name -> env -> N -> expr -> N -> list B.instr -> list B.instr -> Prop).
Local Notation RelO := (B.code -> list name -> env -> N -> expr -> B.operand -> N -> list B.instr -> list B.instr -> Prop).
Local Notation RelS := (B.code -> list name -> env -> N -> list expr -> list B.operand -> list B.instr -> list B.instr -> Prop).
Local Notation RelW := (B.code -> list name -> env -> N -> list expr -> list B.instr -> list B.instr -> Prop).
Local Notation RelA := (B.code -> list name -> env -> N -> N -> list expr -> list (N * N) -> list B.instr -> list B.instr -> Prop).
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

(* A family's rule, as JitEmitRule<X>.v declares Rule_X, RuleT_X and RuleO_X. *)
Definition RuleCty := RelC -> RelT -> RelO -> RelS -> RelW -> RelA -> RelC.
Definition RuleTty := RelC -> RelT -> RelO -> RelS -> RelW -> RelA -> RelT.
Definition RuleOty := RelC -> RelT -> RelO -> RelS -> RelW -> RelA -> RelO.

(* The graph of a callback, from a suffix of c's code. *)
Definition GC (rc : FC) : RelC := fun c cv g top e d r r' => suffix c r /\ rc c cv g top e d r = Some r'.
Definition GT (rt : FT) : RelT := fun c cv g top e l r r' => suffix c r /\ rt c cv g top e r = Some (l, r').
Definition GO (ro : FO) : RelO := fun c cv g top e o top2 r r' => suffix c r /\ ro c cv g top e r = Some (o, top2, r').
Definition GS (rs : FS) : RelS := fun c cv g top es os r r' => suffix c r /\ rs c cv g top es r = Some (os, r').
Definition GW (rw : FW) : RelW := fun c cv g s es r r' => suffix c r /\ rw c cv g s es r = Some r'.
Definition GA (ra : FA) : RelA := fun c cv g s t es ms r r' => suffix c r /\ ra c cv g s t es ms r = Some r'.

(* Callbacks that, from a suffix of the code, end at a suffix. *)
Definition RecOK (rc : FC) (rt : FT) (ro : FO) (rs : FS) (rw : FW) (ra : FA) : Prop :=
 (forall c cv g top e d r r', rc c cv g top e d r = Some r' -> suffix c r -> suffix c r') /\
 (forall c cv g top e r l r', rt c cv g top e r = Some (l, r') -> suffix c r -> suffix c r') /\
 (forall c cv g top e r o top2 r', ro c cv g top e r = Some (o, top2, r') -> suffix c r -> suffix c r') /\
 (forall c cv g top es r os r', rs c cv g top es r = Some (os, r') -> suffix c r -> suffix c r') /\
 (forall c cv g s es r r', rw c cv g s es r = Some r' -> suffix c r -> suffix c r') /\
 (forall c cv g s t es ms r r', ra c cv g s t es ms r = Some r' -> suffix c r -> suffix c r').

(* A family hook's soundness, in graph form: what JitEmitRule<X>.v proves of its hooks. *)
Definition HookC_ok (RX : RuleCty) (h : HkC) : Prop := forall rc rt ro rs rw ra, RecOK rc rt ro rs rw ra ->
 forall c cv g top e d r r', h rc rt ro rs rw ra c cv g top e d r = Some r' -> suffix c r ->
 RX (GC rc) (GT rt) (GO ro) (GS rs) (GW rw) (GA ra) c cv g top e d r r' /\ suffix c r'.
Definition HookT_ok (RX : RuleTty) (h : HkT) : Prop := forall rc rt ro rs rw ra, RecOK rc rt ro rs rw ra ->
 forall c cv g top e r l r', h rc rt ro rs rw ra c cv g top e r = Some (l, r') -> suffix c r ->
 RX (GC rc) (GT rt) (GO ro) (GS rs) (GW rw) (GA ra) c cv g top e l r r' /\ suffix c r'.
Definition HookO_ok (RX : RuleOty) (h : HkO) : Prop := forall rc rt ro rs rw ra, RecOK rc rt ro rs rw ra ->
 forall c cv g top e r o top2 r', h rc rt ro rs rw ra c cv g top e r = Some (o, top2, r') -> suffix c r ->
 RX (GC rc) (GT rt) (GO ro) (GS rs) (GW rw) (GA ra) c cv g top e o top2 r r' /\ suffix c r'.

(* ---------- soundness against Comp ---------- *)
Definition SoundC (rc : FC) : Prop := forall c cv g top e d r r', rc c cv g top e d r = Some r' -> suffix c r ->
 Comp c cv g top e d r r' /\ suffix c r'.
Definition SoundT (rt : FT) : Prop := forall c cv g top e r l r', rt c cv g top e r = Some (l, r') -> suffix c r ->
 CompT c cv g top e l r r' /\ suffix c r'.
Definition SoundO (ro : FO) : Prop := forall c cv g top e r o top2 r', ro c cv g top e r = Some (o, top2, r') -> suffix c r ->
 CompOp c cv g top e o top2 r r' /\ suffix c r'.
Definition SoundS (rs : FS) : Prop := forall c cv g top es r os r', rs c cv g top es r = Some (os, r') -> suffix c r ->
 CompOps c cv g top es os r r' /\ suffix c r'.
Definition SoundW (rw : FW) : Prop := forall c cv g s es r r', rw c cv g s es r = Some r' -> suffix c r ->
 CompW c cv g s es r r' /\ suffix c r'.
Definition SoundA (ra : FA) : Prop := forall c cv g s t es ms r r', ra c cv g s t es ms r = Some r' -> suffix c r ->
 CompTA c cv g s t es ms r r' /\ suffix c r'.

(* A hook (or step) is sound whenever its callbacks are. *)
Definition LiftC (h : HkC) : Prop := forall rc rt ro rs rw ra, SoundC rc -> SoundT rt -> SoundO ro -> SoundS rs -> SoundW rw -> SoundA ra -> SoundC (h rc rt ro rs rw ra).
Definition LiftT (h : HkT) : Prop := forall rc rt ro rs rw ra, SoundC rc -> SoundT rt -> SoundO ro -> SoundS rs -> SoundW rw -> SoundA ra -> SoundT (h rc rt ro rs rw ra).
Definition LiftO (h : HkO) : Prop := forall rc rt ro rs rw ra, SoundC rc -> SoundT rt -> SoundO ro -> SoundS rs -> SoundW rw -> SoundA ra -> SoundO (h rc rt ro rs rw ra).
Definition LiftS (h : FC -> FT -> FO -> FS -> FW -> FA -> FS) : Prop := forall rc rt ro rs rw ra, SoundC rc -> SoundT rt -> SoundO ro -> SoundS rs -> SoundW rw -> SoundA ra -> SoundS (h rc rt ro rs rw ra).
Definition LiftW (h : FC -> FT -> FO -> FS -> FW -> FA -> FW) : Prop := forall rc rt ro rs rw ra, SoundC rc -> SoundT rt -> SoundO ro -> SoundS rs -> SoundW rw -> SoundA ra -> SoundW (h rc rt ro rs rw ra).
Definition LiftA (h : FC -> FT -> FO -> FS -> FW -> FA -> FA) : Prop := forall rc rt ro rs rw ra, SoundC rc -> SoundT rt -> SoundO ro -> SoundS rs -> SoundW rw -> SoundA ra -> SoundA (h rc rt ro rs rw ra).

Lemma sound_recok : forall rc rt ro rs rw ra, SoundC rc -> SoundT rt -> SoundO ro -> SoundS rs -> SoundW rw -> SoundA ra -> RecOK rc rt ro rs rw ra.
Proof.
 intros rc rt ro rs rw ra SC ST SO SS SW SA.
 repeat split; intros; [eapply SC|eapply ST|eapply SO|eapply SS|eapply SW|eapply SA]; eassumption.
Qed.

(* ---------- lifting a family's graph-form derivation to Comp ---------- *)
(* The family's map and all lemmas (JitEmitRule<X>.Rule_X_map, Rule_X_all), and Comp's hook
   constructor for the family, as hypotheses over the rule RX. *)
Definition MapC (RX : RuleCty) := forall (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA),
 subC PC QC -> subT PT QT -> subO PO QO -> subS PS QS -> subW PW QW -> subA PA QA ->
 forall c cv g top e d r r', RX PC PT PO PS PW PA c cv g top e d r r' -> RX QC QT QO QS QW QA c cv g top e d r r'.
Definition AllC (RX : RuleCty) := forall (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA),
 subC PC QC -> subT PT QT -> subO PO QO -> subS PS QS -> subW PW QW -> subA PA QA ->
 forall c cv g top e d r r', RX PC PT PO PS PW PA c cv g top e d r r' ->
 RX (andC PC QC) (andT PT QT) (andO PO QO) (andS PS QS) (andW PW QW) (andA PA QA) c cv g top e d r r'.
Definition InjC (RX : RuleCty) := forall c cv g top e d r r', RX Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' -> Comp c cv g top e d r r'.
Definition MapT (RX : RuleTty) := forall (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA),
 subC PC QC -> subT PT QT -> subO PO QO -> subS PS QS -> subW PW QW -> subA PA QA ->
 forall c cv g top e l r r', RX PC PT PO PS PW PA c cv g top e l r r' -> RX QC QT QO QS QW QA c cv g top e l r r'.
Definition AllT (RX : RuleTty) := forall (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA),
 subC PC QC -> subT PT QT -> subO PO QO -> subS PS QS -> subW PW QW -> subA PA QA ->
 forall c cv g top e l r r', RX PC PT PO PS PW PA c cv g top e l r r' ->
 RX (andC PC QC) (andT PT QT) (andO PO QO) (andS PS QS) (andW PW QW) (andA PA QA) c cv g top e l r r'.
Definition InjT (RX : RuleTty) := forall c cv g top e l r r', RX Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' -> CompT c cv g top e l r r'.
Definition MapO (RX : RuleOty) := forall (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA),
 subC PC QC -> subT PT QT -> subO PO QO -> subS PS QS -> subW PW QW -> subA PA QA ->
 forall c cv g top e o top2 r r', RX PC PT PO PS PW PA c cv g top e o top2 r r' -> RX QC QT QO QS QW QA c cv g top e o top2 r r'.
Definition AllO (RX : RuleOty) := forall (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA),
 subC PC QC -> subT PT QT -> subO PO QO -> subS PS QS -> subW PW QW -> subA PA QA ->
 forall c cv g top e o top2 r r', RX PC PT PO PS PW PA c cv g top e o top2 r r' ->
 RX (andC PC QC) (andT PT QT) (andO PO QO) (andS PS QS) (andW PW QW) (andA PA QA) c cv g top e o top2 r r'.
Definition InjO (RX : RuleOty) := forall c cv g top e o top2 r r', RX Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' -> CompOp c cv g top e o top2 r r'.

(* Each graph is included in the relation, given the callback's soundness; the relation "derivation
   and suffix after" is what Rule_X_all pairs with each nested premise. *)
Section Graphs.
Variables (rc : FC) (rt : FT) (ro : FO) (rs : FS) (rw : FW) (ra : FA).
Hypotheses (SC : SoundC rc) (ST : SoundT rt) (SO : SoundO ro) (SS : SoundS rs) (SW : SoundW rw) (SA : SoundA ra).
Definition QC : RelC := fun c cv g top e d r r' => Comp c cv g top e d r r' /\ suffix c r'.
Definition QT : RelT := fun c cv g top e l r r' => CompT c cv g top e l r r' /\ suffix c r'.
Definition QO : RelO := fun c cv g top e o top2 r r' => CompOp c cv g top e o top2 r r' /\ suffix c r'.
Definition QS : RelS := fun c cv g top es os r r' => CompOps c cv g top es os r r' /\ suffix c r'.
Definition QW : RelW := fun c cv g s es r r' => CompW c cv g s es r r' /\ suffix c r'.
Definition QA : RelA := fun c cv g s t es ms r r' => CompTA c cv g s t es ms r r' /\ suffix c r'.
Lemma gC : subC (GC rc) QC. Proof. intros * [S0 E]. exact (SC _ _ _ _ _ _ _ _ E S0). Qed.
Lemma gT : subT (GT rt) QT. Proof. intros * [S0 E]. exact (ST _ _ _ _ _ _ _ _ E S0). Qed.
Lemma gO : subO (GO ro) QO. Proof. intros * [S0 E]. exact (SO _ _ _ _ _ _ _ _ _ E S0). Qed.
Lemma gS : subS (GS rs) QS. Proof. intros * [S0 E]. exact (SS _ _ _ _ _ _ _ _ E S0). Qed.
Lemma gW : subW (GW rw) QW. Proof. intros * [S0 E]. exact (SW _ _ _ _ _ _ _ E S0). Qed.
Lemma gA : subA (GA ra) QA. Proof. intros * [S0 E]. exact (SA _ _ _ _ _ _ _ _ _ E S0). Qed.
End Graphs.
Lemma pC : forall (P : RelC), subC (andC P QC) Comp. Proof. intros P * [_ [H _]]. exact H. Qed.
Lemma pT : forall (P : RelT), subT (andT P QT) CompT. Proof. intros P * [_ [H _]]. exact H. Qed.
Lemma pO : forall (P : RelO), subO (andO P QO) CompOp. Proof. intros P * [_ [H _]]. exact H. Qed.
Lemma pS : forall (P : RelS), subS (andS P QS) CompOps. Proof. intros P * [_ [H _]]. exact H. Qed.
Lemma pW : forall (P : RelW), subW (andW P QW) CompW. Proof. intros P * [_ [H _]]. exact H. Qed.
Lemma pA : forall (P : RelA), subA (andA P QA) CompTA. Proof. intros P * [_ [H _]]. exact H. Qed.

Ltac lift_fam ok map all inj :=
 intros rc rt ro rs rw ra SC ST SO SS SW SA; intros * H S0;
 apply (ok rc rt ro rs rw ra (sound_recok _ _ _ _ _ _ SC ST SO SS SW SA)) in H; [|exact S0];
 destruct H as [D S1]; split; [|exact S1]; apply inj;
 apply (map (andC (GC rc) QC) Comp (andT (GT rt) QT) CompT (andO (GO ro) QO) CompOp
   (andS (GS rs) QS) CompOps (andW (GW rw) QW) CompW (andA (GA ra) QA) CompTA
   (pC _) (pT _) (pO _) (pS _) (pW _) (pA _));
 apply (all (GC rc) QC (GT rt) QT (GO ro) QO (GS rs) QS (GW rw) QW (GA ra) QA
   (gC _ SC) (gT _ ST) (gO _ SO) (gS _ SS) (gW _ SW) (gA _ SA));
 exact D.

Lemma lift_famC : forall RX (map : MapC RX) (all : AllC RX) (inj : InjC RX) h, HookC_ok RX h -> LiftC h.
Proof. intros RX map all inj h ok. unfold LiftC, SoundC. lift_fam ok map all inj. Qed.
Lemma lift_famT : forall RX (map : MapT RX) (all : AllT RX) (inj : InjT RX) h, HookT_ok RX h -> LiftT h.
Proof. intros RX map all inj h ok. unfold LiftT, SoundT. lift_fam ok map all inj. Qed.
Lemma lift_famO : forall RX (map : MapO RX) (all : AllO RX) (inj : InjO RX) h, HookO_ok RX h -> LiftO h.
Proof. intros RX map all inj h ok. unfold LiftO, SoundO. lift_fam ok map all inj. Qed.

(* ---------- one step of the checker: JitLowerCheck's six bodies over callbacks ---------- *)
Definition stepC (rc : FC) (rt : FT) (ro : FO) (rs : FS) (rw : FW) (ra : FA) (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (dst : dest) (r : list B.instr) : option (list B.instr) :=
 match e with
 | EType a => rc c cv g top a dst r
 | ELet x a b => match a with
   | EVar y => match lookup y g with
     | Some s => rc c cv ((x, s) :: g) top b dst r
     | None => match rc c cv g (top + 1) a (DSlot top) r with
       | Some r1 => rc c cv ((x, top) :: g) (top + 1) b dst r1 | None => None end end
   | _ => match rc c cv g (top + 1) a (DSlot top) r with
     | Some r1 => rc c cv ((x, top) :: g) (top + 1) b dst r1 | None => None end end
 | EIf t a b => match rt c cv g top t r with
   | None => None
   | Some (l, r1) => match dst with
     | DSlot d => match rc c cv g top a dst r1 with
       | Some (B.IJump e0 :: B.ILabel l' :: r3) =>
         if N.eqb l l' && lbl_ok c l r3 then match rc c cv g top b dst r3 with
           | Some (B.ILabel e0' :: r') => if N.eqb e0 e0' && lbl_ok c e0 r' then Some r' else None
           | _ => None end else None
       | _ => None end
     | DRet => match rc c cv g top a dst r1 with
       | Some (B.ILabel l' :: r3) => if N.eqb l l' && lbl_ok c l r3 then rc c cv g top b dst r3 else None
       | _ => None end end end
 | ECond [] => match dst, r with
   | DSlot d, B.IPrim d' q [] :: r' => if N.eqb d d' && q_eqb B.PRaiseCond q then Some r' else None
   | DRet, _ => match ro c cv g top e r with
     | Some (o, _, B.IReturn o' :: r') => if o_eqb o o' then Some r' else None | _ => None end
   | _, _ => None end
 | ECond ((EBool true, x) :: _) => rc c cv g top x dst r
 | ECond ((t, a) :: rest) => match rt c cv g top t r with
   | None => None
   | Some (l, r1) => match dst with
     | DSlot d => match rc c cv g top a dst r1 with
       | Some (B.IJump e0 :: B.ILabel l' :: r3) =>
         if N.eqb l l' && lbl_ok c l r3 then match rc c cv g top (ECond rest) dst r3 with
           | Some (B.ILabel e0' :: r') => if N.eqb e0 e0' && lbl_ok c e0 r' then Some r' else None
           | _ => None end else None
       | _ => None end
     | DRet => match rc c cv g top a dst r1 with
       | Some (B.ILabel l' :: r3) => if N.eqb l l' && lbl_ok c l r3 then rc c cv g top (ECond rest) dst r3 else None
       | _ => None end end end
 | ECall f args => match prim_of_name f with
   | Some p => match pmap p, dst with
     | Some q, DSlot d => match chain_head c d p args with
       | Some (v, e2) => match rc c cv g top e2 (DSlot d) r with
         | Some r1 => chain_tail c d v r1 | None => None end
       | None =>
       if Nat.eqb (List.length args) (prim_arity p) && negb (Nat.eqb (List.length args) 0) then
         match rs c cv g top args r with
         | Some (ops, B.IPrim d' q' ops' :: r') =>
           if N.eqb d d' && q_eqb q q' && os_eqb ops ops' && pguard c q ops then Some r' else None
         | _ => None end
       else None end
     | Some _, DRet => match ro c cv g top e r with
       | Some (o, _, B.IReturn o' :: r') => if o_eqb o o' then Some r' else None | _ => None end
     | None, _ => None end
   | None => let k := N.of_nat (List.length args) in match dst with
     | DSlot d => match rw c cv g (top + 2) args r with
       | Some (i :: r') => if is_call i d top (B.sym_of_text f) k then Some r' else None
       | _ => None end
     | DRet => let t := N.max top (k + 2) in match ra c cv g 2 t args [] r with
       | Some (i :: r') => if is_tailcall i (B.sym_of_text f) k then Some r' else None
       | _ => None end end end
 | _ => match dst with
   | DRet => match ro c cv g top e r with
     | Some (o, _, B.IReturn o' :: r') => if o_eqb o o' then Some r' else None | _ => None end
   | DSlot d => match e with
     | EVar x => match lookup x g with
       | Some s => if N.eqb s d then Some r else match r with
         | B.IMove d' s' :: r' => if N.eqb d d' && N.eqb s s' then Some r' else None | _ => None end
       | None => None end
     | EAnd x y => match rt c cv g top x r with
       | Some (l1, r1) => match rt c cv g top y r1 with
         | Some (l, B.IConst d1 kt :: B.IJump e0 :: B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r') =>
           if N.eqb l1 l && N.eqb d d1 && N.eqb d d2 && N.eqb l l' && N.eqb e0 e0' && is_bool (konst c kt) true
              && is_bool (konst c kf) false && lbl_ok c l (B.IConst d2 kf :: B.ILabel e0' :: r') && lbl_ok c e0 r'
           then Some r' else None
         | _ => None end
       | None => None end
     | EOr x y => match rt c cv g top x r with
       | Some (nx, B.IJump th :: B.ILabel nx' :: r2) =>
         if N.eqb nx nx' && lbl_ok c nx r2 then match rt c cv g top y r2 with
           | Some (l, B.ILabel th' :: B.IConst d1 kt :: B.IJump e0 :: B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r') =>
             if N.eqb th th' && N.eqb d d1 && N.eqb d d2 && N.eqb l l' && N.eqb e0 e0' && is_bool (konst c kt) true
                && is_bool (konst c kf) false && lbl_ok c th (B.IConst d1 kt :: B.IJump e0 :: B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r')
                && lbl_ok c l (B.IConst d2 kf :: B.ILabel e0' :: r') && lbl_ok c e0 r'
             then Some r' else None
           | _ => None end else None
       | _ => None end
     | _ => match lit_val e, r with
       | Some v, B.IConst d' k :: r' => match konst c k with
         | Some w => if N.eqb d d' && vrb v w then Some r' else None | None => None end
       | _, _ => None end end end end.

Definition stepT (rc : FC) (rt : FT) (ro : FO) (rs : FS) (rw : FW) (ra : FA) (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (r : list B.instr) : option (N * list B.instr) :=
 match e with
 | EType a => rt c cv g top a r
 | EAnd x y => match rt c cv g top x r with
   | Some (l1, r1) => match rt c cv g top y r1 with
     | Some (l2, r2) => if N.eqb l1 l2 then Some (l2, r2) else None | None => None end
   | None => None end
 | EOr x y => match rt c cv g top x r with
   | Some (nx, B.IJump th :: B.ILabel nx' :: r2) =>
     if N.eqb nx nx' && lbl_ok c nx r2 then match rt c cv g top y r2 with
       | Some (l, B.ILabel th' :: r') => if N.eqb th th' && lbl_ok c th r' then Some (l, r') else None
       | _ => None end else None
   | _ => None end
 | ELet x a b => match a with
   | EVar y => match lookup y g with
     | Some s => rt c cv ((x, s) :: g) top b r
     | None => match rc c cv g (top + 1) a (DSlot top) r with
       | Some r1 => rt c cv ((x, top) :: g) (top + 1) b r1 | None => None end end
   | _ => match rc c cv g (top + 1) a (DSlot top) r with
     | Some r1 => rt c cv ((x, top) :: g) (top + 1) b r1 | None => None end end
 | _ => match ro c cv g top e r with
   | Some (o, _, B.IJumpIfFalse o' l :: r') => if o_eqb o o' then Some (l, r') else None
   | _ => None end end.

Definition stepO (rc : FC) (rt : FT) (ro : FO) (rs : FS) (rw : FW) (ra : FA) (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (r : list B.instr) : option (B.operand * N * list B.instr) :=
 match e with
 | EType a => ro c cv g top a r
 | EVar x => match lookup x g with
   | Some s => if N.ltb s top then Some (B.OSlot s, top, r) else None
   | None => None end
 | _ => match lit_val e with
   | Some v => match find_k (B.code_consts c) v 0 with Some k => Some (B.OConst k, top, r) | None => None end
   | None => match rc c cv g (top + 1) e (DSlot top) r with
     | Some r1 => Some (B.OSlot top, top + 1, r1) | None => None end end end.

Definition stepS (rc : FC) (rt : FT) (ro : FO) (rs : FS) (rw : FW) (ra : FA) (c : B.code) (cv : list name) (g : env) (top : N) (es : list expr) (r : list B.instr) : option (list B.operand * list B.instr) :=
 match es with
 | [] => Some ([], r)
 | e :: es => match ro c cv g top e r with
   | Some (o, top2, r1) => match rs c cv g top2 es r1 with
     | Some (os, r') => Some (o :: os, r') | None => None end
   | None => None end end.

Definition stepW (rc : FC) (rt : FT) (ro : FO) (rs : FS) (rw : FW) (ra : FA) (c : B.code) (cv : list name) (g : env) (s : N) (es : list expr) (r : list B.instr) : option (list B.instr) :=
 match es with
 | [] => Some r
 | e :: es => match rc c cv g (s + 1) e (DSlot s) r with
   | Some r1 => rw c cv g (s + 1) es r1 | None => None end end.

Definition stepA (rc : FC) (rt : FT) (ro : FO) (rs : FS) (rw : FW) (ra : FA) (c : B.code) (cv : list name) (g : env) (s t : N) (es : list expr) (ms : list (N * N)) (r : list B.instr) : option (list B.instr) :=
 match es with
 | [] => moves_prefix ms r
 | e :: es =>
   let other (_ : unit) :=
     if reads g es s then match rc c cv g (t + 1) e (DSlot t) r with
       | Some r1 => ra c cv g (s + 1) (t + 1) es ((s, t) :: ms) r1 | None => None end
     else match rc c cv g t e (DSlot s) r with
       | Some r1 => ra c cv (kill s g) (s + 1) t es ms r1 | None => None end in
   match e with
   | EVar x => match lookup x g with
     | Some u => if N.eqb u s then ra c cv g (s + 1) t es ms r else other tt
     | None => other tt end
   | _ => other tt end end.

(* ---------- soundness of one step ---------- *)
Ltac sat_sfx := repeat match goal with
 | H : suffix ?c (_ :: ?r) |- _ => lazymatch goal with _ : suffix c r |- _ => fail | _ => pose proof (suffix_cons c _ _ H) end
 end.
Ltac dmE H := match type of H with
 | context [match ?x with _ => _ end] => let E := fresh "E" in destruct x eqn:E
 end.
Ltac cleanE := repeat match goal with
 | H : None = Some _ |- _ => discriminate H
 | H : Some _ = None |- _ => discriminate H
 | H : Some _ = Some _ |- _ => injection H; clear H; intros; subst
 | H : (_, _) = (_, _) |- _ => injection H; clear H; intros; subst
 | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H as [? ?]
 | H : N.eqb _ _ = true |- _ => apply N.eqb_eq in H; subst
 | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
 | H : N.ltb _ _ = true |- _ => apply N.ltb_lt in H
 | H : negb _ = true |- _ => apply negb_true_iff in H
 | H : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in H
 | H : o_eqb _ _ = true |- _ => apply o_eqb_eq in H; subst
 | H : os_eqb _ _ = true |- _ => apply os_eqb_eq in H; subst
 | H : q_eqb _ _ = true |- _ => apply q_eqb_eq in H; subst
 | H : false = true |- _ => discriminate H
 | H : N.eqb _ _ = false |- _ => apply N.eqb_neq in H
 end.
Ltac crushE H := cbn beta iota zeta delta [stepC stepT stepO stepS stepW stepA] in H;
 repeat (dmE H; cleanE; try discriminate); cleanE.
Ltac useE IC IT IO IS IW IA := repeat match goal with
 | H : _ = Some _, S : suffix _ _ |- _ =>
   first [ destruct (IC _ _ _ _ _ _ _ _ H S); clear H
         | destruct (IT _ _ _ _ _ _ _ _ H S); clear H
         | destruct (IO _ _ _ _ _ _ _ _ _ H S); clear H
         | destruct (IS _ _ _ _ _ _ _ _ H S); clear H
         | destruct (IW _ _ _ _ _ _ _ H S); clear H
         | destruct (IA _ _ _ _ _ _ _ _ _ H S); clear H ]
 | H : lbl_ok ?c ?l ?r = true, S : suffix ?c ?r |- _ => apply (lbl_ok_sound c l r H) in S; clear H
 | H : is_bool _ _ = true |- _ => apply is_bool_eq in H
 | H : vrb _ _ = true |- _ => apply vrb_sound in H
 | H : is_call _ _ _ _ _ = true |- _ => apply is_call_ok in H
 | H : is_tailcall _ _ _ = true |- _ => apply is_tailcall_ok in H
 | H : moves_prefix _ _ = Some _ |- _ => apply moves_prefix_ok in H
 | H : chain_tail ?c _ _ _ = Some _ |- _ =>
     let k := fresh "k" in let w := fresh "w" in let A := fresh in let K := fresh in let V := fresh in
     destruct (chain_tail_ok c _ _ _ _ H) as (k & w & A & K & V); clear H; subst
 | H : chain_head ?c _ _ _ = Some (_, _) |- _ =>
     let P := fresh in let a := fresh "a" in let A := fresh in let L := fresh in
     destruct (chain_head_ok c _ _ _ _ _ H) as (P & a & A & L); clear H; subst
 | _ => progress sat_sfx
 end.

Section Step.
Variables (rc : FC) (rt : FT) (ro : FO) (rs : FS) (rw : FW) (ra : FA).
Hypotheses (IC : SoundC rc) (IT : SoundT rt) (IO : SoundO ro) (IS : SoundS rs) (IW : SoundW rw) (IA : SoundA ra).

Lemma stepC_sound : SoundC (stepC rc rt ro rs rw ra).
Proof.
 intros c cv g top e dst r r' H S. destruct e; crushE H; useE IC IT IO IS IW IA.
 all: try (split; [econstructor; eauto|eauto]; fail).
 all: try (split; [eapply C_tail; eauto; lia|eauto]; fail).
 all: try (split; [eapply C_chain; eauto|eauto]; fail).
 all: split; [|assumption]; eapply C_prim; eauto; intro Ea; subst; cbn in *; congruence.
Qed.
Lemma stepT_sound : SoundT (stepT rc rt ro rs rw ra).
Proof.
 intros c cv g top e r l r' H S. destruct e; crushE H; useE IC IT IO IS IW IA.
 all: try (split; [econstructor; eauto|eauto]; fail).
 all: try (split; [eapply T_leaf; eauto|eauto]; fail).
Qed.
Lemma stepO_sound : SoundO (stepO rc rt ro rs rw ra).
Proof.
 intros c cv g top e r o top2 r' H S. destruct e; crushE H; useE IC IT IO IS IW IA.
 all: try (split; [econstructor; eauto|eauto]; fail).
 all: match goal with F : find_k _ _ 0 = Some _ |- _ =>
   destruct (find_k_sound _ _ _ _ F) as (w & W1 & W2 & W3); rewrite Nat.sub_0_r in W1;
   split; [eapply O_lit; [eassumption|exact W1|exact W2]|assumption] end.
Qed.
Lemma stepS_sound : SoundS (stepS rc rt ro rs rw ra).
Proof.
 intros c cv g top es r os r' H S. destruct es; crushE H; useE IC IT IO IS IW IA.
 all: try (split; [econstructor; eauto|eauto]; fail).
Qed.
Lemma stepW_sound : SoundW (stepW rc rt ro rs rw ra).
Proof.
 intros c cv g s es r r' H S. destruct es; crushE H; useE IC IT IO IS IW IA.
 all: try (split; [econstructor; eauto|eauto]; fail).
Qed.
Lemma stepA_sound : SoundA (stepA rc rt ro rs rw ra).
Proof.
 intros c cv g s t es ms r r' H S. destruct es; crushE H; useE IC IT IO IS IW IA.
 all: try (split; [econstructor; eauto|eauto]; fail).
 all: try (split; [eapply TA_same; eauto|eauto]; fail).
 all: try (split; [eapply TA_temp; eauto|eauto]; fail).
 all: try (split; [eapply TA_direct; eauto|eauto]; fail).
 all: match goal with M : ?r = map _ ?ms ++ ?r' |- _ =>
   subst r; split; [constructor|destruct S as [p0 Hp]; exists (p0 ++ map (fun m => B.IMove (fst m) (snd m)) ms); rewrite Hp, <- app_assoc; reflexivity] end.
Qed.
End Step.

Lemma stepC_lift : LiftC stepC. Proof. intros ? ? ? ? ? ? ? ? ? ? ? ?. apply stepC_sound; assumption. Qed.
Lemma stepT_lift : LiftT stepT. Proof. intros ? ? ? ? ? ? ? ? ? ? ? ?. apply stepT_sound; assumption. Qed.
Lemma stepO_lift : LiftO stepO. Proof. intros ? ? ? ? ? ? ? ? ? ? ? ?. apply stepO_sound; assumption. Qed.
Lemma stepS_lift : LiftS stepS. Proof. intros ? ? ? ? ? ? ? ? ? ? ? ?. apply stepS_sound; assumption. Qed.
Lemma stepW_lift : LiftW stepW. Proof. intros ? ? ? ? ? ? ? ? ? ? ? ?. apply stepW_sound; assumption. Qed.
Lemma stepA_lift : LiftA stepA. Proof. intros ? ? ? ? ? ? ? ? ? ? ? ?. apply stepA_sound; assumption. Qed.

(* ---------- falling back to a hook ---------- *)
(* The hook is a thunk, so vm_compute does not run it when the step has already accepted. *)
Definition orelse {A} (a : option A) (b : unit -> option A) : option A := match a with Some x => Some x | None => b tt end.
Definition orC (h1 h2 : HkC) : HkC := fun rc rt ro rs rw ra c cv g top e d r =>
 orelse (h1 rc rt ro rs rw ra c cv g top e d r) (fun _ => h2 rc rt ro rs rw ra c cv g top e d r).
Definition orT (h1 h2 : HkT) : HkT := fun rc rt ro rs rw ra c cv g top e r =>
 orelse (h1 rc rt ro rs rw ra c cv g top e r) (fun _ => h2 rc rt ro rs rw ra c cv g top e r).
Definition orO (h1 h2 : HkO) : HkO := fun rc rt ro rs rw ra c cv g top e r =>
 orelse (h1 rc rt ro rs rw ra c cv g top e r) (fun _ => h2 rc rt ro rs rw ra c cv g top e r).
Ltac lift_or H1 H2 := intros rc rt ro rs rw ra SC ST SO SS SW SA; unfold SoundC, SoundT, SoundO; intros * H S0;
 unfold orC, orT, orO, orelse in H;
 match type of H with context [match ?x with _ => _ end] => destruct x eqn:E end;
 [injection H; intros; subst; eapply (H1 rc rt ro rs rw ra SC ST SO SS SW SA); eassumption
 |eapply (H2 rc rt ro rs rw ra SC ST SO SS SW SA); eassumption].
Lemma lift_orC : forall h1 h2, LiftC h1 -> LiftC h2 -> LiftC (orC h1 h2).
Proof. intros h1 h2 H1 H2. lift_or H1 H2. Qed.
Lemma lift_orT : forall h1 h2, LiftT h1 -> LiftT h2 -> LiftT (orT h1 h2).
Proof. intros h1 h2 H1 H2. lift_or H1 H2. Qed.
Lemma lift_orO : forall h1 h2, LiftO h1 -> LiftO h2 -> LiftO (orO h1 h2).
Proof. intros h1 h2 H1 H2. lift_or H1 H2. Qed.

(* The empty hook: every family's, until the family adds rules. *)
Definition noneC : HkC := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => None.
Definition noneT : HkT := fun _ _ _ _ _ _ _ _ _ _ _ _ => None.
Definition noneO : HkO := fun _ _ _ _ _ _ _ _ _ _ _ _ => None.
Lemma none_okC : forall RX, HookC_ok RX noneC. Proof. unfold HookC_ok, noneC. intros. discriminate. Qed.
Lemma none_okT : forall RX, HookT_ok RX noneT. Proof. unfold HookT_ok, noneT. intros. discriminate. Qed.
Lemma none_okO : forall RX, HookO_ok RX noneO. Proof. unfold HookO_ok, noneO. intros. discriminate. Qed.

(* ---------- the checker, and its soundness under hook hypotheses ---------- *)
Section Chk.
Variables (hC : HkC) (hT : HkT) (hO : HkO).

(* Every function takes all its arguments before matching on the fuel, as JitLowerCheck's do:
   vm_compute then never evaluates a partial application chk n, which would build the closures
   for every fuel level below n eagerly. *)
Fixpoint chk (n : nat) (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (d : dest) (r : list B.instr) {struct n} : option (list B.instr) :=
 match n with O => None | S n => orC stepC hC (chk n) (chkT n) (chkOp n) (chkOps n) (chkW n) (chkTA n) c cv g top e d r end
with chkT (n : nat) (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (r : list B.instr) {struct n} : option (N * list B.instr) :=
 match n with O => None | S n => orT stepT hT (chk n) (chkT n) (chkOp n) (chkOps n) (chkW n) (chkTA n) c cv g top e r end
with chkOp (n : nat) (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (r : list B.instr) {struct n} : option (B.operand * N * list B.instr) :=
 match n with O => None | S n => orO stepO hO (chk n) (chkT n) (chkOp n) (chkOps n) (chkW n) (chkTA n) c cv g top e r end
with chkOps (n : nat) (c : B.code) (cv : list name) (g : env) (top : N) (es : list expr) (r : list B.instr) {struct n} : option (list B.operand * list B.instr) :=
 match n with O => None | S n => stepS (chk n) (chkT n) (chkOp n) (chkOps n) (chkW n) (chkTA n) c cv g top es r end
with chkW (n : nat) (c : B.code) (cv : list name) (g : env) (s : N) (es : list expr) (r : list B.instr) {struct n} : option (list B.instr) :=
 match n with O => None | S n => stepW (chk n) (chkT n) (chkOp n) (chkOps n) (chkW n) (chkTA n) c cv g s es r end
with chkTA (n : nat) (c : B.code) (cv : list name) (g : env) (s t : N) (es : list expr) (ms : list (N * N)) (r : list B.instr) {struct n} : option (list B.instr) :=
 match n with O => None | S n => stepA (chk n) (chkT n) (chkOp n) (chkOps n) (chkW n) (chkTA n) c cv g s t es ms r end.

Hypotheses (LC : LiftC hC) (LT : LiftT hT) (LO : LiftO hO).

Theorem chk_sound : forall n, SoundC (chk n) /\ SoundT (chkT n) /\ SoundO (chkOp n) /\
 SoundS (chkOps n) /\ SoundW (chkW n) /\ SoundA (chkTA n).
Proof.
 induction n as [|n (IC & IT & IO & IS & IW & IA)].
 - unfold SoundC, SoundT, SoundO, SoundS, SoundW, SoundA. cbn. repeat split; intros; discriminate.
 - refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
   + exact (lift_orC _ _ stepC_lift LC _ _ _ _ _ _ IC IT IO IS IW IA).
   + exact (lift_orT _ _ stepT_lift LT _ _ _ _ _ _ IC IT IO IS IW IA).
   + exact (lift_orO _ _ stepO_lift LO _ _ _ _ _ _ IC IT IO IS IW IA).
   + exact (stepS_lift _ _ _ _ _ _ IC IT IO IS IW IA).
   + exact (stepW_lift _ _ _ _ _ _ IC IT IO IS IW IA).
   + exact (stepA_lift _ _ _ _ _ _ IC IT IO IS IW IA).
Qed.

(* A top-level function: its body at the code's start, with the parameters in slots 2 up and no
   captures. Fuel as JitLowerCheck's. *)
Definition check_emit_gen (c : B.code) (ps : list name) (b : expr) : bool :=
 match chk JitLowerCheck.fuel c [] (bind ps 2) (2 + N.of_nat (List.length ps)) b DRet (B.code_ins c) with
 | Some _ => true | None => false end.

Lemma chk_fn_sound : forall n c ps b,
 match chk n c [] (bind ps 2) (2 + N.of_nat (List.length ps)) b DRet (B.code_ins c) with Some _ => true | None => false end = true ->
 CompFn' c ps b.
Proof.
 intros n c ps b H.
 destruct (chk n c [] (bind ps 2) (2 + N.of_nat (List.length ps)) b DRet (B.code_ins c)) as [r'|] eqn:E; [|discriminate].
 exists r'. refine (proj1 (proj1 (chk_sound n) _ _ _ _ _ _ _ _ E _)). exists []. reflexivity.
Qed.

(* The fuel is generalized, as in JitLowerCheck, so that no conversion unfolds it. *)
Theorem check_emit_gen_sound : forall c ps b, check_emit_gen c ps b = true -> CompFn' c ps b.
Proof. intros c ps b. unfold check_emit_gen. generalize JitLowerCheck.fuel. intro n. apply chk_fn_sound. Qed.
End Chk.

(* ---------- the seven families ---------- *)
(* A family's hooks with their graph-form soundness, for its rules RC, RT, RO. *)
Record Fam (RC : RuleCty) (RT : RuleTty) (RO : RuleOty) := mkFam {
 fC : HkC; fT : HkT; fO : HkO;
 fC_ok : HookC_ok RC fC; fT_ok : HookT_ok RT fT; fO_ok : HookO_ok RO fO }.
Arguments fC {RC RT RO}. Arguments fT {RC RT RO}. Arguments fO {RC RT RO}.
Arguments fC_ok {RC RT RO}. Arguments fT_ok {RC RT RO}. Arguments fO_ok {RC RT RO}.
Definition fam_none RC RT RO : Fam RC RT RO := mkFam RC RT RO noneC noneT noneO (none_okC RC) (none_okT RT) (none_okO RO).

Record Hooks := mkHooks {
 kEq : Fam JitEmitRuleEq.Rule_Eq JitEmitRuleEq.RuleT_Eq JitEmitRuleEq.RuleO_Eq;
 kStore : Fam JitEmitRuleStore.Rule_Store JitEmitRuleStore.RuleT_Store JitEmitRuleStore.RuleO_Store;
 kPrim : Fam JitEmitRulePrim.Rule_Prim JitEmitRulePrim.RuleT_Prim JitEmitRulePrim.RuleO_Prim;
 kDoFold : Fam JitEmitRuleDoFold.Rule_DoFold JitEmitRuleDoFold.RuleT_DoFold JitEmitRuleDoFold.RuleO_DoFold;
 kClo : Fam JitEmitRuleClo.Rule_Clo JitEmitRuleClo.RuleT_Clo JitEmitRuleClo.RuleO_Clo;
 kApp : Fam JitEmitRuleApp.Rule_App JitEmitRuleApp.RuleT_App JitEmitRuleApp.RuleO_App;
 kTrap : Fam JitEmitRuleTrap.Rule_Trap JitEmitRuleTrap.RuleT_Trap JitEmitRuleTrap.RuleO_Trap }.

(* Each family's lift: its Rule_X_map and Rule_X_all, and Comp's hook for X (JitEmitRel.inj_X). *)
Definition liftC_Eq : forall h, HookC_ok JitEmitRuleEq.Rule_Eq h -> LiftC h := lift_famC _ JitEmitRuleEq.Rule_Eq_map JitEmitRuleEq.Rule_Eq_all inj_C_Eq.
Definition liftT_Eq : forall h, HookT_ok JitEmitRuleEq.RuleT_Eq h -> LiftT h := lift_famT _ JitEmitRuleEq.RuleT_Eq_map JitEmitRuleEq.RuleT_Eq_all inj_T_Eq.
Definition liftO_Eq : forall h, HookO_ok JitEmitRuleEq.RuleO_Eq h -> LiftO h := lift_famO _ JitEmitRuleEq.RuleO_Eq_map JitEmitRuleEq.RuleO_Eq_all inj_O_Eq.
Definition liftC_Store : forall h, HookC_ok JitEmitRuleStore.Rule_Store h -> LiftC h := lift_famC _ JitEmitRuleStore.Rule_Store_map JitEmitRuleStore.Rule_Store_all inj_C_Store.
Definition liftT_Store : forall h, HookT_ok JitEmitRuleStore.RuleT_Store h -> LiftT h := lift_famT _ JitEmitRuleStore.RuleT_Store_map JitEmitRuleStore.RuleT_Store_all inj_T_Store.
Definition liftO_Store : forall h, HookO_ok JitEmitRuleStore.RuleO_Store h -> LiftO h := lift_famO _ JitEmitRuleStore.RuleO_Store_map JitEmitRuleStore.RuleO_Store_all inj_O_Store.
Definition liftC_Prim : forall h, HookC_ok JitEmitRulePrim.Rule_Prim h -> LiftC h := lift_famC _ JitEmitRulePrim.Rule_Prim_map JitEmitRulePrim.Rule_Prim_all inj_C_Prim.
Definition liftT_Prim : forall h, HookT_ok JitEmitRulePrim.RuleT_Prim h -> LiftT h := lift_famT _ JitEmitRulePrim.RuleT_Prim_map JitEmitRulePrim.RuleT_Prim_all inj_T_Prim.
Definition liftO_Prim : forall h, HookO_ok JitEmitRulePrim.RuleO_Prim h -> LiftO h := lift_famO _ JitEmitRulePrim.RuleO_Prim_map JitEmitRulePrim.RuleO_Prim_all inj_O_Prim.
Definition liftC_DoFold : forall h, HookC_ok JitEmitRuleDoFold.Rule_DoFold h -> LiftC h := lift_famC _ JitEmitRuleDoFold.Rule_DoFold_map JitEmitRuleDoFold.Rule_DoFold_all inj_C_DoFold.
Definition liftT_DoFold : forall h, HookT_ok JitEmitRuleDoFold.RuleT_DoFold h -> LiftT h := lift_famT _ JitEmitRuleDoFold.RuleT_DoFold_map JitEmitRuleDoFold.RuleT_DoFold_all inj_T_DoFold.
Definition liftO_DoFold : forall h, HookO_ok JitEmitRuleDoFold.RuleO_DoFold h -> LiftO h := lift_famO _ JitEmitRuleDoFold.RuleO_DoFold_map JitEmitRuleDoFold.RuleO_DoFold_all inj_O_DoFold.
Definition liftC_Clo : forall h, HookC_ok JitEmitRuleClo.Rule_Clo h -> LiftC h := lift_famC _ JitEmitRuleClo.Rule_Clo_map JitEmitRuleClo.Rule_Clo_all inj_C_Clo.
Definition liftT_Clo : forall h, HookT_ok JitEmitRuleClo.RuleT_Clo h -> LiftT h := lift_famT _ JitEmitRuleClo.RuleT_Clo_map JitEmitRuleClo.RuleT_Clo_all inj_T_Clo.
Definition liftO_Clo : forall h, HookO_ok JitEmitRuleClo.RuleO_Clo h -> LiftO h := lift_famO _ JitEmitRuleClo.RuleO_Clo_map JitEmitRuleClo.RuleO_Clo_all inj_O_Clo.
Definition liftC_App : forall h, HookC_ok JitEmitRuleApp.Rule_App h -> LiftC h := lift_famC _ JitEmitRuleApp.Rule_App_map JitEmitRuleApp.Rule_App_all inj_C_App.
Definition liftT_App : forall h, HookT_ok JitEmitRuleApp.RuleT_App h -> LiftT h := lift_famT _ JitEmitRuleApp.RuleT_App_map JitEmitRuleApp.RuleT_App_all inj_T_App.
Definition liftO_App : forall h, HookO_ok JitEmitRuleApp.RuleO_App h -> LiftO h := lift_famO _ JitEmitRuleApp.RuleO_App_map JitEmitRuleApp.RuleO_App_all inj_O_App.
Definition liftC_Trap : forall h, HookC_ok JitEmitRuleTrap.Rule_Trap h -> LiftC h := lift_famC _ JitEmitRuleTrap.Rule_Trap_map JitEmitRuleTrap.Rule_Trap_all inj_C_Trap.
Definition liftT_Trap : forall h, HookT_ok JitEmitRuleTrap.RuleT_Trap h -> LiftT h := lift_famT _ JitEmitRuleTrap.RuleT_Trap_map JitEmitRuleTrap.RuleT_Trap_all inj_T_Trap.
Definition liftO_Trap : forall h, HookO_ok JitEmitRuleTrap.RuleO_Trap h -> LiftO h := lift_famO _ JitEmitRuleTrap.RuleO_Trap_map JitEmitRuleTrap.RuleO_Trap_all inj_O_Trap.
Definition hooksC (H : Hooks) : HkC := orC (fC (kEq H)) (orC (fC (kStore H)) (orC (fC (kPrim H)) (orC (fC (kDoFold H)) (orC (fC (kClo H)) (orC (fC (kApp H)) (fC (kTrap H))))))).
Definition hooksT (H : Hooks) : HkT := orT (fT (kEq H)) (orT (fT (kStore H)) (orT (fT (kPrim H)) (orT (fT (kDoFold H)) (orT (fT (kClo H)) (orT (fT (kApp H)) (fT (kTrap H))))))).
Definition hooksO (H : Hooks) : HkO := orO (fO (kEq H)) (orO (fO (kStore H)) (orO (fO (kPrim H)) (orO (fO (kDoFold H)) (orO (fO (kClo H)) (orO (fO (kApp H)) (fO (kTrap H))))))).
Lemma hooksC_lift : forall H, LiftC (hooksC H).
Proof. intro H. unfold hooksC.
 apply lift_orC; [exact (liftC_Eq _ (fC_ok (kEq H)))|].
 apply lift_orC; [exact (liftC_Store _ (fC_ok (kStore H)))|].
 apply lift_orC; [exact (liftC_Prim _ (fC_ok (kPrim H)))|].
 apply lift_orC; [exact (liftC_DoFold _ (fC_ok (kDoFold H)))|].
 apply lift_orC; [exact (liftC_Clo _ (fC_ok (kClo H)))|].
 apply lift_orC; [exact (liftC_App _ (fC_ok (kApp H)))|].
 exact (liftC_Trap _ (fC_ok (kTrap H))).
Qed.
Lemma hooksT_lift : forall H, LiftT (hooksT H).
Proof. intro H. unfold hooksT.
 apply lift_orT; [exact (liftT_Eq _ (fT_ok (kEq H)))|].
 apply lift_orT; [exact (liftT_Store _ (fT_ok (kStore H)))|].
 apply lift_orT; [exact (liftT_Prim _ (fT_ok (kPrim H)))|].
 apply lift_orT; [exact (liftT_DoFold _ (fT_ok (kDoFold H)))|].
 apply lift_orT; [exact (liftT_Clo _ (fT_ok (kClo H)))|].
 apply lift_orT; [exact (liftT_App _ (fT_ok (kApp H)))|].
 exact (liftT_Trap _ (fT_ok (kTrap H))).
Qed.
Lemma hooksO_lift : forall H, LiftO (hooksO H).
Proof. intro H. unfold hooksO.
 apply lift_orO; [exact (liftO_Eq _ (fO_ok (kEq H)))|].
 apply lift_orO; [exact (liftO_Store _ (fO_ok (kStore H)))|].
 apply lift_orO; [exact (liftO_Prim _ (fO_ok (kPrim H)))|].
 apply lift_orO; [exact (liftO_DoFold _ (fO_ok (kDoFold H)))|].
 apply lift_orO; [exact (liftO_Clo _ (fO_ok (kClo H)))|].
 apply lift_orO; [exact (liftO_App _ (fO_ok (kApp H)))|].
 exact (liftO_Trap _ (fO_ok (kTrap H))).
Qed.

Definition check_emit_with (H : Hooks) : B.code -> list name -> expr -> bool :=
 check_emit_gen (hooksC H) (hooksT H) (hooksO H).
(* Acceptance with any hooks is a proof of CompFn': the Section's hypotheses instantiated. *)
Theorem check_emit_sound_hooks : forall H c ps b, check_emit_with H c ps b = true -> CompFn' c ps b.
Proof. intro H. exact (check_emit_gen_sound _ _ _ (hooksC_lift H) (hooksT_lift H) (hooksO_lift H)). Qed.

(* The base hooks: every family empty. A hook module for tests/shen-jit/judge_hooks.sh defines
   `hooks : JitEmitCheck.Hooks`; this one is the base. *)
Definition base_hooks : Hooks := mkHooks(fam_none _ _ _) (fam_none _ _ _) (fam_none _ _ _) (fam_none _ _ _) (fam_none _ _ _) (fam_none _ _ _) (fam_none _ _ _).
Definition hooks : Hooks := base_hooks.
Definition check_emit : B.code -> list name -> expr -> bool := check_emit_with base_hooks.
Theorem check_emit_sound : forall c ps b, check_emit c ps b = true -> CompFn' c ps b.
Proof. exact (check_emit_sound_hooks base_hooks). Qed.

(* ---------- the stage 0 judge over hooks ---------- *)
Import JitLowerStage0.JitLowerStage0.
(* JitLowerStage0.judge, with check_emit_with H for check_fn. *)
Definition judge_emit (H : Hooks) (form sbc : sx) : verdict :=
 match parse [] (to_value form), to_val sbc with
 | Some (EDefun f ps b), B.VPair (B.VSym _) (B.VPair (B.VSym g) (B.VPair code B.VNil)) =>
   if negb (Pos.eqb (B.sym_of_text f) g) then Unparsed else
   match B.build_code B.prim_tree 64 code with
   | B.LOk c =>
     if (N.eqb (B.code_arity c) (N.of_nat (List.length ps))
         && match B.code_entry c with None => true | Some _ => false end
         && check_emit_with H c ps b)%bool
     then Accepted f else Rejected f
   | B.LErr _ => Rejected f end
 | _, _ => Unparsed end.

Fixpoint judge_emit_all (H : Hooks) (fs ss : list sx) : list verdict := match fs, ss with
 | f :: fs, s :: ss => judge_emit H f s :: judge_emit_all H fs ss
 | [], [] => []
 | _, _ => [Unparsed] end.

Definition tally_emit (H : Hooks) (fs ss : list sx) : nat * nat * nat * list name :=
 fold_right (fun v acc => let '(a, r, u, names) := acc in match v with
   | Accepted f => (S a, r, u, f :: names)
   | Rejected _ => (a, S r, u, names)
   | Unparsed => (a, r, S u, names) end) (0, 0, 0, [])%nat (judge_emit_all H fs ss).

(* Per-definition verdict codes, in file order: 1 accepted, 2 rejected, 0 unreadable. *)
Definition vcode (v : verdict) : nat := match v with Accepted _ => 1 | Rejected _ => 2 | Unparsed => 0 end%nat.

(* An accepted definition is read from the form, its code object built from the .sbc tree, and the
   code is a lowering of the body in JitEmitRel's sense, with the arity and no entry prefix. *)
Theorem judge_emit_sound : forall H form sbc f, judge_emit H form sbc = Accepted f ->
 exists ps b code c, parse [] (to_value form) = Some (EDefun f ps b) /\
   B.build_code B.prim_tree 64 code = B.LOk c /\ B.code_arity c = N.of_nat (List.length ps) /\
   B.code_entry c = None /\ CompFn' c ps b.
Proof.
 intros H form sbc f J. unfold judge_emit in J.
 repeat (dmE J; try discriminate).
 injection J as <-. subst.
 repeat match goal with A : (_ && _)%bool = true |- _ => apply andb_true_iff in A as [? ?] end.
 match goal with C : check_emit_with _ _ _ _ = true |- _ => pose proof (check_emit_sound_hooks _ _ _ _ C) end.
 do 4 eexists. split; [first [eassumption|reflexivity]|]. split; [eassumption|]. split; [apply N.eqb_eq; eassumption|].
 split; [|eassumption].
 match goal with E : (match B.code_entry ?c with Some _ => false | None => true end) = true |- _ =>
   destruct (B.code_entry c); [discriminate|reflexivity] end.
Qed.
End JitEmitCheck.
