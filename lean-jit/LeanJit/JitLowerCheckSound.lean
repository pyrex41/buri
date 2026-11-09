import LeanJit.JitLowerCheck
import Lean.Elab.Tactic
/-! Port of `rocq/JitLowerCheck.v`, the soundness half: acceptance is a proof of `CompFn`.
Rocq's proof is Ltac (`crush`, `use`: `match goal` loops). Lean core has no `match goal`, so
`use_all` below is a small tactic written in Lean's meta language doing the same job. -/
namespace JitLowerCheck
open KLSyntax KLSyntax.prim KLSyntax.expr KLValue KLValue.value JitLowerRel JitLowerRel.dest
open JitBytecode (Pos)
open Lean Elab Tactic Meta

-- ---------- the decisions are sound ----------
theorem vrb_sound (v : value) (w : JitBytecode.val) (H : vrb v w = true) : VR v w := by
  cases v with
  | VNum n => cases n <;> cases w <;> simp [vrb] at H <;> (subst H; constructor)
  | VSym s =>
    cases w <;> simp only [vrb, reduceCtorEq] at H
    simp only [JitBytecode.Pos.eqb, beq_iff_eq] at H
    rename_i p; obtain ⟨pp⟩ := p; simp only at H; subst H
    exact .VR_sym s
  | VBool b => cases w <;> simp [vrb] at H; subst H; constructor
  | VStr t =>
    cases w <;> simp only [vrb, reduceCtorEq, Bool.and_eq_true] at H
    rw [(text_eqb_eq _ _).1 H.1]; constructor
  | VNil => cases w <;> simp [vrb] at H; constructor
  | VCons a d =>
    cases w <;> simp only [vrb, reduceCtorEq, Bool.and_eq_true] at H
    exact .VR_cons _ _ _ _ (vrb_sound a _ H.1) (vrb_sound d _ H.2)
  | _ => simp [vrb] at H

theorem find_k_sound : ∀ (cs : List JitBytecode.val) (v : value) (i k : Nat), find_k cs v i = some k →
    ∃ w, cs[k - i]? = some w ∧ VR v w ∧ i ≤ k
  | [], _, _, _, H => by simp [find_k] at H
  | w :: cs, v, i, k, H => by
    simp only [find_k] at H
    split at H
    · cases H; exact ⟨w, by simp, vrb_sound _ _ ‹_›, Nat.le_refl _⟩
    · obtain ⟨w', A, Bv, L⟩ := find_k_sound cs v (i + 1) k H
      refine ⟨w', ?_, Bv, by omega⟩
      have : k - i = (k - (i + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ]; exact A

theorem o_eqb_eq {a b : JitBytecode.operand} (H : o_eqb a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [o_eqb]
theorem os_eqb_eq : ∀ {a b : List JitBytecode.operand}, os_eqb a b = true → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, H => by
    simp only [os_eqb, Bool.and_eq_true] at H; rw [o_eqb_eq H.1, os_eqb_eq H.2]
  | [], _ :: _, H | _ :: _, [], H => by simp [os_eqb] at H
theorem q_eqb_eq {a b : JitBytecode.prim} (H : q_eqb a b = true) : a = b := by
  unfold q_eqb at H; split at H <;> first | rfl | (simp at H)
theorem is_bool_eq {w : Option JitBytecode.val} {b : Bool} (H : is_bool w b = true) : w = some (.VBool b) := by
  match w, H with
  | some (.VBool c), H => simp [is_bool] at H; subst H; rfl
theorem is_tailcall_ok {i : JitBytecode.instr} {f : Pos} {n : Nat} (H : is_tailcall i f n = true) :
    tail_instr i 0 f n := by
  cases i <;> simp [is_tailcall, JitBytecode.Pos.eqb] at H <;>
    (obtain ⟨⟨A, B⟩, C⟩ := H; subst A C; cases f; cases ‹Pos›; simp_all [tail_instr])
theorem is_call_ok {i : JitBytecode.instr} {d a : Nat} {f : Pos} {n : Nat} (H : is_call i d a f n = true) :
    call_instr i d a f n := by
  cases i <;> simp [is_call, JitBytecode.Pos.eqb] at H <;>
    (obtain ⟨⟨⟨A, B⟩, C⟩, D⟩ := H; subst A B D; cases f; cases ‹Pos›; simp_all [call_instr])
theorem moves_prefix_ok : ∀ {ms : List (Nat × Nat)} {r r' : List JitBytecode.instr},
    moves_prefix ms r = some r' → r = ms.map (fun m => JitBytecode.instr.IMove m.1 m.2) ++ r'
  | [], r, r', H => by simp [moves_prefix] at H; simp [H]
  | (s, t) :: ms, r, r', H => by
    match r, H with
    | .IMove d u :: r, H =>
      simp only [moves_prefix] at H
      split at H
      · simp only [Bool.and_eq_true, beq_iff_eq] at *; obtain ⟨A, B⟩ := ‹_ ∧ _›; subst A B
        simp [moves_prefix_ok H]
      · simp at H

section Sound
variable (c : JitBytecode.code)

def suffix (r : List JitBytecode.instr) : Prop := ∃ p, ins c = p ++ r
variable {c}
theorem suffix_tail {x : JitBytecode.instr} {r : List JitBytecode.instr} (H : suffix c (x :: r)) : suffix c r := by
  obtain ⟨p, H⟩ := H; exact ⟨p ++ [x], by simp [H]⟩
theorem suffix_app {l r : List JitBytecode.instr} (H : suffix c (l ++ r)) : suffix c r := by
  obtain ⟨p, H⟩ := H; exact ⟨p ++ l, by simp [H]⟩
theorem suffix_eq {a b : List JitBytecode.instr} (A : suffix c a) (B : suffix c b) (L : a.length = b.length) : a = b := by
  obtain ⟨p, Hp⟩ := A; obtain ⟨q, Hq⟩ := B
  rw [Hp] at Hq
  have Lp : p.length = q.length := by
    have := congrArg List.length Hq; simp at this; omega
  exact (List.append_inj Hq Lp).2
theorem find_label_suffix (l : Nat) : ∀ (iss r : List JitBytecode.instr), JitBytecode.find_label l iss = some r →
    ∃ p, iss = p ++ r
  | [], _, H => by simp [JitBytecode.find_label] at H
  | i :: iss, r, H => by
    have Rest : JitBytecode.find_label l iss = some r → ∃ p, i :: iss = p ++ r := fun Hf => by
      obtain ⟨p, E⟩ := find_label_suffix l iss r Hf; exact ⟨i :: p, by simp [E]⟩
    cases i with
    | ILabel x =>
      simp only [JitBytecode.find_label] at H
      split at H
      · cases H; exact ⟨[.ILabel x], rfl⟩
      · exact Rest H
    | _ => exact Rest H
theorem lbl_ok_sound {l : Nat} {r : List JitBytecode.instr} (H : lbl_ok c l r = true) (S : suffix c r) :
    lbl c l = some r := by
  unfold lbl_ok at H
  split at H
  · rename_i r' E
    simp at H
    rw [E]; congr 1
    exact suffix_eq (find_label_suffix l _ _ E) S H
  · simp at H

theorem chain_head_ok {d : Nat} {p : prim} {args : List expr} {v : value} {e : expr}
    (H : chain_head c d p args = some (v, e)) : p = PCons ∧ ∃ a, args = [a, e] ∧ lit_val a = some v := by
  unfold chain_head at H
  split at H
  · split at H
    · rename_i a f2 a2
      split at H
      · simp at H; obtain ⟨A, B⟩ := H; subst A B; exact ⟨rfl, a, rfl, ‹_›⟩
      · simp at H
    · simp at H
  · simp at H
theorem konst_vr_ok {v : value} {k : Nat} (H : konst_vr c v k = true) : ∃ w, konst c k = some w ∧ VR v w := by
  unfold konst_vr at H
  split at H
  · exact ⟨_, ‹_›, vrb_sound _ _ H⟩
  · simp at H
theorem chain_tail_ok {d : Nat} {v : value} {r r' : List JitBytecode.instr} (H : chain_tail c d v r = some r') :
    ∃ k w, r = .IPrim d .PCons [.OConst k, .OSlot d] :: r' ∧ konst c k = some w ∧ VR v w := by
  unfold chain_tail at H
  split at H
  · split at H
    · simp only [Bool.and_eq_true, beq_iff_eq] at *
      obtain ⟨⟨⟨A, B⟩, C⟩, D⟩ := ‹_ ∧ _›; subst A B; have := q_eqb_eq C; subst this
      obtain ⟨w, K, V⟩ := konst_vr_ok D; cases H; exact ⟨_, w, rfl, K, V⟩
    · simp at H
  · simp at H
end Sound

theorem vrb_sound' {v : value} {w : JitBytecode.val} (H : vrb v w = true) : VR v w := vrb_sound v w H

-- ---------- the tactic ----------
/-- Apply each lemma to each hypothesis it accepts (any further argument by `assumption`),
replacing the hypothesis by the result; split conjunctions and existentials; add the tails of
`suffix` hypotheses; substitute; repeat to a fixpoint. Rocq: `use` and `sat_suffix`. -/
partial def useAllLoop (lemmas : Array Term) (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  let mut progress := false
  -- split ∧ and ∃
  for ldecl in (← (← getMainGoal).getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 then
      let s ← saveState
      try
        liftMetaTactic fun g => do
          let rs ← g.cases ldecl.fvarId
          return rs.toList.map (·.mvarId)
        progress := true
      catch _ => s.restore
  if progress then
    try evalTactic (← `(tactic| subst_vars)) catch _ => pure ()
    useAllLoop lemmas (fuel - 1); return
  -- suffix tails
  for ldecl in (← (← getMainGoal).getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    if ty.isAppOf ``JitLowerCheck.suffix then
      for L in #[(← `(suffix_tail)), (← `(suffix_app))] do
        let s ← saveState
        try
          withMainContext do
            let h ← Term.exprToSyntax ldecl.toExpr
            let e ← withReducible <| Term.withoutErrToSorry do
              let e ← Term.elabTerm (← `($L $h)) none
              Term.synthesizeSyntheticMVarsNoPostponing
              pure e
            let e ← instantiateMVars e
            if e.hasMVar || e.hasSorry then throwError "mvars"
            let t ← instantiateMVars (← inferType e)
            if (← findLocalDeclWithType? t).isSome then throwError "dup"
            liftMetaTactic fun g => do
              let g ← g.assert `hs t e
              let (_, g) ← g.intro1
              return [g]
          progress := true
        catch _ => s.restore
  if progress then useAllLoop lemmas (fuel - 1); return
  -- lemmas
  for ldecl in (← (← getMainGoal).getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    if !(← isProp ldecl.type) then continue
    for L in lemmas do
      for twoArgs in [true, false] do
        let s ← saveState
        try
          withMainContext do
            let h ← Term.exprToSyntax ldecl.toExpr
            let stx ← if twoArgs then `($L $h (by assumption)) else `($L $h)
            let e ← withReducible <| Term.withoutErrToSorry do
              let e ← Term.elabTerm stx none
              Term.synthesizeSyntheticMVarsNoPostponing
              pure e
            let e ← instantiateMVars e
            if e.hasMVar || e.hasSorry then throwError "mvars"
            let t ← instantiateMVars (← inferType e)
            if (← whnfR t).isForall then throwError "partial"
            liftMetaTactic fun g => do
              let g ← g.assert `hu t e
              let (_, g) ← g.intro1
              let g ← g.tryClear ldecl.fvarId
              return [g]
          progress := true
          break
        catch _ => s.restore
      if progress then break
    if progress then break
  if progress then
    try evalTactic (← `(tactic| subst_vars)) catch _ => pure ()
    useAllLoop lemmas (fuel - 1)

syntax "use_all" "[" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| use_all [$ls,*]) => useAllLoop ls.getElems 500

/-- Rocq's `crush`: unfold one step of the checker in H and split every match in it. -/
macro "crush " H:ident : tactic => `(tactic| (
  first | unfold chk at $H:ident | unfold chkT at $H:ident | unfold chkOp at $H:ident | unfold chkOps at $H:ident | unfold chkW at $H:ident | unfold chkTA at $H:ident
  try dsimp only at $H:ident
  repeat' (split at $H:ident)
  all_goals (try simp only [reduceCtorEq, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true, beq_iff_eq,
    Bool.not_eq_true', beq_eq_false_iff_ne, decide_eq_true_eq] at *)
  all_goals (try subst_vars)))

macro "side" : tactic => `(tactic| first | assumption | rfl | omega | (simp only [Nat.max_def]; split <;> omega) | (intro h; subst h; simp_all; done) | (simp_all; done))

section Steps
variable (c : JitBytecode.code) (n : Nat)
  (IC : ∀ {g top e dst r r'}, chk c n g top e dst r = some r' → suffix c r → Comp c g top e dst r r' ∧ suffix c r')
  (IT : ∀ {g top e r l r'}, chkT c n g top e r = some (l, r') → suffix c r → CompT c g top e l r r' ∧ suffix c r')
  (IO : ∀ {g top e r o top2 r'}, chkOp c n g top e r = some (o, top2, r') → suffix c r → CompOp c g top e o top2 r r' ∧ suffix c r')
  (IOs : ∀ {g top es r os r'}, chkOps c n g top es r = some (os, r') → suffix c r → CompOps c g top es os r r' ∧ suffix c r')
  (IW : ∀ {g s es r r'}, chkW c n g s es r = some r' → suffix c r → CompW c g s es r r' ∧ suffix c r')
  (ITA : ∀ {g s t es ms r r'}, chkTA c n g s t es ms r = some r' → suffix c r → CompTA c g s t es ms r r' ∧ suffix c r')
include IC IT IO IOs IW ITA

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000 in
theorem chk_step {g top e dst r r'} (H : chk c (n + 1) g top e dst r = some r') (S : suffix c r) :
    Comp c g top e dst r r' ∧ suffix c r' := by
  crush H
  all_goals use_all [IC, IT, IO, IOs, IW, ITA, lbl_ok_sound, is_bool_eq, vrb_sound', is_call_ok,
    is_tailcall_ok, chain_tail_ok, chain_head_ok, o_eqb_eq, os_eqb_eq, q_eqb_eq]
  all_goals (refine ⟨?_, by assumption⟩)
  all_goals first | (apply Comp.C_lit <;> side) | (apply Comp.C_move <;> side) | (apply Comp.C_same <;> side) | (apply Comp.C_prim <;> side) | (apply Comp.C_let <;> side) | (apply Comp.C_alias <;> side) | (apply Comp.C_if_slot <;> side) | (apply Comp.C_if_ret <;> side) | (apply Comp.C_cond_nil) | (apply Comp.C_cond_true <;> side) | (apply Comp.C_cond_slot <;> side) | (apply Comp.C_cond_ret <;> side) | (apply Comp.C_type <;> side) | (apply Comp.C_and <;> side) | (apply Comp.C_or <;> side) | (apply Comp.C_ret <;> side) | (apply Comp.C_call <;> side) | (refine Comp.C_tail ‹_› rfl ?_ ?_ ‹_› ‹_› <;> first | omega | (simp only [Nat.max_def]; split <;> omega)) | (apply Comp.C_chain <;> side)

set_option maxHeartbeats 4000000 in
theorem chkT_step {g top e r l r'} (H : chkT c (n + 1) g top e r = some (l, r')) (S : suffix c r) :
    CompT c g top e l r r' ∧ suffix c r' := by
  crush H
  all_goals use_all [IC, IT, IO, IOs, IW, ITA, lbl_ok_sound, o_eqb_eq]
  all_goals (refine ⟨?_, by assumption⟩)
  all_goals first | (apply CompT.T_and <;> side) | (apply CompT.T_or <;> side) | (apply CompT.T_let <;> side) | (apply CompT.T_alias <;> side) | (apply CompT.T_type <;> side) | (apply CompT.T_leaf <;> side)

set_option maxHeartbeats 4000000 in
theorem chkOp_step {g top e r o top2 r'} (H : chkOp c (n + 1) g top e r = some (o, top2, r')) (S : suffix c r) :
    CompOp c g top e o top2 r r' ∧ suffix c r' := by
  crush H
  all_goals use_all [IC, IT, IO, IOs, IW, ITA]
  all_goals first | (refine ⟨?_, by assumption⟩; first | (apply CompOp.O_var <;> side) | (apply CompOp.O_val <;> side) | (apply CompOp.O_type <;> side)) | (obtain ⟨w, W1, W2, _⟩ := find_k_sound _ _ _ _ ‹find_k _ _ 0 = some _›; exact ⟨CompOp.O_lit ‹_› (by simpa [konst] using W1) W2, S⟩)

set_option maxHeartbeats 4000000 in
theorem chkOps_step {g top es r os r'} (H : chkOps c (n + 1) g top es r = some (os, r')) (S : suffix c r) :
    CompOps c g top es os r r' ∧ suffix c r' := by
  crush H
  all_goals use_all [IC, IT, IO, IOs, IW, ITA]
  all_goals (refine ⟨?_, by assumption⟩)
  all_goals first | (apply CompOps.Os_nil) | (apply CompOps.Os_cons <;> side)

set_option maxHeartbeats 4000000 in
theorem chkW_step {g s es r r'} (H : chkW c (n + 1) g s es r = some r') (S : suffix c r) :
    CompW c g s es r r' ∧ suffix c r' := by
  crush H
  all_goals use_all [IC, IT, IO, IOs, IW, ITA]
  all_goals (refine ⟨?_, by assumption⟩)
  all_goals first | (apply CompW.W_nil) | (apply CompW.W_cons <;> side)

set_option maxHeartbeats 4000000 in
theorem chkTA_step {g s t es ms r r'} (H : chkTA c (n + 1) g s t es ms r = some r') (S : suffix c r) :
    CompTA c g s t es ms r r' ∧ suffix c r' := by
  crush H
  all_goals use_all [IC, IT, IO, IOs, IW, ITA, moves_prefix_ok]
  all_goals first | (refine ⟨?_, by assumption⟩; first | (apply CompTA.TA_same <;> side) | (apply CompTA.TA_temp <;> side) | (apply CompTA.TA_direct <;> side)) | (subst_vars; exact ⟨CompTA.TA_nil, suffix_app S⟩)
end Steps

theorem chk_sound (c : JitBytecode.code) : ∀ n,
    (∀ {g top e dst r r'}, chk c n g top e dst r = some r' → suffix c r → Comp c g top e dst r r' ∧ suffix c r') ∧
    (∀ {g top e r l r'}, chkT c n g top e r = some (l, r') → suffix c r → CompT c g top e l r r' ∧ suffix c r') ∧
    (∀ {g top e r o top2 r'}, chkOp c n g top e r = some (o, top2, r') → suffix c r → CompOp c g top e o top2 r r' ∧ suffix c r') ∧
    (∀ {g top es r os r'}, chkOps c n g top es r = some (os, r') → suffix c r → CompOps c g top es os r r' ∧ suffix c r') ∧
    (∀ {g s es r r'}, chkW c n g s es r = some r' → suffix c r → CompW c g s es r r' ∧ suffix c r') ∧
    (∀ {g s t es ms r r'}, chkTA c n g s t es ms r = some r' → suffix c r → CompTA c g s t es ms r r' ∧ suffix c r') := by
  intro n
  induction n with
  | zero => refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [chk, chkT, chkOp, chkOps, chkW, chkTA]
  | succ n IH =>
    obtain ⟨IC, IT, IO, IOs, IW, ITA⟩ := IH
    exact ⟨chk_step c n IC IT IO IOs IW ITA, chkT_step c n IC IT IO IOs IW ITA, chkOp_step c n IC IT IO IOs IW ITA,
      chkOps_step c n IC IT IO IOs IW ITA, chkW_step c n IC IT IO IOs IW ITA, chkTA_step c n IC IT IO IOs IW ITA⟩

theorem chk_fn_sound (c : JitBytecode.code) (n : Nat) (ps : List name) (b : expr)
    (H : (match chk c n (bind ps 2) (2 + ps.length) b DRet (JitBytecode.code_ins c) with
          | some _ => true | none => false) = true) : CompFn c ps b := by
  split at H
  · rename_i r' E
    exact ⟨r', ((chk_sound c n).1 E ⟨[], rfl⟩).1⟩
  · simp at H

/-- Acceptance is a proof that the code is a lowering of the definition. -/
theorem check_fn_sound (c : JitBytecode.code) (ps : List name) (b : expr) (H : check_fn c ps b = true) :
    CompFn c ps b := chk_fn_sound c fuel ps b H

end JitLowerCheck
