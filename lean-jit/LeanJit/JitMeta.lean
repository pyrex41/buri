import LeanJit.JitBytecode3
/-! Port of `rocq/JitMeta.v`: basic metatheory of the bytecode model. -/
namespace JitMeta
open JitBytecode JitBytecode.val JitBytecode.instr JitBytecode.move JitBytecode.final

inductive step (E : env) (pt : tree (prim × Nat)) : machine → Option (jreq × jres) → machine → Prop
  | StepTau m m' : next E pt m = MTau m' → step E pt m none m'
  | StepIO m q k r : next E pt m = MIO q k → step E pt m (some (q, r)) (k r)

def final_in (E : env) (pt : tree (prim × Nat)) (m : machine) (o : final) : Prop :=
  ∃ m', next E pt m = MFinal o m'
def stuck_in (E : env) (pt : tree (prim × Nat)) (m : machine) (w : stuck) : Prop :=
  next E pt m = MStuck w

theorem step_deterministic_tau (E pt m m1 m2) (H1 : step E pt m none m1) (H2 : step E pt m none m2) :
    m1 = m2 := by
  cases H1 with | StepTau _ A => cases H2 with | StepTau _ B => rw [A] at B; cases B; rfl

theorem step_deterministic_io (E pt m q1 q2 r1 r2 m1 m2)
    (H1 : step E pt m (some (q1, r1)) m1) (H2 : step E pt m (some (q2, r2)) m2) :
    q1 = q2 ∧ (r1 = r2 → m1 = m2) := by
  cases H1 with | StepIO _ k _ A => cases H2 with | StepIO _ k' _ B =>
    rw [A] at B; cases B; exact ⟨rfl, fun h => h ▸ rfl⟩

theorem step_tau_excludes_io (E pt m m1 q r m2) (H1 : step E pt m none m1)
    (H2 : step E pt m (some (q, r)) m2) : False := by
  cases H1 with | StepTau _ A => cases H2 with | StepIO _ _ _ B => rw [A] at B; cases B

theorem move_classification (E pt m) :
    (∃ m', next E pt m = MTau m') ∨ (∃ q k, next E pt m = MIO q k) ∨
    (∃ o m', next E pt m = MFinal o m') ∨ (∃ w, next E pt m = MStuck w) := by
  cases next E pt m with
  | MTau m' => exact .inl ⟨m', rfl⟩
  | MIO q k => exact .inr (.inl ⟨q, k, rfl⟩)
  | MFinal o m' => exact .inr (.inr (.inl ⟨o, m', rfl⟩))
  | MStuck w => exact .inr (.inr (.inr ⟨w, rfl⟩))

theorem final_not_stuck (E pt m o w) : final_in E pt m o → stuck_in E pt m w → False := by
  intro ⟨m', A⟩ B; unfold stuck_in at B; rw [A] at B; cases B

theorem step_not_stuck (E pt m l m' w) (H : step E pt m l m') (S : stuck_in E pt m w) : False := by
  unfold stuck_in at S; cases H with
  | StepTau _ A => rw [A] at S; cases S
  | StepIO _ _ _ A => rw [A] at S; cases S

theorem final_unique (E pt m o1 o2) : final_in E pt m o1 → final_in E pt m o2 → o1 = o2 := by
  intro ⟨a, A⟩ ⟨b, B⟩; rw [A] at B; cases B; rfl

theorem excluded_prims_stuck (E pt m d p args) (H : is_excluded p = true) :
    prim_step E pt m d p args = MStuck (.RExcluded p) := by
  cases p <;> first
    | (exfalso; revert H; decide)
    | (rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, args⟩⟩⟩ <;> rfl)

theorem next_empty_rest (E pt m) (H : m.m_rest = []) : next E pt m = MStuck .RFallOff := by
  unfold next; rw [H]

-- Maps: the lookup laws the machine relies on.
theorem tgetN_tsetN_same {A} (x : A) : ∀ f k (m : tree A), 1 ≤ k → k ≤ f →
    tgetN k (tsetN f k x m) = some x := by
  intro f; induction f with
  | zero => intro k m h1 h2; omega
  | succ f ih =>
    intro k m hk hf
    by_cases k1 : k ≤ 1 <;> by_cases ke : k % 2 = 0 <;> cases m <;>
      simp [tsetN, tgetN, k1, ke] <;> (apply ih <;> omega)

theorem tget_tset_same {A} (k : Pos) (x : A) (m : tree A) : tget k (tset k x m) = some x :=
  tgetN_tsetN_same x _ _ m (by simp [Pos.val]) (Nat.le_refl _)

theorem tget_leaf {A} (k : Pos) : tget k (@Leaf A) = none := rfl

theorem tgetN_tsetN_other {A} (x : A) : ∀ f j (m : tree A) k, 1 ≤ j → j ≤ f → 1 ≤ k → k ≠ j →
    tgetN k (tsetN f j x m) = tgetN k m := by
  intro f; induction f with
  | zero => intro j m k h1 h2; omega
  | succ f ih =>
    intro j m k hj hf hk hne
    by_cases j1 : j ≤ 1 <;> by_cases je : j % 2 = 0 <;> by_cases k1 : k ≤ 1 <;>
      by_cases ke : k % 2 = 0 <;> cases m <;> simp [tsetN, tgetN, j1, je, k1, ke] <;>
      first | omega | (rw [ih] <;> (try simp [tgetN]) <;> omega)

theorem tget_tset_other {A} (k j : Pos) (x : A) (m : tree A) (Hne : k ≠ j) :
    tget k (tset j x m) = tget k m := by
  apply tgetN_tsetN_other x _ _ m _ (by simp [Pos.val]) (Nat.le_refl _) (by simp [Pos.val])
  intro E; apply Hne; cases k; cases j; simp [Pos.val] at E; simp [E]

theorem move_writes (E pt m d s v r) (Hr : m.m_rest = IMove d s :: r)
    (Hs : sread (set_rest m r) s = some v) :
    ∃ m', next E pt m = MTau m' ∧ m'.m_rest = r ∧ tget (skey (m.m_fp + d)) m'.m_stack = some v := by
  unfold next; rw [Hr]; simp only; rw [Hs]
  exact ⟨_, rfl, rfl, tget_tset_same _ _ _⟩

theorem jump_if_false_requires_boolean (E pt m o l r v) (Hr : m.m_rest = IJumpIfFalse o l :: r)
    (Hop : read_op (set_rest m r) o = some v) (Hb : ∀ b, v ≠ VBool b) :
    next E pt m = raise_v (set_rest m r) "~S is not a boolean" v := by
  unfold next; rw [Hr]; simp only; rw [Hop]
  cases v with
  | VBool b => exact absurd rfl (Hb b)
  | _ => rfl

theorem return_at_top (m : machine) (v : val) (H : m.m_conts = []) : do_return m v = MFinal (.FReturn v) m := by
  unfold do_return; rw [H]

theorem raise_no_handler_final (m : machine) (msg : text) (v : val) (H : m.m_handlers = []) :
    ∃ e m', raise m msg v = MFinal (.FError e) m' := by
  unfold raise; rw [H]; exact ⟨_, _, rfl⟩

theorem install_sealed_refused (pt m d name c) (H : tget name m.m_sealed = some ()) :
    install pt m d (VPair (VSym S_defun) (VPair (VSym name) (VPair c VNil))) =
      raise_v m "~S is sealed and cannot be redefined" (VSym name) := by
  simp [install, vlist, Pos.eqb, H]

end JitMeta
