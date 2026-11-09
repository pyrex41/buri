import LeanJit.JitLowerKont
/-! Port of `rocq/JitLowerStable.v`: what writes to the stack leave intact. -/
namespace JitLowerStable
open KLSyntax KLValue KLSemantics JitLowerRel JitLowerKont
open JitBytecode (tree val)

theorem MEnv_stable {fp st st' g rho w} (M : MEnv fp st g rho) (P : Prot g fp w)
    (A : ∀ a, ¬ w a → slotv st a = slotv st' a) : MEnv fp st' g rho := by
  intro x s L
  obtain ⟨v, v', H1, H2, H3⟩ := M x s L
  exact ⟨v, v', H1, by rw [← A _ (P x s L)]; exact H2, H3⟩

theorem DoneR_stable {c fp st st' w vs os} (D : DoneR c fp st vs os) (F : ∀ x ∈ os, o_safe fp w x)
    (A : ∀ a, ¬ w a → slotv st a = slotv st' a) : DoneR c fp st' vs os := by
  induction D with
  | DR_nil => exact .DR_nil
  | @DR_cons v v' o vs os R V _ ih =>
    refine .DR_cons ?_ V (ih (fun x I => F x (by simp [I])))
    have Fo := F o (by simp)
    cases o with
    | OSlot s => simp only [read_o] at R ⊢; rw [← A _ Fo]; exact R
    | OConst k => exact R

theorem ArgsAt_stable {st st' a0 vs} (D : ArgsAt st a0 vs)
    (A : ∀ a, a0 ≤ a → a < a0 + vs.length → slotv st a = slotv st' a) : ArgsAt st' a0 vs := by
  induction D with
  | AA_nil a => exact .AA_nil a
  | @AA_cons a v v' vs S V _ ih =>
    refine .AA_cons ?_ V (ih (fun b B1 B2 => A b (by omega) (by simp; omega)))
    rw [← A a (Nat.le_refl _) (by simp)]; exact S

theorem loc_range : ∀ (ms : List (Nat × Nat)) (i n t : Nat), (∀ m ∈ ms, n + 2 ≤ m.2 ∧ m.2 < t) →
    loc ms i = i ∨ (n + 2 ≤ loc ms i ∧ loc ms i < t)
  | [], _, _, _, _ => .inl rfl
  | (s, u) :: ms, i, n, t, F => by
    simp only [loc]
    split
    · exact .inr (F (s, u) (by simp))
    · exact loc_range ms i n t (fun m I => F m (by simp [I]))

theorem ParamAt_stable {fp st st' ms i vs} (D : ParamAt fp st ms i vs)
    (A : ∀ j, i ≤ j → j < i + vs.length → slotv st (fp + loc ms j) = slotv st' (fp + loc ms j)) :
    ParamAt fp st' ms i vs := by
  induction D with
  | PA_nil i => exact .PA_nil i
  | @PA_cons i v v' vs S V _ ih =>
    refine .PA_cons ?_ V (ih (fun j J1 J2 => A j (by omega) (by simp; omega)))
    rw [← A i (Nat.le_refl _) (by simp)]; exact S

theorem sub_agree {w w1 : Nat → Prop} {P : Nat → Prop} (S : Sub w w1) (A : ∀ a, ¬ w a → P a) :
    ∀ a, ¬ w1 a → P a := fun a N => A a (fun X => N (S a X))

mutual
theorem KD_stable {c fp st cs w o r k} (h : KD c fp st cs w o r k) (st' : tree val)
    (A : ∀ a, ¬ w a → slotv st a = slotv st' a) : KD c fp st' cs w o r k :=
  match h with
  | .KD_ret s rk => .KD_ret s (RK_stable rk st' (fun a L => A a (fun X => by have := s a X; omega)))
  | .KD_jump hl hk => .KD_jump hl (KD_stable hk st' A)
  | .KD_label hk => .KD_label (KD_stable hk st' A)
  | .KD_let hM hP hE hd hC hS hA hK =>
    .KD_let (MEnv_stable hM hP A) hP hE hd hC hS hA (KC_stable hK st' (sub_agree hS A))
  | .KD_lett hM hP hE hd hC hS hA hK =>
    .KD_lett (MEnv_stable hM hP A) hP hE hd hC hS hA (TK_stable hK st' (sub_agree hS A))
  | .KD_test hk => .KD_test (TK_stable hk st' A)
  | .KD_prim h1 h2 h3 hM hP hE hC hD hF hB ho hS hA hw hK =>
    .KD_prim h1 h2 h3 (MEnv_stable hM hP A) hP hE hC (DoneR_stable hD hF A) hF hB ho hS hA hw
      (KD_stable hK st' (sub_agree hS A))
  | @JitLowerKont.KD.KD_call _ _ _ _ _ _ _ vals _ _ _ _ a s _ _ _ _ _ h1 h2 h3 hM hP hE hC hi hAA hs hS hA hw hK =>
    .KD_call h1 h2 h3 (MEnv_stable hM hP A) hP hE hC hi
      (ArgsAt_stable hAA (fun x X1 X2 => A x (fun W => by have := hs x W; simp at X2; omega)))
      hs hS hA hw (KD_stable hK st' (sub_agree hS A))
  | @JitLowerKont.KD.KD_tail _ _ _ _ _ _ _ _ vals es _ _ _ s t t0 ms n _ _ h1 h2 h3 h4 h5 hM hP hE hC hi ho hl hF hN hL hPA hs hrk =>
    .KD_tail h1 h2 h3 h4 h5 (MEnv_stable hM hP A) hP hE hC hi ho hl hF hN hL
      (ParamAt_stable hPA (fun j J1 J2 => A _ (fun W => by
        have := hs _ W; simp at J2
        rcases hL j ⟨J1, by omega⟩ with E | ⟨E1, E2⟩ <;> omega)))
      hs (RK_stable hrk st' (fun a L => A a (fun X => by have := hs a X; omega)))
termination_by structural h
theorem TK_stable {c fp st cs w gd l r k} (h : TK c fp st cs w gd l r k) (st' : tree val)
    (A : ∀ a, ¬ w a → slotv st a = slotv st' a) : TK c fp st' cs w gd l r k :=
  match h with
  | .TK_if hM hP hE hC1 hl hC2 hS hA hK1 hK2 =>
    .TK_if (MEnv_stable hM hP A) hP hE hC1 hl hC2 hS hA (KC_stable hK1 st' (sub_agree hS A)) (KC_stable hK2 st' (sub_agree hS A))
  | .TK_cond hM hP hE hC1 hl hC2 hS hA hK1 hK2 =>
    .TK_cond (MEnv_stable hM hP A) hP hE hC1 hl hC2 hS hA (KC_stable hK1 st' (sub_agree hS A)) (KC_stable hK2 st' (sub_agree hS A))
  | .TK_and hM hP hE hC hS hA hK =>
    .TK_and (MEnv_stable hM hP A) hP hE hC hS hA (TK_stable hK st' (sub_agree hS A))
  | .TK_andr hS hK => .TK_andr hS (TK_stable hK st' (sub_agree hS A))
  | .TK_or hM hP hE hl hC hS hA hK1 hK2 =>
    .TK_or (MEnv_stable hM hP A) hP hE hl hC hS hA (TK_stable hK1 st' (sub_agree hS A)) (TK_stable hK2 st' (sub_agree hS A))
  | .TK_orr hS hK => .TK_orr hS (TK_stable hK st' (sub_agree hS A))
  | .TK_jump hl hK => .TK_jump hl (TK_stable hK st' A)
  | .TK_label hK => .TK_label (TK_stable hK st' A)
  | .TK_value h1 h2 h3 hS hw hK1 hK2 =>
    .TK_value h1 h2 h3 hS hw (KD_stable hK1 st' (sub_agree hS A)) (KD_stable hK2 st' (sub_agree hS A))
termination_by structural h
theorem KC_stable {c fp st cs w dst r k} (h : KC c fp st cs w dst r k) (st' : tree val)
    (A : ∀ a, ¬ w a → slotv st a = slotv st' a) : KC c fp st' cs w dst r k :=
  match h with
  | .KC_ret s rk => .KC_ret s (RK_stable rk st' (fun a L => A a (fun X => by have := s a X; omega)))
  | .KC_slot hw hK => .KC_slot hw (KD_stable hK st' A)
termination_by structural h
theorem RK_stable {fp st cs k} (h : RK fp st cs k) (st' : tree val)
    (A : ∀ a, a < fp → slotv st a = slotv st' a) : RK fp st' cs k :=
  match h with
  | .RK_top => .RK_top
  | .RK_call ha hA hK hw =>
    .RK_call ha hA (KD_stable hK st' (fun x X => A x (by
      rcases Nat.lt_or_ge x fp with L | G
      · exact L
      · exact absurd (hA x (by omega)) X))) hw
termination_by structural h
end

end JitLowerStable
