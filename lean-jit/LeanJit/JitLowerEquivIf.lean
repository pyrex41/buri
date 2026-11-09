import LeanJit.JitLowerEquivCompat
/-! Pilot: `compat_if_statement` (unproved in Rocq at 670d29d), attempted in Lean. -/
namespace JitLowerEquiv
open Observation KLSyntax KLSyntax.expr KLValue KLValue.value KLSemantics KLSemantics.control
open KLSemantics.frame KLSemantics.move KLSemantics.config KLPort JitProfile JitLowerRel

section CompatIf
variable {sealed : List name} {D : List (name × fundef)}

/-- Anti-reduction where the target is not running (a raise), so it has no resource step. -/
theorem obs_anti_nr {j w c0 c c0' c'}
    (N0 : next_r (jit_rules sealed) jit_profile c0 = MTau c0')
    (N : next_r (jit_rules sealed) jit_profile c = MTau c') (Rc : running_state c = false)
    (O : ObsT sealed j w c0' c') : ObsT sealed (j + 1) w c0 c := by
  intro n t c'' L Hr
  cases Hr with
  | runs_0 =>
    refine ⟨fun v s E => ?_, fun x s E => ?_, fun why W => ?_⟩
    · subst E; simp [next_r] at N
    · subst E; simp [next_r] at N
    · rw [N] at W; cases W
  | runs_S n _ l c1 t' _ St Hr' =>
    cases St with
    | step_r_tau _ N1 =>
      rw [N] at N1; cases N1
      obtain ⟨A, B, C⟩ := O n t' c'' (by omega) Hr'
      have pre : ∀ {t c2}, srun sealed c0' t c2 → srun sealed c0 (trace_of .Tau ++ t) c2 :=
        fun H => .step _ .Tau _ _ _ (.step_r_tau _ _ N0) H
      refine ⟨fun v s E => ?_, fun x s E => ?_, fun why W => ?_⟩
      · obtain ⟨v0, s0, w', S, Wx, G1, G2⟩ := A v s E; exact ⟨v0, s0, w', pre S, Wx, G1, G2⟩
      · obtain ⟨s0, w', S, Wx, G⟩ := B x s E; exact ⟨s0, w', pre S, Wx, G⟩
      · obtain ⟨c0'', why0, S, W0⟩ := C why W; exact ⟨c0'', why0, pre S, W0⟩
    | step_r_io q kk r N1 => rw [N] at N1; cases N1
    | step_r_resource r x R _ => rw [Rc] at R; cases R

theorem wext_trans {w w' w'' : world} (A : wext w w') (B : wext w' w'') : wext w w'' :=
  ⟨fun a I => B.1 a (A.1 a I), B.2⟩

theorem ERel_wext {k : Nat} {w w' : world} {rho0 e0 rho e} (Hw : wext w w')
    (H : ERel sealed D k w rho0 e0 rho e) : ERel sealed D k w' rho0 e0 rho e :=
  fun j L w'' Hw'' => H j L w'' (wext_trans Hw Hw'')

theorem KRel_with_wext {V} {j : Nat} {w w' : world} {K0 K} (Hw : wext w w')
    (H : KRel_with sealed D V j w K0 K) : KRel_with sealed D V j w' K0 K :=
  fun i Li w'' Hw'' => H i Li w'' (wext_trans Hw Hw'')

/-- What a value does to an `if` frame (KLSemantics.ret_move, case KIf). -/
def if_ctl (rho : lenv) (a b : expr) (v : value) : control :=
  match v with | VBool true => Eval rho a | VBool false => Eval rho b | _ => Throw .XNotBoolean

/-- A raise through the `if` frame. -/
theorem KIf_throw {k j : Nat} {w : world} {rho0 rho : lenv} {a0 a b0 b : expr} {K0 K : List frame}
    (HK : KRel_with sealed D (VRelF sealed D k) j w K0 K) {i : Nat} (Li : i ≤ j) (Lk : j ≤ k) {w' : world}
    (Hw : wext w w') {x s0 s} (HS : SRel_with D (VRelF sealed D k i) w' s0 s) :
    ObsT sealed i w' (Cfg (Throw x) (KIf a0 b0 rho0 :: K0) s0) (Cfg (Throw x) (KIf a b rho :: K) s) := by
  cases i with
  | zero => intro n _ _ L; omega
  | succ i =>
    have HS' := SRel_with_down (Nat.le_succ i) (by omega) HS
    exact obs_anti_nr (c0' := Cfg (Throw x) K0 s0) (c' := Cfg (Throw x) K s) rfl rfl rfl
      ((HK i (by omega) w' Hw).2 x s0 s HS')

/-- The `if` frame preserves related continuations, given the branches are related. -/
theorem KIf_rel {k j : Nat} (Lj : j ≤ k) {w : world} {rho0 rho : lenv} {a0 a b0 b : expr} {K0 K : List frame}
    (HA : ERel sealed D k w rho0 a0 rho a) (HB : ERel sealed D k w rho0 b0 rho b)
    (HK : KRel_with sealed D (VRelF sealed D k) j w K0 K) :
    KRel_with sealed D (VRelF sealed D k) j w (KIf a0 b0 rho0 :: K0) (KIf a b rho :: K) := by
  intro i Li w' Hw
  refine ⟨?_, fun x s0 s HS => KIf_throw HK Li Lj Hw HS⟩
  intro v0 v s0 s HV HS
  cases i with
  | zero => intro n _ _ L; omega
  | succ i =>
    have HS' := SRel_with_down (Nat.le_succ i) (by omega) HS
    have HK' := KRel_with_down (j' := i) (by omega) HK
    rw [VRelF_index k (i + 1) (by omega), VRel_unfold] at HV
    have thr : ObsT sealed i w' (Cfg (Throw .XNotBoolean) K0 s0) (Cfg (Throw .XNotBoolean) K s) :=
      (HK' i (Nat.le_refl _) w' Hw).2 _ s0 s HS'
    refine obs_anti (c0' := Cfg (if_ctl rho0 a0 b0 v0) K0 s0) (c' := Cfg (if_ctl rho a b v) K s)
      rfl rfl rfl ?_ (fun r x _ => KIf_throw HK (by omega) Lj Hw HS')
    cases v0 <;> cases v <;> simp only [VBody] at HV <;> (try contradiction) <;> (try exact thr)
    rename_i b1 b2; subst HV
    cases b1
    · exact HB i (by omega) w' Hw K0 K (KRel_with_wext Hw HK') s0 s HS'
    · exact HA i (by omega) w' Hw K0 K (KRel_with_wext Hw HK') s0 s HS'

/-- `compat_if_statement`, unproved in Rocq at 670d29d. -/
theorem compat_if : compat_if_statement sealed D := by
  intro g c0 c a0 a b0 b HC HA HB k w rho0 rho W Env j Lj w' Hw K0 K HK s0 s HS
  cases j with
  | zero => intro n _ _ L; omega
  | succ j =>
    have HS' := SRel_with_down (Nat.le_succ j) Lj HS
    refine obs_anti (c0' := Cfg (Eval rho0 c0) (KIf a0 b0 rho0 :: K0) s0)
      (c' := Cfg (Eval rho c) (KIf a b rho :: K) s) rfl rfl rfl ?_
      (fun r x _ => (HK j (Nat.le_succ j) w' (wext_refl Hw.2)).2 x s0 s HS')
    exact HC k w rho0 rho W Env j (by omega) w' Hw _ _
      (KIf_rel (by omega) (ERel_wext Hw (HA k w rho0 rho W Env)) (ERel_wext Hw (HB k w rho0 rho W Env))
        (KRel_with_down (Nat.le_succ j) HK)) s0 s HS'
end CompatIf
end JitLowerEquiv
