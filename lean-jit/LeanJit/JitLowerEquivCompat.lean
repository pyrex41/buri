import LeanJit.JitLowerEquivProofs
/-! Pilot: statements Rocq leaves unproved at 670d29d, attempted in Lean.
`VRel_down` (Rocq: `VRel_down_statement`, unproved) is proved here, and with it the
compatibility lemma for `type` (Rocq: `compat_type_statement`, unproved). -/
namespace JitLowerEquiv
open Observation KLSyntax KLSyntax.expr KLValue KLValue.value KLSemantics KLSemantics.control
open KLSemantics.move KLSemantics.config KLPort JitProfile JitLowerRel

section Compat
variable {sealed : List name} {D : List (name × fundef)}

def VRel_down_statement' (sealed : List name) (D : List (name × fundef)) : Prop :=
  ∀ k j w v0 v, j ≤ k → VRel sealed D k w v0 v → VRel sealed D j w v0 v

theorem Vbelow_eq {j i : Nat} (L : i < j) : Vbelow sealed D j i = VRel sealed D i := by
  cases j with
  | zero => omega
  | succ k => exact VRelF_index k i (by omega)

mutual
theorem VBody_down {j j' : Nat} (Lj : j' ≤ j) {w : world} : ∀ (v0 v : value),
    VBody sealed D (Vbelow sealed D j) j w v0 v → VBody sealed D (Vbelow sealed D j') j' w v0 v
  | VCons a0 d0, v, H => by
      cases v with
      | VCons a d => simp only [VBody] at H ⊢; exact ⟨VBody_down Lj a0 a H.1, VBody_down Lj d0 d H.2⟩
      | _ => simp [VBody] at H
  | VPartial f0 as0, v, H => by
      cases v with
      | VPartial f as1 => simp only [VBody] at H ⊢; exact ⟨H.1, VBody_list_down Lj as0 as1 H.2⟩
      | _ => simp [VBody] at H
  | VLam x0 b0 r0, v, H => by
      cases v with
      | VLam x b r =>
        simp only [VBody] at H ⊢
        refine ⟨H.1, fun i Li w' Hw a0 a A => ?_⟩
        rw [Vbelow_eq Li] at A
        have E : ∀ i', i' ≤ i → Vbelow sealed D j i' = Vbelow sealed D j' i' := fun i' Li' => by
          rw [Vbelow_eq (by omega), Vbelow_eq (by omega)]
        exact ERel_with_ext E (H.2 i (by omega) w' Hw a0 a (by rw [Vbelow_eq (by omega)]; exact A))
      | _ => simp [VBody] at H
  | VFrozen b0 r0, v, H => by
      cases v with
      | VFrozen b r =>
        simp only [VBody] at H ⊢
        refine ⟨H.1, fun i Li w' Hw => ?_⟩
        have E : ∀ i', i' ≤ i → Vbelow sealed D j i' = Vbelow sealed D j' i' := fun i' Li' => by
          rw [Vbelow_eq (by omega), Vbelow_eq (by omega)]
        exact ERel_with_ext E (H.2 i (by omega) w' Hw)
      | _ => simp [VBody] at H
  | VNum _, v, H | VSym _, v, H | VBool _, v, H | VStr _, v, H | VNil, v, H | VVec _, v, H
  | VStream _, v, H | VExn _, v, H => by cases v <;> simp_all [VBody]
theorem VBody_list_down {j j' : Nat} (Lj : j' ≤ j) {w : world} : ∀ (l0 l : List value),
    VBody_list sealed D (Vbelow sealed D j) j w l0 l → VBody_list sealed D (Vbelow sealed D j') j' w l0 l
  | [], [], _ => by simp [VBody_list]
  | x0 :: r0, x :: r, H => by
      simp only [VBody_list] at H ⊢; exact ⟨VBody_down Lj x0 x H.1, VBody_list_down Lj r0 r H.2⟩
  | [], _ :: _, H | _ :: _, [], H => by simp [VBody_list] at H
end

theorem VRel_down : VRel_down_statement' sealed D := by
  intro k j w v0 v L H
  rw [VRel_unfold] at H ⊢
  exact VBody_down L v0 v H

theorem SRel_with_down {k j j' : Nat} (Lj : j' ≤ j) (Lk : j ≤ k) {w s0 s}
    (H : SRel_with D (VRelF sealed D k j) w s0 s) : SRel_with D (VRelF sealed D k j') w s0 s := by
  rw [VRelF_index k j Lk] at H; rw [VRelF_index k j' (by omega)]
  obtain ⟨W, H0, H1, Gf, Gv, Hp⟩ := H
  refine ⟨W, H0, H1, Gf, Forall2_impl (fun _ _ ⟨E, A⟩ => ⟨E, VRel_down j j' w _ _ Lj A⟩) Gv, fun l0 l I => ?_⟩
  obtain ⟨c0, c, N0, N, F⟩ := Hp l0 l I
  exact ⟨c0, c, N0, N, Forall2_impl (fun _ _ A => VRel_down j j' w _ _ Lj A) F⟩

theorem KRel_with_down {V} {j j' : Nat} (Lj : j' ≤ j) {w K0 K} (H : KRel_with sealed D V j w K0 K) :
    KRel_with sealed D V j' w K0 K := fun i Li => H i (by omega)

/-- Anti-reduction: one internal step on each side, with the target's resource step matched by
the source's. The index counts target steps. -/
theorem obs_anti {j w c0 c c0' c'}
    (N0 : next_r (jit_rules sealed) jit_profile c0 = MTau c0') (Rc0 : running_state c0 = true)
    (N : next_r (jit_rules sealed) jit_profile c = MTau c')
    (O : ObsT sealed j w c0' c')
    (ORes : ∀ r x, (jit_rules sealed).resource_exn r = some x →
      ObsT sealed j w (Cfg (Throw x) c0.kont c0.mem) (Cfg (Throw x) c.kont c.mem)) :
    ObsT sealed (j + 1) w c0 c := by
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
    | step_r_resource r x _ X =>
      obtain ⟨A, B, C⟩ := ORes r x X n t' c'' (by omega) Hr'
      have pre : ∀ {t c2}, srun sealed (Cfg (Throw x) c0.kont c0.mem) t c2 → srun sealed c0 (trace_of .Tau ++ t) c2 :=
        fun H => .step _ .Tau _ _ _ (.step_r_resource _ r x Rc0 X) H
      refine ⟨fun v s E => ?_, fun x' s E => ?_, fun why W => ?_⟩
      · obtain ⟨v0, s0, w', S, Wx, G1, G2⟩ := A v s E; exact ⟨v0, s0, w', pre S, Wx, G1, G2⟩
      · obtain ⟨s0, w', S, Wx, G⟩ := B x' s E; exact ⟨s0, w', pre S, Wx, G⟩
      · obtain ⟨c0'', why0, S, W0⟩ := C why W; exact ⟨c0'', why0, pre S, W0⟩

/-- `compat_type_statement`, unproved in Rocq at 670d29d. -/
theorem compat_type : compat_type_statement sealed D := by
  intro g a0 a HA k w rho0 rho W Env j Lj w' Hw K0 K HK s0 s HS
  cases j with
  | zero => intro n _ _ L; omega
  | succ j =>
    have HS' := SRel_with_down (Nat.le_succ j) Lj HS
    refine obs_anti (c0' := Cfg (Eval rho0 a0) K0 s0) (c' := Cfg (Eval rho a) K s) rfl rfl rfl ?_ ?_
    · exact HA k w rho0 rho W Env j (by omega) w' Hw K0 K (KRel_with_down (Nat.le_succ j) HK) s0 s HS'
    · intro r x _
      exact (HK j (Nat.le_succ j) w' (wext_refl Hw.2)).2 x s0 s HS'
end Compat
end JitLowerEquiv
