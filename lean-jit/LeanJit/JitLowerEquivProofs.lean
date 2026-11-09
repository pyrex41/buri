import LeanJit.JitLowerEquiv
/-! Port of the proofs in `rocq/JitLowerEquiv.v` (670d29d) that `call_preservation_src_of_fundamental`
does not need beyond what is here: runs, worlds, the index family, the ground relation,
`KRel_top`, and, as implications from `fundamental_statement`, store reflexivity and adequacy. -/
namespace JitLowerEquiv
open Observation KLSyntax KLSyntax.expr KLValue KLValue.value KLSemantics KLSemantics.control
open KLSemantics.move KLSemantics.config KLPort JitProfile JitLowerRel

section Proofs
variable {sealed : List name} {D : List (name × fundef)}

-- --- runs ---
theorem runs_srun {n c t c'} (H : runs sealed n c t c') : srun sealed c t c' := by
  induction H with
  | runs_0 c => exact .refl c
  | runs_S n c l c1 t c2 St _ ih => exact .step _ _ _ _ _ St ih

theorem srun_runs {c t c'} (H : srun sealed c t c') : ∃ n, runs sealed n c t c' := by
  induction H with
  | refl c => exact ⟨0, .runs_0 c⟩
  | step c l c1 t c2 St _ ih => obtain ⟨n, ih⟩ := ih; exact ⟨n + 1, .runs_S _ _ _ _ _ _ St ih⟩

theorem srun_nil_Sstar : srun_nil_Sstar_statement sealed := by
  intro c c'; constructor
  · intro H
    generalize Et : ([] : trace) = t at H
    induction H with
    | refl c => exact .SS_refl c
    | step c l c1 t c2 St _ ih =>
      cases l with
      | Tau => exact .SS_step _ _ _ St (ih Et)
      | Obs ev => simp [trace_of] at Et
  · intro H
    induction H with
    | SS_refl c => exact .refl c
    | SS_step c c1 c2 St _ ih => exact .step _ .Tau _ [] _ St ih

theorem step_from_ret_top {v s l c1} (H : step_r (jit_rules sealed) jit_profile (Cfg (Ret v) [] s) l c1) :
    l = .Tau ∧ ∃ x r, (jit_rules sealed).resource_exn r = some x ∧ c1 = Cfg (Throw x) [] s := by
  cases H with
  | step_r_tau _ N => simp [next_r] at N
  | step_r_io q kk r N => simp [next_r] at N
  | step_r_resource r x _ X => exact ⟨rfl, x, r, X, rfl⟩

theorem no_step_from_throw_top {x s l c1} (H : step_r (jit_rules sealed) jit_profile (Cfg (Throw x) [] s) l c1) :
    False := by
  cases H with
  | step_r_tau _ N => simp [next_r] at N
  | step_r_io q kk r N => simp [next_r] at N
  | step_r_resource r x' R _ => simp [running_state] at R

-- --- worlds ---
theorem wext_refl {w : world} (H : wf_world w) : wext w w := ⟨fun _ A => A, H⟩

theorem mem_id_world {s : store} {a b : Nat} : (a, b) ∈ id_world s ↔ a = b ∧ a < s.heap.length := by
  simp only [id_world, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨l, L, E⟩; cases E; exact ⟨rfl, L⟩
  · rintro ⟨rfl, L⟩; exact ⟨a, L, rfl⟩

theorem id_world_wf (s : store) : wf_world (id_world s) := by
  simp only [wf_world, id_world, List.map_map]
  have : ∀ (f : Nat → Nat), (∀ l, f l = l) → ((List.range s.heap.length).map f).Nodup := by
    intro f hf; rw [show (List.range s.heap.length).map f = List.range s.heap.length from by
      simp [funext hf]]; exact List.nodup_range
  exact ⟨this _ (fun _ => rfl), this _ (fun _ => rfl)⟩

-- --- the ground relation ---
theorem GVal_list_iff {w : world} : ∀ {as0 as1 : List value}, GVal_list w as0 as1 ↔ Forall2 (GVal w) as0 as1
  | [], [] => by simp [GVal_list]; exact .nil
  | x0 :: r0, x :: r => by
    simp only [GVal_list]; constructor
    · rintro ⟨A, B⟩; exact .cons A (GVal_list_iff.1 B)
    · intro H; cases H with | cons A B => exact ⟨A, GVal_list_iff.2 B⟩
  | [], _ :: _ => by simp [GVal_list]; intro H; cases H
  | _ :: _, [] => by simp [GVal_list]; intro H; cases H

theorem GVal_fo {w : world} {v0 v : value} (F : fo v) (G : GVal w v0 v) : v0 = v := by
  induction F generalizing v0 with
  | fo_cons a d _ _ iha ihd =>
    cases v0 <;> simp [GVal] at G
    rw [iha G.1, ihd G.2]
  | _ => cases v0 <;> simp_all [GVal]

-- --- the index family ---
theorem VRel_unfold (k : Nat) : VRel sealed D k =
    VBody sealed D (match k with | 0 => fun _ _ _ _ => False | k' + 1 => VRelF sealed D k') k := by
  cases k with
  | zero => rfl
  | succ k =>
    show (if Nat.ble (k + 1) k = true then _ else _) = _
    rw [if_neg (by simp)]

theorem VRelF_index : VRelF_index_statement sealed D := by
  intro k; induction k with
  | zero => intro j L; have : j = 0 := by omega
            subst this; rfl
  | succ k ih =>
    intro j L
    show (if Nat.ble j k = true then _ else _) = _
    by_cases E : Nat.ble j k = true
    · rw [if_pos E]; exact ih j (Nat.le_of_ble_eq_true E)
    · rw [if_neg E]
      have : j = k + 1 := by have := Nat.not_le.1 (fun h => E (Nat.ble_eq_true_of_le h)); omega
      subst this; exact (VRel_unfold (k + 1)).symm

mutual
theorem VBody_ground {V} {k : Nat} {w : world} : ∀ (v0 v : value), VBody sealed D V k w v0 v → GVal w v0 v
  | VCons a0 d0, v, H => by
      cases v with
      | VCons a d => simp only [VBody] at H; simp only [GVal]; exact ⟨VBody_ground a0 a H.1, VBody_ground d0 d H.2⟩
      | _ => simp [VBody] at H
  | VPartial f0 as0, v, H => by
      cases v with
      | VPartial f as1 => simp only [VBody] at H; simp only [GVal]; exact ⟨H.1, VBody_list_ground as0 as1 H.2⟩
      | _ => simp [VBody] at H
  | VLam _ _ _, v, H => by cases v <;> simp_all [VBody, GVal]
  | VFrozen _ _, v, H => by cases v <;> simp_all [VBody, GVal]
  | VNum _, v, H | VSym _, v, H | VBool _, v, H | VStr _, v, H | VNil, v, H | VVec _, v, H
  | VStream _, v, H | VExn _, v, H => by cases v <;> simp_all [VBody, GVal]
theorem VBody_list_ground {V} {k : Nat} {w : world} : ∀ (l0 l : List value), VBody_list sealed D V k w l0 l → GVal_list w l0 l
  | [], [], _ => by simp [GVal_list]
  | x0 :: r0, x :: r, H => by
      simp only [VBody_list] at H; simp only [GVal_list]; exact ⟨VBody_ground x0 x H.1, VBody_list_ground r0 r H.2⟩
  | [], _ :: _, H | _ :: _, [], H => by simp [VBody_list] at H
end

theorem VRel_ground : VRel_ground_statement sealed D := by
  intro k w v0 v H; rw [VRel_unfold] at H; exact VBody_ground v0 v H

theorem SRel_with_ground {V1 : world → value → value → Prop} {w s0 s} (G : ∀ a b, V1 w a b → GVal w a b)
    (H : SRel_with D V1 w s0 s) : GStore w s0 s := by
  obtain ⟨_, _, _, Gf, Gv, Hp⟩ := H
  refine ⟨Gf, Forall2_impl (fun _ _ ⟨E, A⟩ => ⟨E, G _ _ A⟩) Gv, fun l0 l I => ?_⟩
  obtain ⟨c0, c, N0, N, F⟩ := Hp l0 l I
  exact ⟨c0, c, N0, N, Forall2_impl G F⟩

theorem SRel_ground : SRel_ground_statement sealed D := by
  intro k w s0 s H; exact SRel_with_ground (fun a b => VRel_ground k w a b) H

-- --- the empty continuation ---
theorem obs_top_throw {j w x s0 s} (W : wf_world w) (G : GStore w s0 s) :
    ObsT sealed j w (Cfg (Throw x) [] s0) (Cfg (Throw x) [] s) := by
  intro n t c' _ Hr
  cases Hr with
  | runs_0 =>
    refine ⟨fun v s' E => by simp at E, fun x' s' E => ?_, fun why N => by simp [next_r] at N⟩
    simp at E; obtain ⟨E1, E2⟩ := E; subst E1 E2
    exact ⟨s0, w, .refl _, wext_refl W, G⟩
  | runs_S n _ l c1 t c2 St _ => exact absurd St (fun St => no_step_from_throw_top St)

theorem obs_top_ret {j w v0 v s0 s} (W : wf_world w) (Gv : GVal w v0 v) (G : GStore w s0 s) :
    ObsT sealed j w (Cfg (Ret v0) [] s0) (Cfg (Ret v) [] s) := by
  intro n t c' _ Hr
  cases Hr with
  | runs_0 =>
    refine ⟨fun v' s' E => ?_, fun x s' E => by simp at E, fun why N => by simp [next_r] at N⟩
    simp at E; obtain ⟨E1, E2⟩ := E; subst E1 E2
    exact ⟨v0, s0, w, .refl _, wext_refl W, Gv, G⟩
  | runs_S n _ l c1 t' c2 St Hr' =>
    obtain ⟨El, x, r, Rx, Ec⟩ := step_from_ret_top St
    subst El Ec
    cases Hr' with
    | runs_0 =>
      refine ⟨fun v' s' E => by simp at E, fun x' s' E => ?_, fun why N => by simp [next_r] at N⟩
      simp at E; obtain ⟨E1, E2⟩ := E; subst E1 E2
      refine ⟨s0, w, ?_, wext_refl W, G⟩
      exact .step _ .Tau _ [] _ (step_r.step_r_resource (Cfg (Ret v0) [] s0) r x rfl Rx) (.refl _)
    | runs_S _ _ _ _ _ _ St' _ => exact absurd St' (fun St => no_step_from_throw_top St)

theorem KRel_top : KRel_top_statement sealed D := by
  intro k w _ j L w' ⟨_, W⟩
  constructor
  · intro v0 v s0 s HV HS
    rw [VRelF_index k j L] at HV HS
    exact obs_top_ret W (VRel_ground j w' v0 v HV) (SRel_with_ground (fun a b => VRel_ground j w' a b) HS)
  · intro x s0 s HS
    rw [VRelF_index k j L] at HS
    exact obs_top_throw W (SRel_with_ground (fun a b => VRel_ground j w' a b) HS)

-- --- transport between index families ---
theorem KRel_with_ext {V V' : Nat → world → value → value → Prop} {j w K0 K}
    (Eq : ∀ i, i ≤ j → V i = V' i) (H : KRel_with sealed D V j w K0 K) : KRel_with sealed D V' j w K0 K := by
  intro i L w' Hw
  obtain ⟨A, B⟩ := H i L w' Hw
  rw [← Eq i L]; exact ⟨A, B⟩

theorem ERel_with_ext {V V' : Nat → world → value → value → Prop} {j w r0 e0 r e}
    (Eq : ∀ i, i ≤ j → V i = V' i) (H : ERel_with sealed D V j w r0 e0 r e) : ERel_with sealed D V' j w r0 e0 r e := by
  intro j' L w' Hw K0 K HK s0 s HS
  rw [← Eq j' L] at HS
  exact H j' L w' Hw K0 K (KRel_with_ext (fun i Li => (Eq i (by omega)).symm) HK) s0 s HS

-- --- reflexivity of values and stores, from the fundamental property ---
/-- The value relation below index k, as `VRel_unfold` spells it. -/
abbrev Vbelow (sealed : List name) (D : List (name × fundef)) (k : Nat) : Nat → world → value → value → Prop :=
  match k with | 0 => fun _ _ _ _ => False | k' + 1 => VRelF sealed D k'

theorem closure_id_ok {n l : Nat} : ∀ {rho : lenv}, closure_id rho = some l → vok_env n rho → l < n
  | (kk, VVec l') :: rr, h, E => by
      simp only [closure_id] at h; split at h
      · cases h; simp only [vok_env, vok] at E; exact E.1
      · simp at h
  | [], h, _ => by simp [closure_id] at h
  | (_, VNum _) :: _, h, _ | (_, VSym _) :: _, h, _ | (_, VBool _) :: _, h, _ | (_, VStr _) :: _, h, _
  | (_, VNil) :: _, h, _ | (_, VCons _ _) :: _, h, _ | (_, VStream _) :: _, h, _ | (_, VLam _ _ _) :: _, h, _
  | (_, VFrozen _ _) :: _, h, _ | (_, VPartial _ _) :: _, h, _ | (_, VExn _) :: _, h, _ => by simp [closure_id] at h

theorem same_id_refl {n : Nat} {w : world} {rho : lenv} (E : vok_env n rho) (H : ∀ l, l < n → (l, l) ∈ w) :
    same_id w rho rho := by
  unfold same_id
  cases h : closure_id rho with
  | none => trivial
  | some l => exact H l (closure_id_ok h E)

theorem fo_vok {n : Nat} {v : value} (H : fo v) : vok n v := by
  induction H <;> simp_all [vok]

theorem lookup_In {x : name} : ∀ {rho : lenv} {v : value}, lookup x rho = some v → (x, v) ∈ rho
  | [], _, E => by simp [lookup] at E
  | (y, u) :: rho, v, E => by
    simp only [lookup] at E
    split at E
    · rename_i T; cases E; rw [(text_eqb_eq x y).1 T]; simp
    · exact List.mem_cons_of_mem _ (lookup_In E)

section FromFundamental
set_option linter.unusedSectionVars false
variable (F : fundamental_statement sealed D)
include F

theorem body_of_fundamental (DW : D_wf sealed D) {k j : Nat} (L : j < k + 1) {w' : world} (W' : wf_world w')
    {rho0 rho : lenv} {b : expr} (Env : EnvRelAll sealed D j w' rho0 rho) :
    ERel_with sealed D (VRelF sealed D k) j w' rho0 b rho b := by
  refine ERel_with_ext (V := VRelF sealed D j) (fun i Li => ?_) (F j w' rho0 rho b DW W' Env)
  rw [VRelF_index j i Li, VRelF_index k i (by omega)]

mutual
theorem vrefl (DW : D_wf sealed D) : ∀ (v : value) (n k : Nat) (w : world), wf_world w →
    (∀ l, l < n → (l, l) ∈ w) → vok n v → VRel sealed D k w v v
  | VCons a d, n, k, w, W, Hw, Ok => by
      rw [VRel_unfold]; simp only [vok] at Ok; simp only [VBody]
      have A := vrefl DW a n k w W Hw Ok.1; have B := vrefl DW d n k w W Hw Ok.2
      rw [VRel_unfold] at A B; exact ⟨A, B⟩
  | VVec l, n, k, w, W, Hw, Ok => by rw [VRel_unfold]; simp only [vok] at Ok; simp only [VBody]; exact Hw l Ok
  | VLam x b rho, n, k, w, W, Hw, Ok => by
      rw [VRel_unfold]; simp only [vok] at Ok; simp only [VBody]
      refine ⟨same_id_refl Ok Hw, ?_⟩
      cases k with
      | zero => intro j L; omega
      | succ k =>
        intro j L w' ⟨Iw', W'⟩ a0 a A
        simp only at A
        rw [VRelF_index k j (by omega)] at A
        exact body_of_fundamental F DW L W' (.cons ⟨rfl, A⟩
          (vrefl_env DW rho n j w' W' (fun l Ll => Iw' _ (Hw l Ll)) Ok))
  | VFrozen b rho, n, k, w, W, Hw, Ok => by
      rw [VRel_unfold]; simp only [vok] at Ok; simp only [VBody]
      refine ⟨same_id_refl Ok Hw, ?_⟩
      cases k with
      | zero => intro j L; omega
      | succ k =>
        intro j L w' ⟨Iw', W'⟩
        exact body_of_fundamental F DW L W' (vrefl_env DW rho n j w' W' (fun l Ll => Iw' _ (Hw l Ll)) Ok)
  | VPartial f args, n, k, w, W, Hw, Ok => by
      rw [VRel_unfold]; simp only [vok] at Ok; simp only [VBody]
      exact ⟨by trivial, vrefl_list DW args n k w W Hw Ok⟩
  | VNum _, _, k, _, _, _, _ | VSym _, _, k, _, _, _, _ | VBool _, _, k, _, _, _, _
  | VStr _, _, k, _, _, _, _ | VNil, _, k, _, _, _, _ | VStream _, _, k, _, _, _, _
  | VExn _, _, k, _, _, _, _ => by rw [VRel_unfold]; simp [VBody]
theorem vrefl_env (DW : D_wf sealed D) : ∀ (rho : lenv) (n k : Nat) (w : world), wf_world w →
    (∀ l, l < n → (l, l) ∈ w) → vok_env n rho → EnvRelAll sealed D k w rho rho
  | [], _, _, _, _, _, _ => .nil
  | (y, u) :: rr, n, k, w, W, Hw, Ok => by
      simp only [vok_env] at Ok
      exact .cons ⟨rfl, vrefl DW u n k w W Hw Ok.1⟩ (vrefl_env DW rr n k w W Hw Ok.2)
theorem vrefl_list (DW : D_wf sealed D) : ∀ (l : List value) (n k : Nat) (w : world), wf_world w →
    (∀ l, l < n → (l, l) ∈ w) → vok_list n l → VBody_list sealed D (Vbelow sealed D k) k w l l
  | [], _, _, _, _, _, _ => by simp [VBody_list]
  | x :: r, n, k, w, W, Hw, Ok => by
      simp only [vok_list] at Ok; simp only [VBody_list]
      have A := vrefl DW x n k w W Hw Ok.1; rw [VRel_unfold] at A
      exact ⟨A, vrefl_list DW r n k w W Hw Ok.2⟩
end

theorem store_refl_of_fundamental : store_refl_statement sealed D := by
  intro k s DW HS ⟨Hh, Hg⟩
  have Hw : ∀ l, l < s.heap.length → (l, l) ∈ id_world s := fun l L => mem_id_world.2 ⟨rfl, L⟩
  refine ⟨id_world_wf s, HS, HS, rfl, ?_, ?_⟩
  · have : ∀ (g : List (name × value)), (∀ p ∈ g, vok s.heap.length p.2) →
        Forall2 (fun p0 p => p0.1 = p.1 ∧ VRel sealed D k (id_world s) p0.2 p.2) g g := by
      intro g; induction g with
      | nil => intro _; exact .nil
      | cons p g ih =>
        intro H; exact .cons ⟨rfl, vrefl F DW p.2 _ k _ (id_world_wf s) Hw (H p (by simp))⟩
          (ih (fun q I => H q (by simp [I])))
    exact this _ Hg
  · intro l0 l I
    obtain ⟨E, L⟩ := mem_id_world.1 I; subst E
    obtain ⟨c, N⟩ : ∃ c, s.heap[l0]? = some c := ⟨_, List.getElem?_eq_getElem L⟩
    refine ⟨c, c, N, N, ?_⟩
    have Oc : lok s.heap.length c := Hh c (List.mem_of_getElem? N)
    have : ∀ (c : List value), lok s.heap.length c → Forall2 (VRel sealed D k (id_world s)) c c := by
      intro c; induction c with
      | nil => intro _; exact .nil
      | cons x c ih =>
        intro H; exact .cons (vrefl F DW x _ k _ (id_world_wf s) Hw (H x (by simp)))
          (ih (fun y I => H y (by simp [I])))
    exact this c Oc

theorem adequacy_of_fundamental : adequacy_statement sealed D := by
  intro g e0 e rho s DW HK Hfo Hdom HS Hok
  have Main : ∀ n t c', runs sealed n (Cfg (Eval rho e) [] s) t c' →
      ObsT sealed (n + 1) (id_world s) (Cfg (Eval rho e0) [] s) (Cfg (Eval rho e) [] s) := by
    intro n t c' _
    refine HK (n + 1) (id_world s) rho rho (id_world_wf s) ?_ (n + 1) (Nat.le_refl _) (id_world s)
      (wext_refl (id_world_wf s)) [] [] (KRel_top (n + 1) _ (id_world_wf s)) s s
      (store_refl_of_fundamental F (n + 1) s DW HS Hok)
    intro x Ix
    obtain ⟨v, Lv⟩ := Hdom x Ix
    exact ⟨v, v, Lv, Lv, vrefl F DW v 0 _ _ (id_world_wf s) (fun l L => absurd L (Nat.not_lt_zero _))
      (fo_vok (Hfo (x, v) (lookup_In Lv)))⟩
  constructor
  · intro v s' Hr Fv
    obtain ⟨n, Hn⟩ := srun_runs Hr
    obtain ⟨A, _⟩ := Main _ _ _ Hn n [] _ (Nat.lt_succ_self n) Hn
    obtain ⟨v0, s0, w', S0, Wx, Gv, Gs⟩ := A v s' rfl
    rw [GVal_fo Fv Gv] at S0
    exact ⟨s0, w', S0, Wx, Gs⟩
  · intro x s' Hr
    obtain ⟨n, Hn⟩ := srun_runs Hr
    obtain ⟨_, B, _⟩ := Main _ _ _ Hn n [] _ (Nat.lt_succ_self n) Hn
    obtain ⟨s0, w', S0, Wx, Gs⟩ := B x s' rfl
    exact ⟨s0, w', S0, Wx, Gs⟩
end FromFundamental
end Proofs
end JitLowerEquiv
