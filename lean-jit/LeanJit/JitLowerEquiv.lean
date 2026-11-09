import LeanJit.JitLowerCheck
/-! Port of `rocq/JitLowerEquiv.v` at commit 670d29d (branch pass/equiv): the step-indexed
Kripke relation `KRef` for the lowerer's front passes, its statements, and the implications
proved there. `call_preservation_src_statement` and its proof are not ported: they need
`JitLowerThm.call_preservation` (see Unported.lean). -/
namespace JitLowerEquiv
open Observation KLSyntax KLSyntax.expr KLValue KLValue.value KLSemantics KLSemantics.control
open KLSemantics.move KLSemantics.config KLPort JitProfile JitLowerRel

/-- Rocq's `Forall2` (core Lean has no relational list zip). -/
inductive Forall2 {A B : Type} (R : A → B → Prop) : List A → List B → Prop
  | nil : Forall2 R [] []
  | cons {a b l1 l2} : R a b → Forall2 R l1 l2 → Forall2 R (a :: l1) (b :: l2)

theorem Forall2_impl {A B} {R1 R2 : A → B → Prop} (H : ∀ a b, R1 a b → R2 a b) :
    ∀ {l1 l2}, Forall2 R1 l1 l2 → Forall2 R2 l1 l2
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (H _ _ h) (Forall2_impl H t)

section Equiv
variable (sealed : List name) (D : List (name × fundef))

/-- `JitLowerStep.Sstar` (JitLowerStep.v is not ported; this one inductive is). -/
inductive Sstar : config → config → Prop
  | SS_refl c : Sstar c c
  | SS_step c c1 c2 : step_r (jit_rules sealed) jit_profile c .Tau c1 → Sstar c1 c2 → Sstar c c2

-- ---------- runs ----------
inductive runs : Nat → config → trace → config → Prop
  | runs_0 c : runs 0 c [] c
  | runs_S n c l c1 t c2 : step_r (jit_rules sealed) jit_profile c l c1 → runs n c1 t c2 →
      runs (n + 1) c (trace_of l ++ t) c2

def srun (c : config) (t : trace) (c' : config) : Prop := star (step_r (jit_rules sealed) jit_profile) c t c'

-- ---------- worlds ----------
abbrev world := List (Nat × Nat)
def wf_world (w : world) : Prop := (w.map Prod.fst).Nodup ∧ (w.map Prod.snd).Nodup
def incl {A} (l1 l2 : List A) : Prop := ∀ a ∈ l1, a ∈ l2
def wext (w w' : world) : Prop := incl w w' ∧ wf_world w'

def same_id (w : world) (r0 r : lenv) : Prop :=
  match closure_id r0, closure_id r with
  | some l0, some l => (l0, l) ∈ w
  | none, none => True
  | _, _ => False

def StoreHas (s : store) : Prop := ∀ f d, (f, d) ∈ D → lookup f s.gfuns = some d

-- ---------- the ground relation ----------
mutual
def GVal (w : world) : value → value → Prop
  | VNum a, VNum b => a = b
  | VSym a, VSym b => a = b
  | VBool a, VBool b => a = b
  | VStr a, VStr b => a = b
  | VNil, VNil => True
  | VCons a0 d0, VCons a d => GVal w a0 a ∧ GVal w d0 d
  | VVec l0, VVec l => (l0, l) ∈ w
  | VStream h0, VStream h => h0 = h
  | VLam _ _ r0, VLam _ _ r => same_id w r0 r
  | VFrozen _ r0, VFrozen _ r => same_id w r0 r
  | VPartial f0 as0, VPartial f as1 => f0 = f ∧ GVal_list w as0 as1
  | VExn x0, VExn x => x0 = x
  | _, _ => False
def GVal_list (w : world) : List value → List value → Prop
  | [], [] => True
  | x0 :: r0, x :: r => GVal w x0 x ∧ GVal_list w r0 r
  | _, _ => False
end

def GStore (w : world) (s0 s : store) : Prop :=
  s0.gfuns = s.gfuns ∧
  Forall2 (fun p0 p => p0.1 = p.1 ∧ GVal w p0.2 p.2) s0.gvals s.gvals ∧
  (∀ l0 l, (l0, l) ∈ w → ∃ c0 c, s0.heap[l0]? = some c0 ∧ s.heap[l]? = some c ∧ Forall2 (GVal w) c0 c)

-- ---------- observation ----------
def ObsT (k : Nat) (w : world) (c0 c : config) : Prop :=
  ∀ n t c', n < k → runs sealed n c t c' →
   (∀ v s, c' = Cfg (Ret v) [] s → ∃ v0 s0 w',
      srun sealed c0 t (Cfg (Ret v0) [] s0) ∧ wext w w' ∧ GVal w' v0 v ∧ GStore w' s0 s) ∧
   (∀ x s, c' = Cfg (Throw x) [] s → ∃ s0 w',
      srun sealed c0 t (Cfg (Throw x) [] s0) ∧ wext w w' ∧ GStore w' s0 s) ∧
   (∀ why, next_r (jit_rules sealed) jit_profile c' = MWrong why → ∃ c0' why0,
      srun sealed c0 t c0' ∧ next_r (jit_rules sealed) jit_profile c0' = MWrong why0)

-- ---------- the logical relation, generic in the value relation at lower indices ----------
section Gen
variable (V : Nat → world → value → value → Prop)

def SRel_with (V1 : world → value → value → Prop) (w : world) (s0 s : store) : Prop :=
  wf_world w ∧ StoreHas D s0 ∧ StoreHas D s ∧ s0.gfuns = s.gfuns ∧
  Forall2 (fun p0 p => p0.1 = p.1 ∧ V1 w p0.2 p.2) s0.gvals s.gvals ∧
  (∀ l0 l, (l0, l) ∈ w → ∃ c0 c, s0.heap[l0]? = some c0 ∧ s.heap[l]? = some c ∧ Forall2 (V1 w) c0 c)

def EnvRel_with (V1 : world → value → value → Prop) (w : world) (g : List name) (rho0 rho : lenv) : Prop :=
  ∀ x ∈ g, ∃ v0 v, lookup x rho0 = some v0 ∧ lookup x rho = some v ∧ V1 w v0 v

def KRel_with (k : Nat) (w : world) (K0 K : List frame) : Prop :=
  ∀ j, j ≤ k → ∀ w', wext w w' →
   (∀ v0 v s0 s, V j w' v0 v → SRel_with D (V j) w' s0 s → ObsT sealed j w' (Cfg (Ret v0) K0 s0) (Cfg (Ret v) K s)) ∧
   (∀ x s0 s, SRel_with D (V j) w' s0 s → ObsT sealed j w' (Cfg (Throw x) K0 s0) (Cfg (Throw x) K s))

def ERel_with (k : Nat) (w : world) (rho0 : lenv) (e0 : expr) (rho : lenv) (e : expr) : Prop :=
  ∀ j, j ≤ k → ∀ w', wext w w' → ∀ K0 K, KRel_with sealed D V j w' K0 K →
   ∀ s0 s, SRel_with D (V j) w' s0 s → ObsT sealed j w' (Cfg (Eval rho0 e0) K0 s0) (Cfg (Eval rho e) K s)

mutual
def VBody (k : Nat) (w : world) : value → value → Prop
  | VNum a, VNum b => a = b
  | VSym a, VSym b => a = b
  | VBool a, VBool b => a = b
  | VStr a, VStr b => a = b
  | VNil, VNil => True
  | VCons a0 d0, VCons a d => VBody k w a0 a ∧ VBody k w d0 d
  | VVec l0, VVec l => (l0, l) ∈ w
  | VStream h0, VStream h => h0 = h
  | VLam x0 b0 r0, VLam x b r => same_id w r0 r ∧
      ∀ j, j < k → ∀ w', wext w w' → ∀ a0 a, V j w' a0 a →
        ERel_with sealed D V j w' ((x0, a0) :: r0) b0 ((x, a) :: r) b
  | VFrozen b0 r0, VFrozen b r => same_id w r0 r ∧
      ∀ j, j < k → ∀ w', wext w w' → ERel_with sealed D V j w' r0 b0 r b
  | VPartial f0 as0, VPartial f as1 => f0 = f ∧ VBody_list k w as0 as1
  | VExn x0, VExn x => x0 = x
  | _, _ => False
def VBody_list (k : Nat) (w : world) : List value → List value → Prop
  | [], [] => True
  | x0 :: r0, x :: r => VBody k w x0 x ∧ VBody_list k w r0 r
  | _, _ => False
end
end Gen

def VRelF : Nat → Nat → world → value → value → Prop
  | 0 => fun _ => VBody sealed D (fun _ _ _ _ => False) 0
  | k + 1 => fun j => if Nat.ble j k then VRelF k j else VBody sealed D (VRelF k) (k + 1)

def VRel (k : Nat) : world → value → value → Prop := VRelF sealed D k k
def SRel (k : Nat) : world → store → store → Prop := SRel_with D (VRel sealed D k)
def KRel (k : Nat) : world → List frame → List frame → Prop := KRel_with sealed D (VRelF sealed D k) k
def ERel (k : Nat) : world → lenv → expr → lenv → expr → Prop := ERel_with sealed D (VRelF sealed D k) k

-- ---------- KRef ----------
def KRef (g : List name) (e0 e : expr) : Prop :=
  ∀ k w rho0 rho, wf_world w → EnvRel_with (VRel sealed D k) w g rho0 rho → ERel sealed D k w rho0 e0 rho e

def D_wf : Prop := (∀ p ∈ D, p.1 ∈ sealed) ∧ (D.map Prod.fst).Nodup

def id_world (s : store) : world := (List.range s.heap.length).map (fun l => (l, l))

-- ---------- statements ----------
def VRelF_index_statement : Prop := ∀ k j, j ≤ k → VRelF sealed D k j = VRel sealed D j
def VRel_ground_statement : Prop := ∀ k w v0 v, VRel sealed D k w v0 v → GVal w v0 v
def SRel_ground_statement : Prop := ∀ k w s0 s, SRel sealed D k w s0 s → GStore w s0 s
def KRel_top_statement : Prop := ∀ k w, wf_world w → KRel sealed D k w [] []
def EnvRelAll (k : Nat) (w : world) (rho0 rho : lenv) : Prop :=
  Forall2 (fun p0 p => p0.1 = p.1 ∧ VRel sealed D k w p0.2 p.2) rho0 rho
def fundamental_statement : Prop := ∀ k w rho0 rho e,
  D_wf sealed D → wf_world w → EnvRelAll sealed D k w rho0 rho → ERel sealed D k w rho0 e rho e
def store_refl_statement : Prop := ∀ k s,
  D_wf sealed D → StoreHas D s → store_ok s → SRel sealed D k (id_world s) s s
def compat_let_statement : Prop := ∀ g x a0 a b0 b,
  KRef sealed D g a0 a → KRef sealed D (x :: g) b0 b → KRef sealed D g (ELet x a0 b0) (ELet x a b)
def compat_if_statement : Prop := ∀ g c0 c a0 a b0 b,
  KRef sealed D g c0 c → KRef sealed D g a0 a → KRef sealed D g b0 b → KRef sealed D g (EIf c0 a0 b0) (EIf c a b)
def compat_type_statement : Prop := ∀ g a0 a, KRef sealed D g a0 a → KRef sealed D g (EType a0) (EType a)

inductive fo : value → Prop
  | fo_num n : fo (VNum n) | fo_sym x : fo (VSym x) | fo_bool b : fo (VBool b)
  | fo_str t : fo (VStr t) | fo_nil : fo VNil | fo_cons a d : fo a → fo d → fo (VCons a d)

def adequacy_statement : Prop := ∀ g e0 e rho s,
  D_wf sealed D → KRef sealed D g e0 e → (∀ p ∈ rho, fo p.2) → (∀ x ∈ g, ∃ v, lookup x rho = some v) →
  StoreHas D s → store_ok s →
  (∀ v s', srun sealed (Cfg (Eval rho e) [] s) [] (Cfg (Ret v) [] s') → fo v →
     ∃ s0 w, srun sealed (Cfg (Eval rho e0) [] s) [] (Cfg (Ret v) [] s0) ∧ wext (id_world s) w ∧ GStore w s0 s') ∧
  (∀ x s', srun sealed (Cfg (Eval rho e) [] s) [] (Cfg (Throw x) [] s') →
     ∃ s0 w, srun sealed (Cfg (Eval rho e0) [] s) [] (Cfg (Throw x) [] s0) ∧ wext (id_world s) w ∧ GStore w s0 s')

def srun_nil_Sstar_statement : Prop := ∀ c c', srun sealed c [] c' ↔ Sstar sealed c c'

end Equiv
end JitLowerEquiv
