import LeanJit.JitLowerRel
import LeanJit.JitMeta
/-! Port of `rocq/JitLowerKont.v`: the continuation relation, and stack facts. -/
namespace JitLowerKont
open KLSyntax KLValue KLSemantics KLSemantics.frame JitLowerRel JitLowerRel.dest
open JitBytecode (Pos tree val code cont operand instr)

-- ---------- stack facts ----------
def slotv (st : tree val) (a : Nat) : Option val := JitBytecode.tget (JitBytecode.skey a) st

theorem skey_inj {a b : Nat} (H : JitBytecode.skey a = JitBytecode.skey b) : a = b := by
  simp [JitBytecode.skey] at H; exact H
theorem slotv_same (st : tree val) (a : Nat) (v : val) : slotv (JitBytecode.tset (JitBytecode.skey a) v st) a = some v :=
  JitMeta.tget_tset_same _ _ _
theorem slotv_other (st : tree val) (a b : Nat) (v : val) (H : a ≠ b) :
    slotv (JitBytecode.tset (JitBytecode.skey b) v st) a = slotv st a :=
  JitMeta.tget_tset_other _ _ _ _ (fun E => H (skey_inj E))

def MEnv (fp : Nat) (st : tree val) (g : env) (rho : lenv) : Prop :=
  ∀ x s, lookup x g = some s → ∃ v v', lookup x rho = some v ∧ slotv st (fp + s) = some v' ∧ VR v v'
def EnvBelow (g : env) (top : Nat) := ∀ x s, lookup x g = some s → s < top
def Prot (g : env) (fp : Nat) (w : Nat → Prop) := ∀ x s, lookup x g = some s → ¬ w (fp + s)
def Above (fp top : Nat) (w : Nat → Prop) := ∀ a, fp + top ≤ a → w a
def Sub (w w1 : Nat → Prop) := ∀ a, w a → w1 a

def read_o (c : code) (fp : Nat) (st : tree val) (o : operand) : Option val :=
  match o with
  | .OSlot s => slotv st (fp + s)
  | .OConst k => (JitBytecode.code_consts c)[k]?
def o_safe (fp : Nat) (w : Nat → Prop) (o : operand) : Prop :=
  match o with | .OSlot s => ¬ w (fp + s) | .OConst _ => True
def o_below (top : Nat) (o : operand) : Prop :=
  match o with | .OSlot s => s < top | .OConst _ => True

inductive DoneR (c : code) (fp : Nat) (st : tree val) : List value → List operand → Prop
  | DR_nil : DoneR c fp st [] []
  | DR_cons {v v' o vs os} : read_o c fp st o = some v' → VR v v' → DoneR c fp st vs os →
      DoneR c fp st (v :: vs) (o :: os)

inductive ArgsAt (st : tree val) : Nat → List value → Prop
  | AA_nil a : ArgsAt st a []
  | AA_cons {a v v' vs} : slotv st a = some v' → VR v v' → ArgsAt st (a + 1) vs → ArgsAt st a (v :: vs)

def loc : List (Nat × Nat) → Nat → Nat
  | [], i => i
  | (s, t) :: ms, i => if s == i then t else loc ms i

inductive ParamAt (fp : Nat) (st : tree val) (ms : List (Nat × Nat)) : Nat → List value → Prop
  | PA_nil i : ParamAt fp st ms i []
  | PA_cons {i v v' vs} : slotv st (fp + loc ms i) = some v' → VR v v' →
      ParamAt fp st ms (i + 1) vs → ParamAt fp st ms i (v :: vs)

mutual
inductive KD : code → Nat → tree val → List cont → (Nat → Prop) → operand → List instr → List frame → Prop
  | KD_ret {c fp st cs w o r k} : Sub w (fun a => fp ≤ a) → RK fp st cs k →
      KD c fp st cs w o (.IReturn o :: r) k
  | KD_jump {c fp st cs w o e r r1 k} : lbl c e = some r1 → KD c fp st cs w o r1 k →
      KD c fp st cs w o (.IJump e :: r) k
  | KD_label {c fp st cs w o l r k} : KD c fp st cs w o r k → KD c fp st cs w o (.ILabel l :: r) k
  | KD_let {c fp st cs w d r x b rho k1 g top dst r2 w1} :
      MEnv fp st g rho → Prot g fp w → EnvBelow g top → d < top →
      Comp c ((x, d) :: g) top b dst r r2 → Sub w w1 → Above fp top w1 →
      KC c fp st cs w1 dst r2 k1 →
      KD c fp st cs w (.OSlot d) r (KLet x b rho :: k1)
  | KD_lett {c fp st cs w d r x b rho k1 g top l r2 w1} :
      MEnv fp st g rho → Prot g fp w → EnvBelow g top → d < top →
      CompT c ((x, d) :: g) top b l r r2 → Sub w w1 → Above fp top w1 →
      TK c fp st cs w1 true l r2 k1 →
      KD c fp st cs w (.OSlot d) r (KLet x b rho :: k1)
  | KD_test {c fp st cs w o l r k} : TK c fp st cs w true l r k →
      KD c fp st cs w o (.IJumpIfFalse o l :: r) k
  | KD_prim {c fp st cs w o r f p q vals es rho k1 g top ops dops d r1 w1} :
      prim_of_name f = some p → pmap p = some q →
      vals.length + 1 + es.length = prim_arity p →
      MEnv fp st g rho → Prot g fp w → EnvBelow g top →
      CompOps c g top es ops r (.IPrim d q (dops.reverse ++ o :: ops) :: r1) →
      DoneR c fp st vals dops → (∀ x ∈ dops, o_safe fp w x) →
      (∀ x ∈ dops, o_below top x) → o_below top o →
      Sub w w1 → Above fp top w1 → w1 (fp + d) → KD c fp st cs w1 (.OSlot d) r1 k1 →
      KD c fp st cs w o r (KCallArgs f vals es rho :: k1)
  | KD_call {c fp st cs w r f vals es rho k1 g a s d n i r1 w1} :
      not_prim_name f → s = a + 2 + vals.length →
      n = vals.length + 1 + es.length →
      MEnv fp st g rho → Prot g fp w → EnvBelow g (s + 1) →
      CompW c g (s + 1) es r (i :: r1) → call_instr i d a (JitBytecode.sym_of_text f) n →
      ArgsAt st (fp + a + 2) vals.reverse → Sub w (fun x => fp + s ≤ x) →
      Sub w w1 → Above fp a w1 → w1 (fp + d) → KD c fp st cs w1 (.OSlot d) r1 k1 →
      KD c fp st cs w (.OSlot s) r (KCallArgs f vals es rho :: k1)
  | KD_tail {c fp st cs w o r f vals es rho k1 g s t t0 ms n i r1} :
      not_prim_name f → s = 2 + vals.length →
      n = vals.length + 1 + es.length → n + 2 ≤ t0 → t0 ≤ t →
      MEnv fp st g rho → Prot g fp w → EnvBelow g t →
      CompTA c g (s + 1) t es ms r (i :: r1) → tail_instr i 0 (JitBytecode.sym_of_text f) n →
      o = .OSlot (loc ms s) → loc ms s < t →
      (∀ m ∈ ms, (2 ≤ m.1 ∧ m.1 < s + 1) ∧ (n + 2 ≤ m.2 ∧ m.2 < t)) → (ms.map Prod.fst).Nodup →
      (∀ j, 2 ≤ j ∧ j < s → loc ms j = j ∨ (n + 2 ≤ loc ms j ∧ loc ms j < t0)) →
      ParamAt fp st ms 2 vals.reverse →
      Sub w (fun x => x = fp + s ∨ fp + t0 ≤ x) → RK fp st cs k1 →
      KD c fp st cs w o r (KCallArgs f vals es rho :: k1)

inductive TK : code → Nat → tree val → List cont → (Nat → Prop) → Bool → Nat → List instr → List frame → Prop
  | TK_if {c fp st cs w l r a b rho k1 g top dst r2 r3 r4 w1} :
      MEnv fp st g rho → Prot g fp w → EnvBelow g top →
      Comp c g top a dst r r2 → lbl c l = some r3 → Comp c g top b dst r3 r4 →
      Sub w w1 → Above fp top w1 → KC c fp st cs w1 dst r2 k1 → KC c fp st cs w1 dst r4 k1 →
      TK c fp st cs w true l r (KIf a b rho :: k1)
  | TK_cond {c fp st cs w l r a rest rho k1 g top dst r2 r3 r4 w1} :
      MEnv fp st g rho → Prot g fp w → EnvBelow g top →
      Comp c g top a dst r r2 → lbl c l = some r3 → Comp c g top (.ECond rest) dst r3 r4 →
      Sub w w1 → Above fp top w1 → KC c fp st cs w1 dst r2 k1 → KC c fp st cs w1 dst r4 k1 →
      TK c fp st cs w true l r (KCond a rest rho :: k1)
  | TK_and {c fp st cs w gd l r y rho k1 g top r2 w1} :
      MEnv fp st g rho → Prot g fp w → EnvBelow g top →
      CompT c g top y l r r2 → Sub w w1 → Above fp top w1 →
      TK c fp st cs w1 gd l r2 k1 →
      TK c fp st cs w true l r (KAnd y rho :: k1)
  | TK_andr {c fp st cs w gd l r k1 w1} : Sub w w1 → TK c fp st cs w1 gd l r k1 →
      TK c fp st cs w true l r (KAndR :: k1)
  | TK_or {c fp st cs w gd l nx r1 y rho k1 g top r2 r3 w1} :
      MEnv fp st g rho → Prot g fp w → EnvBelow g top →
      lbl c nx = some r2 → CompT c g top y l r2 r3 → Sub w w1 → Above fp top w1 →
      TK c fp st cs w1 gd l r3 k1 → TK c fp st cs w1 gd l r1 k1 →
      TK c fp st cs w true nx r1 (KOr y rho :: k1)
  | TK_orr {c fp st cs w gd l r k1 w1} : Sub w w1 → TK c fp st cs w1 gd l r k1 →
      TK c fp st cs w true l r (KOrR :: k1)
  | TK_jump {c fp st cs w gd l e r r1 k} : lbl c e = some r1 → TK c fp st cs w gd l r1 k →
      TK c fp st cs w gd l (.IJump e :: r) k
  | TK_label {c fp st cs w gd l x r k} : TK c fp st cs w gd l r k →
      TK c fp st cs w gd l (.ILabel x :: r) k
  | TK_value {c fp st cs w l d kt kf r2 r4 k w1} :
      konst c kt = some (.VBool true) → konst c kf = some (.VBool false) →
      lbl c l = some (.IConst d kf :: r4) → Sub w w1 → w1 (fp + d) →
      KD c fp st cs w1 (.OSlot d) r2 k → KD c fp st cs w1 (.OSlot d) r4 k →
      TK c fp st cs w false l (.IConst d kt :: r2) k

inductive KC : code → Nat → tree val → List cont → (Nat → Prop) → dest → List instr → List frame → Prop
  | KC_ret {c fp st cs w r k} : Sub w (fun a => fp ≤ a) → RK fp st cs k → KC c fp st cs w DRet r k
  | KC_slot {c fp st cs w d r k} : w (fp + d) → KD c fp st cs w (.OSlot d) r k →
      KC c fp st cs w (DSlot d) r k

inductive RK : Nat → tree val → List cont → List frame → Prop
  | RK_top {fp st} : RK fp st [] []
  | RK_call {fp st c r d a cs k w} : a ≤ fp → Above (fp - a) a w →
      KD c (fp - a) st cs w (.OSlot d) r k → w (fp - a + d) →
      RK fp st (cont.Cont c r d a :: cs) k
end

end JitLowerKont
