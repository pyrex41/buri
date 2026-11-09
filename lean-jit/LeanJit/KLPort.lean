import LeanJit.KLSemantics
/-! Port of `rocq/KLPort.v`: per-port options on the KLambda semantics. -/
namespace KLPort
open Observation KLSyntax KLSyntax.prim KLSyntax.expr KLValue KLValue.value KLValue.exn
open KLSemantics KLSemantics.pout KLSemantics.presult KLSemantics.frame KLSemantics.control
open KLSemantics.move KLSemantics.config

structure port_rules where
  int_range : Option (Int × Int)
  char_ok : Int → Bool
  object_identity : Bool
  arity_errors : Bool
  defun_allowed : store → name → Bool
  time_kind_ok : text → Bool
  unchecked_writes : Bool
  resource_exn : resource → Option exn

def agreed_rules : port_rules :=
  ⟨none, scalar_ok, false, false, fun _ _ => true, fun _ => true, false, fun _ => none⟩

-- ---------- 1: integer range ----------
def in_range (R : port_rules) (z : Int) : Bool := match R.int_range with
  | none => true
  | some (lo, hi) => decide (lo ≤ z) && decide (z ≤ hi)

def rule_arith_r (R : port_rules) (P : profile) (p : prim) (iop : Int → Int → Int) (args : List value) (s : store) :=
  match args with
  | [VNum (.NInt x), VNum (.NInt y)] =>
    if in_range R (iop x y) then rule_arith P p iop args s else dom p
  | _ => rule_arith P p iop args s

def rule_div_r (R : port_rules) (P : profile) (args : List value) (s : store) := match args with
  | [VNum (.NInt x), VNum (.NInt y)] =>
    if !(y == 0) && (Int.tmod x y == 0) && !(in_range R (Int.tdiv x y))
    then dom PDiv else rule_div P args s
  | _ => rule_div P args s

-- ---------- 2: characters ----------
def rule_n_to_string_r (R : port_rules) (args : List value) (s : store) := match args with
  | [VNum (.NInt z)] => if R.char_ok z then ret (VStr [z.toNat]) s else dom PNToString
  | _ => dom PNToString

-- ---------- 3: identity ----------
def id_key : name := [0, 105, 100]
def closure_id (rho : lenv) : Option Nat := match rho with
  | (k, VVec l) :: _ => if text_eqb k id_key then some l else none
  | _ => none

def opaque_eq (a b : value) : Option Bool := match a, b with
  | VLam _ _ r1, VLam _ _ r2 | VFrozen _ r1, VFrozen _ r2 =>
    match closure_id r1, closure_id r2 with
    | some x, some y => some (x == y)
    | _, _ => none
  | VLam _ _ _, VFrozen _ _ | VFrozen _ _, VLam _ _ _ => some false
  | _, _ => none

def eq_opaque_r (R : port_rules) (a b : value) : Option Bool :=
  if R.object_identity then opaque_eq a b else none

/-- KLPort's own copy of the inner loop of `=`, as in Rocq (a drift from KLValue stops
`eq_depth_r_agreed`). -/
def eq_go_r (R : port_rules) (P : profile) (h : List (List value)) (rec : value → value → Option Bool) :
    value → value → Option Bool
  | VNum x, VNum y => some (num_cmp P PEqual x y)
  | VSym x, VSym y => some (text_eqb x y)
  | VStr x, VStr y => some (text_eqb x y)
  | VBool x, VBool y => some (x == y)
  | VNil, VNil => some true
  | VCons a1 a2, VCons b1 b2 => match eq_go_r R P h rec a1 b1 with
    | some true => eq_go_r R P h rec a2 b2
    | r => r
  | VStream x, VStream y => some (x == y)
  | VVec l1, VVec l2 => if l1 == l2 then some true else
      match h[l1]?, h[l2]? with
      | some xs, some ys => list_eq rec xs ys
      | _, _ => none
  | a, b => if is_opaque a then (if is_opaque b then eq_opaque_r R a b else some false) else some false

def eq_depth_r (R : port_rules) (P : profile) (h : List (List value)) : Nat → value → value → Option Bool
  | 0 => fun _ _ => none
  | d + 1 => eq_go_r R P h (eq_depth_r R P h d)
def kl_eq_r (R : port_rules) (P : profile) (h : List (List value)) (a b : value) :=
  eq_depth_r R P h (h.length + 1) a b

def rule_equal_r (R : port_rules) (P : profile) (args : List value) (s : store) := match args with
  | [a, b] => match kl_eq_r R P s.heap a b with
    | some r => ret (VBool r) s | none => PDone (OWrong (kw "equality-undefined"))
  | _ => dom PEqual

def tagged_env (rho : lenv) (s : store) : lenv := (id_key, VVec s.heap.length) :: rho
def with_cell (s : store) : store := ⟨s.heap ++ [[]], s.gvals, s.gfuns⟩

-- ---------- 6 and 7: clock and writes ----------
def rule_get_time_r (R : port_rules) (P : profile) (args : List value) (s : store) := match args with
  | [VSym k] => if R.time_kind_ok k then rule_get_time P args s else dom PGetTime
  | _ => rule_get_time P args s

def rule_write_byte_r (R : port_rules) (args : List value) (s : store) :=
  if R.unchecked_writes then match args with
    | [VNum (.NInt b), VStream h] => if decide (0 ≤ b) && decide (b < 256)
      then PIO (.QWrite h [b.toNat]) (fun _ => ORet (VNum (.NInt b)) s)
      else dom PWriteByte
    | _ => dom PWriteByte
  else rule_write_byte args s

def prim_rule_r (R : port_rules) (P : profile) (p : prim) (args : List value) (s : store) : presult :=
  match p with
  | PNToString => rule_n_to_string_r R args s
  | PEqual => rule_equal_r R P args s
  | PWriteByte => rule_write_byte_r R args s
  | PGetTime => rule_get_time_r R P args s
  | PAdd => rule_arith_r R P PAdd (· + ·) args s
  | PSub => rule_arith_r R P PSub (· - ·) args s
  | PMul => rule_arith_r R P PMul (· * ·) args s
  | PDiv => rule_div_r R P args s
  | _ => prim_rule P p args s

-- ---------- machine ----------
def prim_move_r (R : port_rules) (P : profile) (p : prim) (args rest : List value) (k : List frame) (s : store) : move :=
  match prim_rule_r R P p args s with
  | PDone o => MTau (pout_config P o rest k s)
  | PIO q kont => MIO q (fun r => pout_config P (kont r) rest k s)

def arity_mismatch (R : port_rules) (gv want : Nat) : Bool :=
  R.arity_errors && !(gv == want)

def call_named_r (R : port_rules) (P : profile) (g : name) (args : List value) (k : List frame) (s : store) : move :=
  match lookup g s.gfuns with
  | none => MTau (Cfg (Throw (XUndefinedFun g)) k s)
  | some (.FUser ps body) =>
    if arity_mismatch R args.length ps.length then MTau (Cfg (Throw XArity) k s)
    else if decide (args.length < ps.length) then MTau (Cfg (Ret (VPartial g args)) k s)
    else MTau (continue_with P (args.drop ps.length) k (Eval (ps.zip (args.take ps.length)) body) s)
  | some (.FPrim p) =>
    if arity_mismatch R args.length (prim_arity p) then MTau (Cfg (Throw XArity) k s)
    else if decide (args.length < prim_arity p) then MTau (Cfg (Ret (VPartial g args)) k s)
    else prim_move_r R P p (args.take (prim_arity p)) (args.drop (prim_arity p)) k s

def apply_value_r (R : port_rules) (P : profile) (f : value) (args : List value) (k : List frame) (s : store) : move :=
  match f, args with
  | VFrozen body rho, [] => MTau (Cfg (Eval rho body) k s)
  | VLam x body rho, a :: rest => MTau (continue_with P rest k (Eval ((x, a) :: rho) body) s)
  | VPartial g prev, _ => call_named_r R P g (prev ++ args) k s
  | VFrozen _ _, _ :: _ | VLam _ _ _, [] => MTau (Cfg (Throw XArity) k s)
  | _, _ => MTau (Cfg (Throw XNotCallable) k s)

def eval_move_r (R : port_rules) (P : profile) (rho : lenv) (e : expr) (k : List frame) (s : store) : move :=
  match e with
  | ELam x b => if R.object_identity
      then MTau (Cfg (Ret (VLam x b (tagged_env rho s))) k (with_cell s))
      else MTau (Cfg (Ret (VLam x b rho)) k s)
  | EFreeze b => if R.object_identity
      then MTau (Cfg (Ret (VFrozen b (tagged_env rho s))) k (with_cell s))
      else MTau (Cfg (Ret (VFrozen b rho)) k s)
  | EDefun f ps b =>
    if R.defun_allowed s f then
      if nodupb ps then
        MTau (Cfg (Ret (VSym f)) k ⟨s.heap, s.gvals, (f, .FUser ps b) :: s.gfuns⟩)
      else MTau (Cfg (Throw XBadDefinition) k s)
    else MTau (Cfg (Throw XBadDefinition) k s)
  | ECall f [] => call_named_r R P f [] k s
  | _ => eval_move P rho e k s

def ret_move_r (R : port_rules) (P : profile) (v : value) (f : frame) (k : List frame) (s : store) : move :=
  match f with
  | KHead [] _ => apply_value_r R P v [] k s
  | KArgs fv done [] _ => apply_value_r R P fv (v :: done).reverse k s
  | KCallArgs g done [] _ => call_named_r R P g (v :: done).reverse k s
  | KApply args => apply_value_r R P v args k s
  | _ => ret_move P v f k s

def next_r (R : port_rules) (P : profile) (c : config) : move :=
  match c.ctl with
  | Eval rho e => eval_move_r R P rho e c.kont c.mem
  | Ret v => match c.kont with | [] => MFinal (.Normal v) | f :: k => ret_move_r R P v f k c.mem
  | Throw x => match c.kont with | [] => MFinal (.Error x) | f :: k => throw_move x f k c.mem
  | Fail r => match R.resource_exn r with
    | some x => MTau (Cfg (Throw x) c.kont c.mem)
    | none => MFinal (.ResourceOut r)
  | Halted (.Signal sg) => MFinal (.Killed sg)
  | Halted .Cancel => MFinal .Cancelled
  | Wrong w => MWrong w

def running_state (c : config) : Bool := match c.ctl with
  | Eval _ _ | Ret _ => true | _ => false

inductive step_r (R : port_rules) (P : profile) : config → label → config → Prop
  | step_r_tau c c' : next_r R P c = MTau c' → step_r R P c .Tau c'
  | step_r_io c q kk r : next_r R P c = MIO q kk → step_r R P c (.Obs (.EvIO q r)) (kk r)
  | step_r_resource c r x :
      running_state c = true → R.resource_exn r = some x →
      step_r R P c .Tau (Cfg (Throw x) c.kont c.mem)

-- ---------- the agreed options are exactly the agreed semantics ----------
theorem eq_go_r_agreed (P : profile) (h : List (List value)) (rec : value → value → Option Bool) :
    ∀ a b, eq_go_r agreed_rules P h rec a b = eq_go P h rec a b
  | VCons a1 a2, b => by
      cases b <;> simp only [eq_go_r, eq_go, eq_go_r_agreed P h rec a1, eq_go_r_agreed P h rec a2] <;> rfl
  | VNum _, b | VSym _, b | VBool _, b | VStr _, b | VNil, b | VVec _, b | VStream _, b
  | VLam _ _ _, b | VFrozen _ _, b | VPartial _ _, b | VExn _, b => by cases b <;> rfl

theorem eq_depth_r_agreed (P : profile) (h : List (List value)) :
    ∀ d a b, eq_depth_r agreed_rules P h d a b = eq_depth P h d a b
  | 0, _, _ => rfl
  | d + 1, a, b => by
    have E : eq_depth_r agreed_rules P h d = eq_depth P h d :=
      funext fun x => funext fun y => eq_depth_r_agreed P h d x y
    simp only [eq_depth_r, eq_depth, E, eq_go_r_agreed]

theorem kl_eq_r_agreed (P : profile) (h : List (List value)) (a b : value) :
    kl_eq_r agreed_rules P h a b = kl_eq P h a b := eq_depth_r_agreed P h _ a b

theorem in_range_agreed (z : Int) : in_range agreed_rules z = true := rfl

theorem rule_equal_agreed (P : profile) (args : List value) (s : store) :
    rule_equal_r agreed_rules P args s = rule_equal P args s := by
  unfold rule_equal_r rule_equal; split <;> simp only [kl_eq_r_agreed] <;> rfl
theorem rule_get_time_agreed (P : profile) (args : List value) (s : store) :
    rule_get_time_r agreed_rules P args s = rule_get_time P args s := by
  unfold rule_get_time_r; split <;> rfl
theorem rule_arith_agreed (P : profile) (p : prim) (iop : Int → Int → Int) (args : List value) (s : store) :
    rule_arith_r agreed_rules P p iop args s = rule_arith P p iop args s := by
  unfold rule_arith_r; split <;> rfl
theorem rule_div_agreed (P : profile) (args : List value) (s : store) :
    rule_div_r agreed_rules P args s = rule_div P args s := by
  unfold rule_div_r; split <;> simp [in_range_agreed]
theorem rule_n_to_string_agreed (args : List value) (s : store) :
    rule_n_to_string_r agreed_rules args s = rule_n_to_string args s := rfl
theorem rule_write_byte_agreed (args : List value) (s : store) :
    rule_write_byte_r agreed_rules args s = rule_write_byte args s := rfl

theorem prim_rule_r_agreed (P : profile) (p : prim) (args : List value) (s : store) :
    prim_rule_r agreed_rules P p args s = prim_rule P p args s := by
  cases p <;> first | rfl | exact rule_equal_agreed .. | exact rule_get_time_agreed .. | exact rule_arith_agreed .. | exact rule_div_agreed ..

theorem prim_move_r_agreed (P : profile) (p : prim) (args rest : List value) (k : List frame) (s : store) :
    prim_move_r agreed_rules P p args rest k s = prim_move P p args rest k s := by
  unfold prim_move_r prim_move; simp only [prim_rule_r_agreed]; rfl

theorem call_named_r_agreed (P : profile) (g : name) (args : List value) (k : List frame) (s : store) :
    call_named_r agreed_rules P g args k s = call_named P g args k s := by
  unfold call_named_r call_named
  cases lookup g s.gfuns with
  | none => rfl
  | some d => cases d with
    | FUser ps b => rfl
    | FPrim p =>
      simp only [arity_mismatch, agreed_rules, Bool.false_and, Bool.false_eq_true, ite_false]
      split
      · rfl
      · exact prim_move_r_agreed ..

theorem apply_value_r_agreed (P : profile) (f : value) (args : List value) (k : List frame) (s : store) :
    apply_value_r agreed_rules P f args k s = apply_value P f args k s := by
  cases f <;> cases args <;> first | rfl | exact call_named_r_agreed ..

theorem eval_move_r_agreed (P : profile) (rho : lenv) (e : expr) (k : List frame) (s : store) :
    eval_move_r agreed_rules P rho e k s = eval_move P rho e k s := by
  cases e with
  | ECall f args => cases args <;> first | rfl | exact call_named_r_agreed ..
  | _ => rfl

theorem ret_move_r_agreed (P : profile) (v : value) (f : frame) (k : List frame) (s : store) :
    ret_move_r agreed_rules P v f k s = ret_move P v f k s := by
  cases f with
  | KHead args _ => cases args <;> first | rfl | exact apply_value_r_agreed ..
  | KArgs _ _ rest _ => cases rest <;> first | rfl | exact apply_value_r_agreed ..
  | KCallArgs _ _ rest _ => cases rest <;> first | rfl | exact call_named_r_agreed ..
  | KApply _ => exact apply_value_r_agreed ..
  | _ => rfl

theorem next_r_agreed (P : profile) (c : config) : next_r agreed_rules P c = next P c := by
  obtain ⟨ctl0, k, s⟩ := c
  cases ctl0 with
  | Eval rho e => exact eval_move_r_agreed ..
  | Ret v => cases k <;> first | rfl | exact ret_move_r_agreed ..
  | Throw x => cases k <;> rfl
  | Fail r => rfl
  | Halted ev => cases ev <;> rfl
  | Wrong w => rfl

theorem step_r_agreed (P : profile) (c : config) (l : label) (c' : config) :
    step_r agreed_rules P c l c' ↔ step P c l c' := by
  constructor
  · intro H; cases H with
    | step_r_tau _ N => exact step.step_tau _ _ (by rw [← next_r_agreed]; exact N)
    | step_r_io q kk r N => exact step.step_io _ q kk r (by rw [← next_r_agreed]; exact N)
    | step_r_resource r x _ X => cases X
  · intro H; cases H with
    | step_tau _ N => exact step_r.step_r_tau _ _ (by rw [next_r_agreed]; exact N)
    | step_io q kk r N => exact step_r.step_r_io _ q kk r (by rw [next_r_agreed]; exact N)

-- ---------- what the options say ----------
theorem range_raises (R : port_rules) (P : profile) (p : prim) (iop : Int → Int → Int) (x y : Int) (s : store)
    (H : in_range R (iop x y) = false) :
    rule_arith_r R P p iop [VNum (.NInt x), VNum (.NInt y)] s = dom p := by
  simp [rule_arith_r, H]

theorem no_partial_application (R : port_rules) (P : profile) (g : name) (args : List value) (k : List frame)
    (s : store) (ps : List name) (b : expr) (A : R.arity_errors = true)
    (L : lookup g s.gfuns = some (.FUser ps b)) (N : args.length ≠ ps.length) :
    call_named_r R P g args k s = MTau (Cfg (Throw XArity) k s) := by
  simp [call_named_r, L, arity_mismatch, A, N]

theorem defun_refused (R : port_rules) (P : profile) (rho : lenv) (f : name) (ps : List name) (b : expr)
    (k : List frame) (s : store) (H : R.defun_allowed s f = false) :
    eval_move_r R P rho (EDefun f ps b) k s = MTau (Cfg (Throw XBadDefinition) k s) := by
  simp [eval_move_r, H]

theorem unchecked_write_returns (R : port_rules) (b : Int) (h : Nat) (s : store) (r : response)
    (U : R.unchecked_writes = true) (Hb : 0 ≤ b ∧ b < 256) :
    ∃ kk, rule_write_byte_r R [VNum (.NInt b), VStream h] s = PIO (.QWrite h [b.toNat]) kk ∧
      kk r = ORet (VNum (.NInt b)) s := by
  refine ⟨fun _ => ORet (VNum (.NInt b)) s, ?_, rfl⟩
  simp [rule_write_byte_r, U, Hb.1, Hb.2]

theorem catchable_resource (R : port_rules) (P : profile) (r : resource) (x : exn) (k : List frame) (s : store)
    (H : R.resource_exn r = some x) : next_r R P (Cfg (Fail r) k s) = MTau (Cfg (Throw x) k s) := by
  simp [next_r, H]

theorem closure_identity (R : port_rules) (P : profile) (h : List (List value)) (x : name) (b : expr)
    (r1 r2 : lenv) (I : R.object_identity = true) :
    kl_eq_r R P h (VLam x b ((id_key, VVec 0) :: r1)) (VLam x b ((id_key, VVec 0) :: r1)) = some true ∧
    kl_eq_r R P h (VLam x b ((id_key, VVec 0) :: r1)) (VLam x b ((id_key, VVec 1) :: r2)) = some false := by
  simp [kl_eq_r, eq_depth_r, eq_go_r, is_opaque, eq_opaque_r, I, opaque_eq, closure_id, id_key, text_eqb]

theorem step_r_deterministic_tau (R : port_rules) (P : profile) (c c1 c2 : config)
    (N : ∀ r, R.resource_exn r = none) (H1 : step_r R P c .Tau c1) (H2 : step_r R P c .Tau c2) : c1 = c2 := by
  cases H1 with
  | step_r_tau _ E1 => cases H2 with
    | step_r_tau _ E2 => rw [E1] at E2; cases E2; rfl
    | step_r_resource r _ _ X => rw [N] at X; cases X
  | step_r_resource r _ _ X => rw [N] at X; cases X

end KLPort
