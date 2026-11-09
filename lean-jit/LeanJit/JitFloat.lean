import LeanJit.ZOps
/-! Port of `rocq/JitFloat.v`: IEEE-754 binary64 over bit patterns, in exact integer arithmetic.
Rocq `N` is `Nat`, `Z` is `Int`, `comparison` is `Ordering`. -/
namespace JitFloat

def canonical_nan : Nat := 9221120237041090560
def pos_inf : Int := 9218868437227405312

inductive cls | CNan | CInf (neg : Bool) | CZero (neg : Bool) | CFin (neg : Bool) (m : Int) (e : Int)
open cls

def classify (b : Nat) : cls :=
  let z : Int := b
  let neg := Z.testbit z 63
  let ex := Z.land (Z.shiftr z 52) 2047
  let frac := Z.land z 4503599627370495
  if ex == 2047 then (if frac == 0 then CInf neg else CNan)
  else if ex == 0 then (if frac == 0 then CZero neg else CFin neg frac (-1074))
  else CFin neg (frac + 4503599627370496) (ex - 1075)

def with_sign (neg : Bool) (z : Int) : Nat :=
  (if neg then z + 9223372036854775808 else z).toNat

def bitlen (z : Int) : Int := if z ≤ 0 then 0 else Z.log2 z + 1

def encode (neg : Bool) (mant e : Int) : Nat :=
  let (mant, e) := if mant == 9007199254740992 then ((4503599627370496 : Int), e + 1) else (mant, e)
  if mant == 0 then with_sign neg 0
  else if mant < 4503599627370496 then with_sign neg mant
  else let field := e + 1075
    if field ≥ 2047 then with_sign neg pos_inf
    else with_sign neg (Z.lor (Z.shiftl field 52) (Z.land mant 4503599627370495))

def round_scaled (neg : Bool) (q e : Int) (sticky : Bool) : Nat :=
  let d := Z.max (bitlen q - 53) (-1074 - e)
  if d ≤ 0 then encode neg (Z.shiftl q (- d)) (e + d)
  else
    let mant := Z.shiftr q d
    let rest := q - Z.shiftl mant d
    let half := Z.shiftl 1 (d - 1)
    let up := if half < rest then true
              else if rest < half then false
              else if sticky then true else Z.odd mant
    encode neg (if up then mant + 1 else mant) (e + d)

def of_ratio (neg : Bool) (num den : Int) : Nat :=
  if num ≤ 0 then with_sign neg 0 else
  let sh := 60 + bitlen den - bitlen num
  let n' := if 0 ≤ sh then Z.shiftl num sh else num
  let d' := if 0 ≤ sh then den else Z.shiftl den (- sh)
  let q := Z.quot n' d'
  round_scaled neg q (- sh) (!(Z.rem n' d' == 0))

def of_Z (z : Int) : Nat :=
  if z == 0 then 0 else of_ratio (z < 0) (Z.abs z) 1

def snum (neg : Bool) (m : Int) := if neg then - m else m
def sum_exact (n1 : Bool) (m1 e1 : Int) (n2 : Bool) (m2 e2 : Int) : Int × Int :=
  let e := Z.min e1 e2
  (snum n1 m1 * Z.shiftl 1 (e1 - e) + snum n2 m2 * Z.shiftl 1 (e2 - e), e)

def of_scaled (z e : Int) (zero_neg : Bool) : Nat :=
  if z == 0 then with_sign zero_neg 0 else
  if 0 ≤ e then of_ratio (z < 0) (Z.abs z * Z.shiftl 1 e) 1
  else of_ratio (z < 0) (Z.abs z) (Z.shiftl 1 (- e))

def add (a b : Nat) : Nat := match classify a, classify b with
  | CNan, _ | _, CNan => canonical_nan
  | CInf x, CInf y => if x == y then a else canonical_nan
  | CInf _, _ => a | _, CInf _ => b
  | CZero x, CZero y => with_sign (x && y) 0
  | CZero _, _ => b | _, CZero _ => a
  | CFin n1 m1 e1, CFin n2 m2 e2 =>
    let (z, e) := sum_exact n1 m1 e1 n2 m2 e2
    of_scaled z e false
def negate (b : Nat) : Nat := (Z.lxor (b : Int) 9223372036854775808).toNat
def sub (a b : Nat) : Nat := match classify b with | CNan => canonical_nan | _ => add a (negate b)
def mul (a b : Nat) : Nat := match classify a, classify b with
  | CNan, _ | _, CNan => canonical_nan
  | CInf _, CZero _ | CZero _, CInf _ => canonical_nan
  | CInf x, CInf y | CInf x, CFin y _ _ | CFin x _ _, CInf y => with_sign (xor x y) pos_inf
  | CZero x, CZero y | CZero x, CFin y _ _ | CFin x _ _, CZero y => with_sign (xor x y) 0
  | CFin n1 m1 e1, CFin n2 m2 e2 => of_scaled (snum (xor n1 n2) (m1 * m2)) (e1 + e2) false
def div (a b : Nat) : Nat := match classify a, classify b with
  | CNan, _ | _, CNan => canonical_nan
  | CInf _, CInf _ | CZero _, CZero _ => canonical_nan
  | CInf x, CZero y | CInf x, CFin y _ _ | CFin x _ _, CZero y => with_sign (xor x y) pos_inf
  | CZero x, CInf y | CZero x, CFin y _ _ | CFin x _ _, CInf y => with_sign (xor x y) 0
  | CFin n1 m1 e1, CFin n2 m2 e2 =>
    let e := e1 - e2
    if 0 ≤ e then of_ratio (xor n1 n2) (m1 * Z.shiftl 1 e) m2
    else of_ratio (xor n1 n2) m1 (m2 * Z.shiftl 1 (- e))

def rank (c : cls) : Option (Int × Int × Int) := match c with
  | CNan => none
  | CInf neg => some (if neg then -1 else 1, 0, 0)
  | CZero _ => some (0, 0, 0)
  | CFin neg m e => some (0, snum neg m, e)
def compare (a b : Nat) : Option Ordering :=
  match rank (classify a), rank (classify b) with
  | some (i1, m1, e1), some (i2, m2, e2) =>
    if !(i1 == i2) then some (Z.compare i1 i2)
    else if i1 == 0 then
      let e := Z.min e1 e2
      some (Z.compare (m1 * Z.shiftl 1 (e1 - e)) (m2 * Z.shiftl 1 (e2 - e)))
    else some .eq
  | _, _ => none
def lt (a b : Nat) := match compare a b with | some .lt => true | _ => false
def gt (a b : Nat) := match compare a b with | some .gt => true | _ => false
def le (a b : Nat) := match compare a b with | some .lt | some .eq => true | _ => false
def ge (a b : Nat) := match compare a b with | some .gt | some .eq => true | _ => false
def eqv (a b : Nat) := match compare a b with | some .eq => true | _ => false
def is_nan (b : Nat) := match classify b with | CNan => true | _ => false
def is_zero (b : Nat) := match classify b with | CZero _ => true | _ => false
def is_finite (b : Nat) := match classify b with | CNan | CInf _ => false | _ => true
def to_Z_exact (b : Nat) : Option Int := match classify b with
  | CZero _ => some 0
  | CFin neg m e =>
    if 0 ≤ e then some (snum neg (Z.shiftl m e))
    else if Z.land m (Z.shiftl 1 (- e) - 1) == 0 then some (snum neg (Z.shiftr m (- e))) else none
  | _ => none
def ratio (b : Nat) : Option (Bool × Int × Int) := match classify b with
  | CZero neg => some (neg, 0, 1)
  | CFin neg m e => some (if 0 ≤ e then (neg, Z.shiftl m e, 1) else (neg, m, Z.shiftl 1 (- e)))
  | _ => none

-- --- Decimal text ---
def digits_of : Nat → Int → List Nat → List Nat
  | 0, _, acc => acc
  | f + 1, z, acc =>
    let acc' := (48 + Z.rem z 10).toNat :: acc
    if z < 10 then acc' else digits_of f (Z.quot z 10) acc'
def z_digits (z : Int) : List Nat := digits_of 40000 (Z.abs z) []
def z_text (z : Int) : List Nat := (if z < 0 then [45] else []) ++ z_digits z
def pow10 (n : Int) : Int := Z.pow 10 n

/-- The inline `fix up` of `dec_exp`. -/
def dec_exp_up (holds : Int → Bool) : Nat → Int → Int × Nat
  | 0, x => (x, 0)
  | f + 1, x => if holds (x + 1) then dec_exp_up holds f (x + 1) else (x, f + 1)
def dec_exp (num den : Int) : Int :=
  let approx := Z.quot ((bitlen num - bitlen den) * 30103) 100000
  let holds (x : Int) : Bool := if 0 ≤ x then decide (den * pow10 x ≤ num) else decide (den ≤ num * pow10 (- x))
  (dec_exp_up holds 8 (approx - 3)).1

def dec_round (num den p : Int) : Int × Int :=
  let x := dec_exp num den
  let s := x - p + 1
  let n' := if 0 ≤ s then num else num * pow10 (- s)
  let d' := if 0 ≤ s then den * pow10 s else den
  let q := Z.quot n' d'
  let r := Z.rem n' d'
  let q' := match Z.compare (2 * r) d' with
    | .lt => q | .gt => q + 1 | .eq => if Z.odd q then q + 1 else q
  if q' == pow10 p then (pow10 (p - 1), x + 1) else (q', x)

def reads_back (neg : Bool) (q x p : Int) : Nat :=
  let s := x - p + 1
  if 0 ≤ s then of_ratio neg (q * pow10 s) 1 else of_ratio neg q (pow10 (- s))

def strip_zeros : List Nat → List Nat
  | 48 :: t => strip_zeros t
  | l => l
def rstrip (l : List Nat) : List Nat := (strip_zeros l.reverse).reverse

def g_text (q x p : Int) : List Nat :=
  let ds := z_digits q
  if x < -4 || x ≥ p then
    let frac := rstrip ds.tail
    ds.headD 48 :: ((match frac with | [] => [] | _ => 46 :: frac)
      ++ 101 :: (if x < 0 then [45] else []) ++ z_digits x)
  else if x < 0 then
    [48, 46] ++ List.replicate (- x - 1).toNat 48 ++ rstrip ds
  else
    let n := (x + 1).toNat
    let ip := ds.take n
    let fp := rstrip (ds.drop n)
    ip ++ 46 :: (match fp with | [] => [48] | _ => fp)

def ascii (s : List Int) : List Nat := s.map Int.toNat
def format_real (b : Nat) : List Nat := match classify b with
  | CNan => ascii [43, 110, 97, 110, 46, 48]
  | CInf neg => ascii [if neg then 45 else 43, 105, 110, 102, 46, 48]
  | CZero neg => (if neg then [45] else []) ++ [48, 46, 48]
  | CFin neg m e =>
    let num := if 0 ≤ e then Z.shiftl m e else m
    let den := if 0 ≤ e then 1 else Z.shiftl 1 (- e)
    let attempt (p : Int) : Option (Int × Int × Int) :=
      let (q, x) := dec_round num den p
      if reads_back neg q x p == b then some (q, x, p) else none
    let (q, x, p) := match attempt 15, attempt 16 with
      | some r, _ => r | none, some r => r
      | none, none => let (q, x) := dec_round num den 17; (q, x, 17)
    (if neg then [45] else []) ++ g_text q x p

def scan_digits : List Nat → Int → Int → Int × Int × List Nat
  | c :: t, acc, n => if 48 ≤ c && c ≤ 57
      then scan_digits t (acc * 10 + (c : Int) - 48) (n + 1) else (acc, n, c :: t)
  | [], acc, n => (acc, n, [])
def parse_decimal (text : List Nat) (exp10 : Int) : Nat :=
  let (neg, t) := match text with
    | 45 :: t => (true, t) | 43 :: t => (false, t) | _ => (false, text)
  let (ip, _, t1) := scan_digits t 0 0
  let (mant, nf) := match t1 with
    | 46 :: t2 => let (m, n, _) := scan_digits t2 ip 0; (m, n)
    | _ => (ip, 0)
  let e := exp10 - nf
  if mant == 0 then with_sign neg 0
  else if 0 ≤ e then of_ratio neg (mant * pow10 e) 1 else of_ratio neg mant (pow10 (- e))

end JitFloat
