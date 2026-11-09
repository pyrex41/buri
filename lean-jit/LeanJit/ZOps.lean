/-! The `ZArith` operations the Rocq files use, on Lean `Int`, with Rocq's meaning
(two's-complement bit operations on unbounded integers, truncating `quot`/`rem`, floor `div`).
Lean core has `Int.shiftRight`, `Int.tdiv`, `Int.tmod`, `Int.fdiv`, but no `land`/`lor`/`lxor`/
`testbit`/`log2` on `Int`, so they are defined here from the `Nat` operations. -/
namespace Z

def lnot (z : Int) : Int := -z - 1

def land : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a &&& b)
  | .ofNat a, .negSucc b => .ofNat (a ^^^ (a &&& b))
  | .negSucc a, .ofNat b => .ofNat (b ^^^ (a &&& b))
  | .negSucc a, .negSucc b => .negSucc (a ||| b)
def lor : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ||| b)
  | .ofNat a, .negSucc b => .negSucc (b ^^^ (a &&& b))
  | .negSucc a, .ofNat b => .negSucc (a ^^^ (a &&& b))
  | .negSucc a, .negSucc b => .negSucc (a &&& b)
def lxor : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ^^^ b)
  | .ofNat a, .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .ofNat b => .negSucc (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)

/-- `Z.testbit z n`: false for a negative index. -/
def testbit (z : Int) (n : Int) : Bool :=
  if n < 0 then false else match z with
  | .ofNat a => a.testBit n.toNat
  | .negSucc a => !(a.testBit n.toNat)

/-- `Z.shiftl z k`: multiplication by `2^k`, or floor division by `2^-k` when `k < 0`. -/
def shiftl (z k : Int) : Int := if 0 ≤ k then z * 2 ^ k.toNat else z >>> (-k).toNat
def shiftr (z k : Int) : Int := shiftl z (-k)

def log2 (z : Int) : Int := if z ≤ 0 then 0 else (Nat.log2 z.toNat : Int)
def quot (a b : Int) : Int := Int.tdiv a b
def rem (a b : Int) : Int := Int.tmod a b
def div (a b : Int) : Int := Int.fdiv a b
def odd (z : Int) : Bool := Int.emod z 2 == 1
def pow (z n : Int) : Int := if n < 0 then 0 else z ^ n.toNat
def abs (z : Int) : Int := if z < 0 then -z else z
def max (a b : Int) : Int := if a ≤ b then b else a
def min (a b : Int) : Int := if a ≤ b then a else b
def eqb (a b : Int) : Bool := a == b
def leb (a b : Int) : Bool := decide (a ≤ b)
def ltb (a b : Int) : Bool := decide (a < b)
def geb (a b : Int) : Bool := decide (a ≥ b)
def gtb (a b : Int) : Bool := decide (a > b)
def compare (a b : Int) : Ordering := if a < b then .lt else if a = b then .eq else .gt

end Z
