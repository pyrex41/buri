(* Shen/JIT Phase 1: IEEE-754 binary64 as computed on the pinned RV64 build,
   over bit patterns, in exact integer arithmetic. This is a model written for
   Shen/JIT's semantic profile; it has not been related to Flocq or to the RISC-V
   model's Fpu.v (obligation OB-JIT-FLOAT-MODEL). Generated NaNs are the RISC-V
   canonical NaN. Formatting and parsing follow prims.c: format_real and decimal. *)
From Coq Require Import List ZArith NArith Bool.
Import ListNotations.
Module JitFloat.
Local Open Scope Z_scope.

Definition canonical_nan : N := 9221120237041090560%N.  (* 0x7FF8000000000000 *)
Definition pos_inf : Z := 9218868437227405312.          (* 0x7FF0000000000000 *)

Inductive cls := CNan | CInf (neg : bool) | CZero (neg : bool) | CFin (neg : bool) (m : Z) (e : Z).

Definition classify (b : N) : cls :=
 let z := Z.of_N b in
 let neg := Z.testbit z 63 in
 let ex := Z.land (Z.shiftr z 52) 2047 in
 let frac := Z.land z 4503599627370495 in
 if Z.eqb ex 2047 then (if Z.eqb frac 0 then CInf neg else CNan)
 else if Z.eqb ex 0 then (if Z.eqb frac 0 then CZero neg else CFin neg frac (-1074))
 else CFin neg (frac + 4503599627370496) (ex - 1075).

Definition with_sign (neg : bool) (z : Z) : N :=
 Z.to_N (if neg then z + 9223372036854775808 else z).

Definition bitlen (z : Z) : Z := if Z.leb z 0 then 0 else Z.log2 z + 1.

(* The bits of mant * 2^e, already at most 53 bits unless a carry made 2^53. *)
Definition encode (neg : bool) (mant e : Z) : N :=
 let '(mant, e) := if Z.eqb mant 9007199254740992 then (4503599627370496, e + 1) else (mant, e) in
 if Z.eqb mant 0 then with_sign neg 0
 else if Z.ltb mant 4503599627370496 then with_sign neg mant
 else let field := e + 1075 in
   if Z.geb field 2047 then with_sign neg pos_inf
   else with_sign neg (Z.lor (Z.shiftl field 52) (Z.land mant 4503599627370495)).

(* Round q * 2^e plus a sticky flag, nearest with ties to even. *)
Definition round_scaled (neg : bool) (q e : Z) (sticky : bool) : N :=
 let d := Z.max (bitlen q - 53) (-1074 - e) in
 if Z.leb d 0 then encode neg (Z.shiftl q (- d)) (e + d)
 else
   let mant := Z.shiftr q d in
   let rest := q - Z.shiftl mant d in
   let half := Z.shiftl 1 (d - 1) in
   let up := if Z.ltb half rest then true
             else if Z.ltb rest half then false
             else if sticky then true else Z.odd mant in
   encode neg (if up then mant + 1 else mant) (e + d).

(* Nearest double to neg? num/den, num and den positive. Keeps at least 56
   significant bits and a sticky flag, so rounding is exact. *)
Definition of_ratio (neg : bool) (num den : Z) : N :=
 if Z.leb num 0 then with_sign neg 0 else
 let sh := 60 + bitlen den - bitlen num in
 let n' := if Z.leb 0 sh then Z.shiftl num sh else num in
 let d' := if Z.leb 0 sh then den else Z.shiftl den (- sh) in
 let q := Z.quot n' d' in
 round_scaled neg q (- sh) (negb (Z.eqb (Z.rem n' d') 0)).

Definition of_Z (z : Z) : N :=
 if Z.eqb z 0 then 0%N else of_ratio (Z.ltb z 0) (Z.abs z) 1.

Definition snum (neg : bool) (m : Z) := if neg then - m else m.
(* A finite double as exact num * 2^e. *)
Definition sum_exact (n1 m1 e1 n2 m2 e2 : _) : Z * Z :=
 let e := Z.min e1 e2 in
 (snum n1 m1 * Z.shiftl 1 (e1 - e) + snum n2 m2 * Z.shiftl 1 (e2 - e), e).

Definition of_scaled (z e : Z) (zero_neg : bool) : N :=
 if Z.eqb z 0 then with_sign zero_neg 0 else
 if Z.leb 0 e then of_ratio (Z.ltb z 0) (Z.abs z * Z.shiftl 1 e) 1
 else of_ratio (Z.ltb z 0) (Z.abs z) (Z.shiftl 1 (- e)).

Definition add (a b : N) : N := match classify a, classify b with
 | CNan, _ | _, CNan => canonical_nan
 | CInf x, CInf y => if Bool.eqb x y then a else canonical_nan
 | CInf _, _ => a | _, CInf _ => b
 | CZero x, CZero y => with_sign (x && y)%bool 0
 | CZero _, _ => b | _, CZero _ => a
 | CFin n1 m1 e1, CFin n2 m2 e2 =>
   let '(z, e) := sum_exact n1 m1 e1 n2 m2 e2 in of_scaled z e false end.
Definition negate (b : N) : N := Z.to_N (Z.lxor (Z.of_N b) 9223372036854775808).
Definition sub (a b : N) : N := match classify b with CNan => canonical_nan | _ => add a (negate b) end.
Definition mul (a b : N) : N := match classify a, classify b with
 | CNan, _ | _, CNan => canonical_nan
 | CInf _, CZero _ | CZero _, CInf _ => canonical_nan
 | CInf x, CInf y | CInf x, CFin y _ _ | CFin x _ _, CInf y => with_sign (xorb x y) pos_inf
 | CZero x, CZero y | CZero x, CFin y _ _ | CFin x _ _, CZero y => with_sign (xorb x y) 0
 | CFin n1 m1 e1, CFin n2 m2 e2 => of_scaled (snum (xorb n1 n2) (m1 * m2)) (e1 + e2) false end.
Definition div (a b : N) : N := match classify a, classify b with
 | CNan, _ | _, CNan => canonical_nan
 | CInf _, CInf _ | CZero _, CZero _ => canonical_nan
 | CInf x, CZero y | CInf x, CFin y _ _ | CFin x _ _, CZero y => with_sign (xorb x y) pos_inf
 | CZero x, CInf y | CZero x, CFin y _ _ | CFin x _ _, CInf y => with_sign (xorb x y) 0
 | CFin n1 m1 e1, CFin n2 m2 e2 =>
   let e := e1 - e2 in
   if Z.leb 0 e then of_ratio (xorb n1 n2) (m1 * Z.shiftl 1 e) m2
   else of_ratio (xorb n1 n2) m1 (m2 * Z.shiftl 1 (- e)) end.

(* Exact ordering of two non-NaN doubles; None when either is NaN. *)
Definition rank (c : cls) : option (Z * Z * Z) := match c with
 | CNan => None
 | CInf neg => Some (if neg then -1 else 1, 0, 0)
 | CZero _ => Some (0, 0, 0)
 | CFin neg m e => Some (0, snum neg m, e) end.
Definition compare (a b : N) : option comparison :=
 match rank (classify a), rank (classify b) with
 | Some (i1, m1, e1), Some (i2, m2, e2) =>
   if negb (Z.eqb i1 i2) then Some (Z.compare i1 i2)
   else if Z.eqb i1 0 then
     let e := Z.min e1 e2 in
     Some (Z.compare (m1 * Z.shiftl 1 (e1 - e)) (m2 * Z.shiftl 1 (e2 - e)))
   else Some Eq
 | _, _ => None end.
Definition lt a b := match compare a b with Some Lt => true | _ => false end.
Definition gt a b := match compare a b with Some Gt => true | _ => false end.
Definition le a b := match compare a b with Some Lt | Some Eq => true | _ => false end.
Definition ge a b := match compare a b with Some Gt | Some Eq => true | _ => false end.
Definition eqv a b := match compare a b with Some Eq => true | _ => false end.
Definition is_nan b := match classify b with CNan => true | _ => false end.
Definition is_zero b := match classify b with CZero _ => true | _ => false end.
Definition is_finite b := match classify b with CNan | CInf _ => false | _ => true end.
(* An integral finite value, for shen-jit.integer? and hash. *)
Definition to_Z_exact (b : N) : option Z := match classify b with
 | CZero _ => Some 0
 | CFin neg m e =>
   if Z.leb 0 e then Some (snum neg (Z.shiftl m e))
   else if Z.eqb (Z.land m (Z.shiftl 1 (- e) - 1)) 0 then Some (snum neg (Z.shiftr m (- e))) else None
 | _ => None end.
(* The real as an exact fraction, sign apart. *)
Definition ratio (b : N) : option (bool * Z * Z) := match classify b with
 | CZero neg => Some (neg, 0, 1)
 | CFin neg m e => Some (if Z.leb 0 e then (neg, Z.shiftl m e, 1) else (neg, m, Z.shiftl 1 (- e)))
 | _ => None end.

(* --- Decimal text --- *)
Fixpoint digits_of (fuel : nat) (z : Z) (acc : list N) : list N :=
 match fuel with
 | O => acc
 | S f => let acc' := Z.to_N (48 + Z.rem z 10) :: acc in
   if Z.ltb z 10 then acc' else digits_of f (Z.quot z 10) acc' end.
Definition z_digits (z : Z) : list N := digits_of 40000 (Z.abs z) [].
Definition z_text (z : Z) : list N := (if Z.ltb z 0 then [45%N] else []) ++ z_digits z.
Definition pow10 (n : Z) : Z := Z.pow 10 n.

(* floor(log10(num/den)) for positive num and den, from a binary estimate. *)
Definition dec_exp (num den : Z) : Z :=
 let approx := Z.quot ((bitlen num - bitlen den) * 30103) 100000 in
 let holds x := if Z.leb 0 x then Z.leb (den * pow10 x) num else Z.leb den (num * pow10 (- x)) in
 let '(x, _) := (fix up (f : nat) (x : Z) : Z * nat := match f with
     | O => (x, O) | S f => if holds (x + 1) then up f (x + 1) else (x, S f) end) 8%nat (approx - 3) in x.

(* The nearest p significant decimal digits, ties to even, as (q, X) with
   v near q * 10^(X - p + 1) and 10^(p-1) <= q < 10^p. *)
Definition dec_round (num den p : Z) : Z * Z :=
 let x := dec_exp num den in
 let s := x - p + 1 in
 let n' := if Z.leb 0 s then num else num * pow10 (- s) in
 let d' := if Z.leb 0 s then den * pow10 s else den in
 let q := Z.quot n' d' in
 let r := Z.rem n' d' in
 let q' := match Z.compare (2 * r) d' with
   | Lt => q | Gt => q + 1 | Eq => if Z.odd q then q + 1 else q end in
 if Z.eqb q' (pow10 p) then (pow10 (p - 1), x + 1) else (q', x).

Definition reads_back (neg : bool) (q x p : Z) : N :=
 let s := x - p + 1 in
 if Z.leb 0 s then of_ratio neg (q * pow10 s) 1 else of_ratio neg q (pow10 (- s)).

Fixpoint strip_zeros (l : list N) : list N := match l with
 | 48%N :: t => strip_zeros t | _ => l end.
Definition rstrip (l : list N) : list N := rev (strip_zeros (rev l)).

(* %.{p}g of a nonzero value, in the post-processed form format_real prints:
   exponent without + or leading zeros; a positional result gets .0 if it has
   no point. *)
Definition g_text (q x p : Z) : list N :=
 let ds := z_digits q in
 if orb (Z.ltb x (-4)) (Z.geb x p) then
   let frac := rstrip (tl ds) in
   hd 48%N ds :: (match frac with [] => [] | _ => 46%N :: frac end)
     ++ 101%N :: (if Z.ltb x 0 then [45%N] else []) ++ z_digits x
 else if Z.ltb x 0 then
   [48%N; 46%N] ++ repeat 48%N (Z.to_nat (- x - 1)) ++ rstrip ds
 else
   let n := Z.to_nat (x + 1) in
   let ip := firstn n ds in
   let fp := rstrip (skipn n ds) in
   ip ++ 46%N :: (match fp with [] => [48%N] | _ => fp end).

Definition ascii (s : list Z) : list N := map Z.to_N s.
Definition format_real (b : N) : list N := match classify b with
 | CNan => ascii [43;110;97;110;46;48]
 | CInf neg => ascii [if neg then 45 else 43;105;110;102;46;48]
 | CZero neg => (if neg then [45%N] else []) ++ [48%N;46%N;48%N]
 | CFin neg m e =>
   let num := if Z.leb 0 e then Z.shiftl m e else m in
   let den := if Z.leb 0 e then 1 else Z.shiftl 1 (- e) in
   let attempt p := let '(q, x) := dec_round num den p in
     if N.eqb (reads_back neg q x p) b then Some (q, x, p) else None in
   let '(q, x, p) := match attempt 15, attempt 16 with
     | Some r, _ => r | None, Some r => r
     | None, None => let '(q, x) := dec_round num den 17 in (q, x, 17) end in
   (if neg then [45%N] else []) ++ g_text q x p end.

(* strtod on the digit forms shen-jit.decimal is given: an optional sign, digits,
   an optional fraction. Anything else parses as far as it can, as strtod does. *)
Fixpoint scan_digits (l : list N) (acc : Z) (n : Z) : Z * Z * list N := match l with
 | c :: t => if andb (N.leb 48 c) (N.leb c 57)
             then scan_digits t (acc * 10 + Z.of_N c - 48) (n + 1) else (acc, n, l)
 | [] => (acc, n, []) end.
Definition parse_decimal (text : list N) (exp10 : Z) : N :=
 let '(neg, t) := match text with
   | 45%N :: t => (true, t) | 43%N :: t => (false, t) | _ => (false, text) end in
 let '(ip, _, t1) := scan_digits t 0 0 in
 let '(mant, nf) := match t1 with
   | 46%N :: t2 => let '(m, n, _) := scan_digits t2 ip 0 in (m, n)
   | _ => (ip, 0) end in
 let e := exp10 - nf in
 if Z.eqb mant 0 then with_sign neg 0
 else if Z.leb 0 e then of_ratio neg (mant * pow10 e) 1 else of_ratio neg mant (pow10 (- e)).
End JitFloat.
