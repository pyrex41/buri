(* Port of rocq/JitFloat.v: IEEE-754 binary64 over bit patterns, in exact integer arithmetic. *)
module Buri.JitFloat
open Buri.Lib

let canonical_nan : nat = 9221120237041090560
let pos_inf : int = 9218868437227405312

type cls = | CNan | CInf : neg:bool -> cls | CZero : neg:bool -> cls | CFin : neg:bool -> m:int -> e:int -> cls

let classify (b : nat) : cls =
  let z : int = b in
  let neg = ztestbit z 63 in
  let ex = zland (zshiftr z 52) 2047 in
  let frac = zland z 4503599627370495 in
  if ex = 2047 then (if frac = 0 then CInf neg else CNan)
  else if ex = 0 then (if frac = 0 then CZero neg else CFin neg frac (-1074))
  else CFin neg (frac + 4503599627370496) (ex - 1075)

let with_sign (neg : bool) (z : int) : nat = to_nat (if neg then z + 9223372036854775808 else z)

let bitlen (z : int) : int = if z <= 0 then 0 else zlog2 z + 1

let encode (neg : bool) (mant0 e0 : int) : nat =
  let (mant, e) = if mant0 = 9007199254740992 then (4503599627370496, e0 + 1) else (mant0, e0) in
  if mant = 0 then with_sign neg 0
  else if mant < 4503599627370496 then with_sign neg mant
  else let field = e + 1075 in
    if field >= 2047 then with_sign neg pos_inf
    else with_sign neg (zlor (zshiftl field 52) (zland mant 4503599627370495))

let round_scaled (neg : bool) (q e : int) (sticky : bool) : nat =
  let d = zmax (bitlen q - 53) (-1074 - e) in
  if d <= 0 then encode neg (zshiftl q (- d)) (e + d)
  else
    let mant = zshiftr q d in
    let rest = q - zshiftl mant d in
    let half = zshiftl 1 (d - 1) in
    let up = if half < rest then true
             else if rest < half then false
             else if sticky then true else zodd mant in
    encode neg (if up then mant + 1 else mant) (e + d)

let of_ratio (neg : bool) (num den : int) : nat =
  if num <= 0 then with_sign neg 0 else
  let sh = 60 + bitlen den - bitlen num in
  let n' = if 0 <= sh then zshiftl num sh else num in
  let d' = if 0 <= sh then den else zshiftl den (- sh) in
  let q = zquot n' d' in
  round_scaled neg q (- sh) (not (zrem n' d' = 0))

let of_Z (z : int) : nat = if z = 0 then 0 else of_ratio (z < 0) (zabs z) 1

let snum (neg : bool) (m : int) : int = if neg then - m else m
let sum_exact (n1 : bool) (m1 e1 : int) (n2 : bool) (m2 e2 : int) : int & int =
  let e = zmin e1 e2 in
  (snum n1 m1 * zshiftl 1 (e1 - e) + snum n2 m2 * zshiftl 1 (e2 - e), e)

let of_scaled (z e : int) (zero_neg : bool) : nat =
  if z = 0 then with_sign zero_neg 0 else
  if 0 <= e then of_ratio (z < 0) (zabs z * zshiftl 1 e) 1
  else of_ratio (z < 0) (zabs z) (zshiftl 1 (- e))

let add (a b : nat) : nat = match classify a, classify b with
  | CNan, _ | _, CNan -> canonical_nan
  | CInf x, CInf y -> if x = y then a else canonical_nan
  | CInf _, _ -> a | _, CInf _ -> b
  | CZero x, CZero y -> with_sign (x && y) 0
  | CZero _, _ -> b | _, CZero _ -> a
  | CFin n1 m1 e1, CFin n2 m2 e2 ->
    let (z, e) = sum_exact n1 m1 e1 n2 m2 e2 in of_scaled z e false
let negate (b : nat) : nat = to_nat (zlxor b 9223372036854775808)
let sub (a b : nat) : nat = match classify b with CNan -> canonical_nan | _ -> add a (negate b)
let mul (a b : nat) : nat = match classify a, classify b with
  | CNan, _ | _, CNan -> canonical_nan
  | CInf _, CZero _ | CZero _, CInf _ -> canonical_nan
  | CInf x, CInf y | CInf x, CFin y _ _ | CFin x _ _, CInf y -> with_sign (x <> y) pos_inf
  | CZero x, CZero y | CZero x, CFin y _ _ | CFin x _ _, CZero y -> with_sign (x <> y) 0
  | CFin n1 m1 e1, CFin n2 m2 e2 -> of_scaled (snum (n1 <> n2) (m1 * m2)) (e1 + e2) false
let div (a b : nat) : nat = match classify a, classify b with
  | CNan, _ | _, CNan -> canonical_nan
  | CInf _, CInf _ | CZero _, CZero _ -> canonical_nan
  | CInf x, CZero y | CInf x, CFin y _ _ | CFin x _ _, CZero y -> with_sign (x <> y) pos_inf
  | CZero x, CInf y | CZero x, CFin y _ _ | CFin x _ _, CInf y -> with_sign (x <> y) 0
  | CFin n1 m1 e1, CFin n2 m2 e2 ->
    let e = e1 - e2 in
    if 0 <= e then of_ratio (n1 <> n2) (m1 * zshiftl 1 e) m2
    else of_ratio (n1 <> n2) m1 (m2 * zshiftl 1 (- e))

let rank (c : cls) : option (int & int & int) = match c with
  | CNan -> None
  | CInf neg -> Some ((if neg then -1 else 1), 0, 0)
  | CZero _ -> Some (0, 0, 0)
  | CFin neg m e -> Some (0, snum neg m, e)
let compare (a b : nat) : option comparison =
  match rank (classify a), rank (classify b) with
  | Some (i1, m1, e1), Some (i2, m2, e2) ->
    if not (i1 = i2) then Some (zcompare i1 i2)
    else if i1 = 0 then
      let e = zmin e1 e2 in
      Some (zcompare (m1 * zshiftl 1 (e1 - e)) (m2 * zshiftl 1 (e2 - e)))
    else Some Eq
  | _, _ -> None
let lt a b = match compare a b with Some Lt -> true | _ -> false
let gt a b = match compare a b with Some Gt -> true | _ -> false
let le a b = match compare a b with Some Lt | Some Eq -> true | _ -> false
let ge a b = match compare a b with Some Gt | Some Eq -> true | _ -> false
let eqv a b = match compare a b with Some Eq -> true | _ -> false
let is_nan b = match classify b with CNan -> true | _ -> false
let is_zero b = match classify b with CZero _ -> true | _ -> false
let is_finite b = match classify b with CNan | CInf _ -> false | _ -> true
let to_Z_exact (b : nat) : option int = match classify b with
  | CZero _ -> Some 0
  | CFin neg m e ->
    if 0 <= e then Some (snum neg (zshiftl m e))
    else if zland m (zshiftl 1 (- e) - 1) = 0 then Some (snum neg (zshiftr m (- e))) else None
  | _ -> None
let ratio (b : nat) : option (bool & int & int) = match classify b with
  | CZero neg -> Some (neg, 0, 1)
  | CFin neg m e -> Some (if 0 <= e then (neg, zshiftl m e, 1) else (neg, m, zshiftl 1 (- e)))
  | _ -> None

(* --- Decimal text --- *)
let rec digits_of (fuel : nat) (z : int) (acc : list nat) : Tot (list nat) (decreases fuel) =
  if fuel = 0 then acc
  else let acc' = to_nat (48 + zrem z 10) :: acc in
    if z < 10 then acc' else digits_of (fuel - 1) (zquot z 10) acc'
let z_digits (z : int) : list nat = digits_of 40000 (zabs z) []
let z_text (z : int) : list nat = app (if z < 0 then [45] else []) (z_digits z)
let pow10 (n : int) : int = zpow 10 n

let rec dec_exp_up (holds : int -> bool) (f : nat) (x : int) : Tot (int & nat) (decreases f) =
  if f = 0 then (x, 0) else if holds (x + 1) then dec_exp_up holds (f - 1) (x + 1) else (x, f)
let dec_exp (num den : int) : int =
  let approx = zquot ((bitlen num - bitlen den) * 30103) 100000 in
  let holds (x : int) : bool = if 0 <= x then den * pow10 x <= num else den <= num * pow10 (- x) in
  let (x, _) = dec_exp_up holds 8 (approx - 3) in x

let dec_round (num den p : int) : int & int =
  let x = dec_exp num den in
  let s = x - p + 1 in
  let n' = if 0 <= s then num else num * pow10 (- s) in
  let d' = if 0 <= s then den * pow10 s else den in
  let q = zquot n' d' in
  let r = zrem n' d' in
  let q' = match zcompare (2 * r) d' with
    | Lt -> q | Gt -> q + 1 | Eq -> if zodd q then q + 1 else q in
  if q' = pow10 p then (pow10 (p - 1), x + 1) else (q', x)

let reads_back (neg : bool) (q x p : int) : nat =
  let s = x - p + 1 in
  if 0 <= s then of_ratio neg (q * pow10 s) 1 else of_ratio neg q (pow10 (- s))

let rec strip_zeros (l : list nat) : list nat = match l with
  | 48 :: t -> strip_zeros t | _ -> l
let rstrip (l : list nat) : list nat = rev (strip_zeros (rev l))

let g_text (q x p : int) : list nat =
  let ds = z_digits q in
  if x < -4 || x >= p then
    let frac = rstrip (tl ds) in
    hd 48 ds :: app (match frac with [] -> [] | _ -> 46 :: frac)
      (101 :: app (if x < 0 then [45] else []) (z_digits x))
  else if x < 0 then
    app [48; 46] (app (repeat 48 (to_nat (- x - 1))) (rstrip ds))
  else
    let n = to_nat (x + 1) in
    let ip = firstn n ds in
    let fp = rstrip (skipn n ds) in
    app ip (46 :: (match fp with [] -> [48] | _ -> fp))

let ascii (s : list int) : list nat = map to_nat s
let format_real (b : nat) : list nat = match classify b with
  | CNan -> ascii [43;110;97;110;46;48]
  | CInf neg -> ascii [(if neg then 45 else 43);105;110;102;46;48]
  | CZero neg -> app (if neg then [45] else []) [48;46;48]
  | CFin neg m e ->
    let num = if 0 <= e then zshiftl m e else m in
    let den = if 0 <= e then 1 else zshiftl 1 (- e) in
    let attempt (p : int) : option (int & int & int) = let (q, x) = dec_round num den p in
      if reads_back neg q x p = b then Some (q, x, p) else None in
    let (q, x, p) = match attempt 15, attempt 16 with
      | Some r, _ -> r | None, Some r -> r
      | None, None -> let (q, x) = dec_round num den 17 in (q, x, 17) in
    app (if neg then [45] else []) (g_text q x p)

let rec scan_digits (l : list nat) (acc : int) (n : int) : int & int & list nat = match l with
  | c :: t -> if 48 <= c && c <= 57 then scan_digits t (acc * 10 + c - 48) (n + 1) else (acc, n, l)
  | [] -> (acc, n, [])
let parse_decimal (text : list nat) (exp10 : int) : nat =
  let (neg, t) = match text with
    | 45 :: t -> (true, t) | 43 :: t -> (false, t) | _ -> (false, text) in
  let (ip, _, t1) = scan_digits t 0 0 in
  let (mant, nf) = match t1 with
    | 46 :: t2 -> let (m, n, _) = scan_digits t2 ip 0 in (m, n)
    | _ -> (ip, 0) in
  let e = exp10 - nf in
  if mant = 0 then with_sign neg 0
  else if 0 <= e then of_ratio neg (mant * pow10 e) 1 else of_ratio neg mant (pow10 (- e))
