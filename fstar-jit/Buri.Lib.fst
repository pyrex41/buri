(* Rocq standard-library semantics, written once, so that every port module computes what the Rocq
   development computes. Each definition names the Rocq function it stands for. Edge cases follow
   Rocq exactly: truncated subtraction on N/nat, Z.quot/Z.rem truncate toward zero, Z.div/Z.modulo
   floor, x/0 = 0, Z.to_nat/Z.to_N of a negative is 0, Z.log2 of a non-positive is 0, the bitwise
   operations are on unbounded two's complement integers, and the list functions have Coq.Lists
   edge behavior (combine truncates, nth_error is None past the end, firstn/skipn saturate).

   Encodings: Rocq Z is F* int; N and nat are both F* nat; positive is F* pos (xH = 1,
   xO k = 2k, xI k = 2k+1). *)
module Buri.Lib

(* ---------- N / nat ---------- *)
(* N.sub, Nat.sub: truncated at 0. *)
let nsub (a b : nat) : nat = if a >= b then a - b else 0
let nat_eqb (a b : nat) : bool = a = b
let nat_ltb (a b : nat) : bool = a < b
let nat_leb (a b : nat) : bool = a <= b

(* N.succ_pos *)
let succ_pos (n : nat) : pos = n + 1

(* ---------- Z ---------- *)
let zabs (x : int) : nat = if x >= 0 then x else - x
let zmax (a b : int) : int = if a >= b then a else b
let zmin (a b : int) : int = if a <= b then a else b
let nmax (a b : nat) : nat = if a >= b then a else b

(* Z.to_nat, Z.to_N, Z.of_nat, Z.of_N *)
let to_nat (z : int) : nat = if z >= 0 then z else 0

(* Z.quot, Z.rem: truncation toward zero; x quot 0 = 0 and x rem 0 = x. *)
let zquot (x y : int) : int =
  if y = 0 then 0
  else
    let q : nat = zabs x / zabs y in
    if (x >= 0) = (y >= 0) then q else - q
let zrem (x y : int) : int = x - y * zquot x y

(* Z.div, Z.modulo: floor; x div 0 = 0 and x mod 0 = x. *)
let zdiv (x y : int) : int =
  if y = 0 then 0
  else
    let q = zquot x y in
    if zrem x y <> 0 && ((x < 0) <> (y < 0)) then q - 1 else q
let zmodulo (x y : int) : int = x - y * zdiv x y

(* Z.odd *)
let zodd (x : int) : bool = zrem x 2 <> 0

(* 2^n for n : nat. *)
let rec pow2 (n : nat) : pos = if n = 0 then 1 else 2 * pow2 (n - 1)

(* Z.pow: a^n, 0 for n < 0. *)
let rec pow_nat (a : int) (n : nat) : int = if n = 0 then 1 else a * pow_nat a (n - 1)
let zpow (a : int) (n : int) : int = if n < 0 then 0 else pow_nat a n

(* Z.log2: floor of log2 for x > 0, else 0. *)
let rec log2_pos (x : pos) : Tot nat (decreases x) = if x = 1 then 0 else 1 + log2_pos (x / 2)
let zlog2 (x : int) : nat = if x > 0 then log2_pos x else 0

(* ---------- bitwise operations on non-negative integers ---------- *)
let rec nand (a b : nat) : Tot nat (decreases a) =
  if a = 0 || b = 0 then 0
  else 2 * nand (a / 2) (b / 2) + (if a % 2 = 1 && b % 2 = 1 then 1 else 0)
let rec nor (a b : nat) : Tot nat (decreases (a + b)) =
  if a = 0 then b else if b = 0 then a
  else 2 * nor (a / 2) (b / 2) + (if a % 2 = 1 || b % 2 = 1 then 1 else 0)
let rec nxor (a b : nat) : Tot nat (decreases (a + b)) =
  if a = 0 then b else if b = 0 then a
  else 2 * nxor (a / 2) (b / 2) + (if (a % 2 = 1) <> (b % 2 = 1) then 1 else 0)
(* a AND NOT b *)
let rec nandnot (a b : nat) : Tot nat (decreases a) =
  if a = 0 then 0 else if b = 0 then a
  else 2 * nandnot (a / 2) (b / 2) + (if a % 2 = 1 && b % 2 = 0 then 1 else 0)

(* ---------- bitwise operations on Z (two's complement, unbounded) ---------- *)
(* Z.lnot *)
let zlnot (x : int) : int = - x - 1
(* For x < 0, x = lnot x' with x' = -x-1 >= 0. *)
let negpart (x : int{x < 0}) : nat = - x - 1

(* Z.land *)
let zland (a b : int) : int =
  if a >= 0 && b >= 0 then nand a b
  else if a < 0 && b >= 0 then nandnot b (negpart a)
  else if a >= 0 && b < 0 then nandnot a (negpart b)
  else zlnot (nor (negpart a) (negpart b))
(* Z.lor *)
let zlor (a b : int) : int =
  if a >= 0 && b >= 0 then nor a b
  else if a < 0 && b >= 0 then zlnot (nandnot (negpart a) b)
  else if a >= 0 && b < 0 then zlnot (nandnot (negpart b) a)
  else zlnot (nand (negpart a) (negpart b))
(* Z.lxor *)
let zlxor (a b : int) : int =
  if a >= 0 && b >= 0 then nxor a b
  else if a < 0 && b >= 0 then zlnot (nxor (negpart a) b)
  else if a >= 0 && b < 0 then zlnot (nxor a (negpart b))
  else nxor (negpart a) (negpart b)

(* Z.shiftl, Z.shiftr: a negative count shifts the other way; shiftr floors. *)
let zshiftl (x : int) (n : int) : int =
  if n >= 0 then x * pow2 n else zdiv x (pow2 (- n))
let zshiftr (x : int) (n : int) : int =
  if n >= 0 then zdiv x (pow2 n) else x * pow2 (- n)
(* Z.testbit: false at a negative index. *)
let ztestbit (x : int) (n : int) : bool =
  if n < 0 then false else zodd (zshiftr x n)

(* N.land, N.shiftr on N *)
let nland (a b : nat) : nat = nand a b
let nshiftr (a : nat) (n : nat) : nat = a / pow2 n

(* comparison *)
type comparison = | Lt | Eq | Gt
let zcompare (a b : int) : comparison = if a < b then Lt else if a = b then Eq else Gt

(* ---------- lists (Coq.Lists.List) ---------- *)
let rec length (#a : Type) (l : list a) : nat = match l with [] -> 0 | _ :: r -> 1 + length r
let rec app (#a : Type) (l1 l2 : list a) : list a = match l1 with [] -> l2 | x :: r -> x :: app r l2
let rec map (#a #b : Type) (f : a -> b) (l : list a) : list b =
  match l with [] -> [] | x :: r -> f x :: map f r
let rec rev_append (#a : Type) (l acc : list a) : list a =
  match l with [] -> acc | x :: r -> rev_append r (x :: acc)
(* rev; Rocq's rev is defined with app, but the two agree (rev_append_rev). *)
let rec rev (#a : Type) (l : list a) : list a = match l with [] -> [] | x :: r -> app (rev r) [x]
let rec nth_error (#a : Type) (l : list a) (n : nat) : option a =
  match l with
  | [] -> None
  | x :: r -> if n = 0 then Some x else nth_error r (n - 1)
let rec firstn (#a : Type) (n : nat) (l : list a) : list a =
  if n = 0 then [] else match l with [] -> [] | x :: r -> x :: firstn (n - 1) r
let rec skipn (#a : Type) (n : nat) (l : list a) : list a =
  if n = 0 then l else match l with [] -> [] | _ :: r -> skipn (n - 1) r
let rec combine (#a #b : Type) (l1 : list a) (l2 : list b) : list (a & b) =
  match l1, l2 with
  | x :: r1, y :: r2 -> (x, y) :: combine r1 r2
  | _, _ -> []
let rec repeat (#a : Type) (x : a) (n : nat) : list a = if n = 0 then [] else x :: repeat x (n - 1)
let rec last (#a : Type) (l : list a) (d : a) : a =
  match l with [] -> d | [x] -> x | _ :: r -> last r d
let rec existsb (#a : Type) (f : a -> bool) (l : list a) : bool =
  match l with [] -> false | x :: r -> f x || existsb f r
let rec forallb (#a : Type) (f : a -> bool) (l : list a) : bool =
  match l with [] -> true | x :: r -> f x && forallb f r
let rec flat_map (#a #b : Type) (f : a -> list b) (l : list a) : list b =
  match l with [] -> [] | x :: r -> app (f x) (flat_map f r)
let rec fold_left (#a #b : Type) (f : a -> b -> a) (l : list b) (acc : a) : Tot a (decreases l) =
  match l with [] -> acc | x :: r -> fold_left f r (f acc x)
let rec fold_right (#a #b : Type) (f : b -> a -> a) (acc : a) (l : list b) : a =
  match l with [] -> acc | x :: r -> f x (fold_right f acc r)
let rec filter (#a : Type) (f : a -> bool) (l : list a) : list a =
  match l with [] -> [] | x :: r -> if f x then x :: filter f r else filter f r
let rec find (#a : Type) (f : a -> bool) (l : list a) : option a =
  match l with [] -> None | x :: r -> if f x then Some x else find f r
let hd (#a : Type) (d : a) (l : list a) : a = match l with [] -> d | x :: _ -> x
let tl (#a : Type) (l : list a) : list a = match l with [] -> [] | _ :: r -> r
let option_map (#a #b : Type) (f : a -> b) (o : option a) : option b =
  match o with None -> None | Some x -> Some (f x)

(* Forall, In, NoDup, incl, Forall2 *)
let rec forall_l (#a : Type) (p : a -> prop) (l : list a) : prop =
  match l with [] -> True | x :: r -> p x /\ forall_l p r
let rec mem_l (#a : Type) (x : a) (l : list a) : prop =
  match l with [] -> False | y :: r -> x == y \/ mem_l x r
let rec nodup_l (#a : Type) (l : list a) : prop =
  match l with [] -> True | x :: r -> ~(mem_l x r) /\ nodup_l r
let rec forall2_l (#a #b : Type) (p : a -> b -> prop) (l1 : list a) (l2 : list b) : prop =
  match l1, l2 with
  | [], [] -> True
  | x :: r1, y :: r2 -> p x y /\ forall2_l p r1 r2
  | _, _ -> False

(* ---------- lemmas used across modules ---------- *)
let rec app_length (#a : Type) (l1 l2 : list a)
  : Lemma (length (app l1 l2) = length l1 + length l2) =
  match l1 with [] -> () | _ :: r -> app_length r l2
let rec app_assoc (#a : Type) (l1 l2 l3 : list a)
  : Lemma (app l1 (app l2 l3) == app (app l1 l2) l3) =
  match l1 with [] -> () | _ :: r -> app_assoc r l2 l3
let rec app_nil (#a : Type) (l : list a) : Lemma (app l [] == l) =
  match l with [] -> () | _ :: r -> app_nil r
let rec rev_length (#a : Type) (l : list a) : Lemma (length (rev l) = length l) =
  match l with [] -> () | x :: r -> rev_length r; app_length (rev r) [x]

(* ---------- text ---------- *)
(* Observation.text: code points. String literals stand for ASCII text via of_string. *)
let char_code (c : FStar.Char.char) : nat = FStar.Char.int_of_char c
let of_string (s : string) : list nat = map char_code (FStar.String.list_of_string s)
