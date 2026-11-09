(* Port of rocq/KLValue.v: values, store and semantic profile.
   Encoding notes: `eq_depth` uses a mutual `eq_depth_list` where Rocq passes `eq_depth P h d'` to
   the generic `list_eq` (F* checks termination of the recursive call when it is applied, so the
   partially applied form is spelled out); `list_eq` is kept and `eq_depth_list_is_list_eq` proves
   the two agree. `vok` uses mutual `vok_env`/`vok_list` in place of fold_right over a lambda, and
   `fold_eok`/`fold_lok` connect them to the Forall forms. Rocq's hand-written nested induction
   principle `value_rect'` is not needed: F*'s well-founded `<<` covers nested lists directly. *)
module Buri.KLValue
open Buri.Lib
open Buri.Observation
open Buri.KLSyntax

type exn =
  | XUser : msg:text -> exn
  | XUnboundVar : x:name -> exn
  | XUnboundGlobal : x:name -> exn
  | XUndefinedFun : f:name -> exn
  | XNotCallable | XNotBoolean | XArity
  | XPrim : p:prim -> exn
  | XDivZero | XBounds | XCondFail
  | XBadDefinition
  | XIO : e:io_error -> exn
  | XEvalKL

type value =
  | VNum : n:num -> value
  | VSym : s:name -> value
  | VBool : b:bool -> value
  | VStr : t:text -> value
  | VNil : value
  | VCons : a:value -> d:value -> value
  | VVec : l:nat -> value
  | VStream : h:nat -> value
  | VLam : x:name -> body:expr -> env:list (name & value) -> value
  | VFrozen : body:expr -> env:list (name & value) -> value
  | VPartial : f:name -> args:list value -> value
  | VExn : x:exn -> value
type lenv = list (name & value)

type fundef = | FPrim : p:prim -> fundef | FUser : params:list name -> body:expr -> fundef
let fun_arity (d : fundef) : nat = match d with FPrim p -> prim_arity p | FUser ps _ -> length ps

type store = { heap : list (list value); gvals : list (name & value); gfuns : list (name & fundef) }
let mkStore h v f : store = { heap = h; gvals = v; gfuns = f }

let rec lookup (#a : Type) (x : name) (l : list (name & a)) : option a =
  match l with
  | [] -> None
  | (y, v) :: l -> if text_eqb x y then Some v else lookup x l

noeq type profile = {
  inexact_op : prim -> num -> num -> option num;
  inexact_cmp : prim -> num -> num -> bool;
  int_div_inexact : int -> int -> num;
  float_text : nat -> text;
  str_other : value -> option text;
  sys_message : exn -> text;
  absvector_fill : value;
  time_value : text -> int -> option num;
  stack_limit : option nat;
  heap_limit : option nat }

let int_or (pr : profile) (p : prim) (iop : int -> int -> int) (a b : num) : option num =
  match a, b with NInt x, NInt y -> Some (NInt (iop x y)) | _, _ -> pr.inexact_op p a b
let num_div (pr : profile) (a b : num) : option (option num) =
  match a, b with
  | _, NInt 0 -> None
  | NInt x, NInt y -> Some (Some (if zrem x y = 0 then NInt (zquot x y) else pr.int_div_inexact x y))
  | _, _ -> Some (pr.inexact_op PDiv a b)
let num_cmp (pr : profile) (p : prim) (a b : num) : bool =
  match a, b with
  | NInt x, NInt y -> (match p with
    | PGt -> x > y | PLt -> x < y | PGe -> x >= y | PLe -> x <= y
    | _ -> x = y)
  | _, _ -> pr.inexact_cmp p a b

let rec list_eq (f : value -> value -> option bool) (xs ys : list value) : option bool =
  match xs, ys with
  | [], [] -> Some true
  | x :: xs, y :: ys -> (match f x y with Some true -> list_eq f xs ys | r -> r)
  | _, _ -> Some false

let is_opaque (v : value) : bool = match v with VLam _ _ _ | VFrozen _ _ | VPartial _ _ | VExn _ -> true | _ -> false

let rec eq_depth (pr : profile) (h : list (list value)) (d : nat) (a b : value)
  : Tot (option bool) (decreases %[d; a]) =
  if d = 0 then None else
  match a, b with
  | VNum x, VNum y -> Some (num_cmp pr PEqual x y)
  | VSym x, VSym y | VStr x, VStr y -> Some (text_eqb x y)
  | VBool x, VBool y -> Some (x = y)
  | VNil, VNil -> Some true
  | VCons a1 a2, VCons b1 b2 ->
    (match eq_depth pr h d a1 b1 with Some true -> eq_depth pr h d a2 b2 | r -> r)
  | VStream x, VStream y -> Some (x = y)
  | VVec l1, VVec l2 -> if l1 = l2 then Some true else
      (match nth_error h l1, nth_error h l2 with
       | Some xs, Some ys -> eq_depth_list pr h (d - 1) xs ys
       | _, _ -> None)
  | _, _ ->
    if is_opaque a then (if is_opaque b then None else Some false)
    else if is_opaque b then Some false
    else Some false
and eq_depth_list (pr : profile) (h : list (list value)) (d : nat) (xs ys : list value)
  : Tot (option bool) (decreases %[d; xs]) =
  match xs, ys with
  | [], [] -> Some true
  | x :: xs', y :: ys' -> (match eq_depth pr h d x y with Some true -> eq_depth_list pr h d xs' ys' | r -> r)
  | _, _ -> Some false

let rec eq_depth_list_is_list_eq (pr : profile) (h : list (list value)) (d : nat) (xs ys : list value)
  : Lemma (eq_depth_list pr h d xs ys == list_eq (eq_depth pr h d) xs ys) =
  match xs, ys with
  | _ :: xs', _ :: ys' -> eq_depth_list_is_list_eq pr h d xs' ys'
  | _ -> ()

let kl_eq (pr : profile) (h : list (list value)) (a b : value) : option bool =
  eq_depth pr h (length h + 1) a b

(* Printing of exact data: NilZero.string_of_int (Z.to_int z). *)
let rec digits (n : nat) (acc : text) : Tot text (decreases n) =
  let acc' = (48 + n % 10) :: acc in
  if n < 10 then acc' else digits (n / 10) acc'
let dec_text (z : int) : text = if z < 0 then 45 :: digits (- z) [] else digits z []
let bool_text (b : bool) : text = of_string (if b then "true" else "false")

let scalar_ok (z : int) : bool = 0 <= z && z <= 1114111 && not (55296 <= z && z <= 57343)

let heap_cells (h : list (list value)) : nat = fold_right #nat (fun (v : list value) (n : nat) -> length v + n) 0 h
let alloc_ok (pr : profile) (h : list (list value)) (n : nat) : bool =
  match pr.heap_limit with None -> true | Some m -> heap_cells h + n + 1 <= m
let rec replace_nth (#a : Type) (n : nat) (x : a) (l : list a) : list a =
  match l with
  | [] -> []
  | y :: l' -> if n = 0 then x :: l' else y :: replace_nth (n - 1) x l'
let rec replace_nth_length (#a : Type) (n : nat) (x : a) (l : list a)
  : Lemma (length (replace_nth n x l) = length l) =
  match l with [] -> () | _ :: l' -> if n = 0 then () else replace_nth_length (n - 1) x l'

(* Well-formed values. *)
let rec vok (n : nat) (v : value) : Tot prop (decreases v) =
  match v with
  | VCons a d -> vok n a /\ vok n d
  | VVec l -> l < n
  | VLam _ _ rho | VFrozen _ rho -> vok_env n rho
  | VPartial _ args -> vok_list n args
  | _ -> True
and vok_env (n : nat) (rho : lenv) : Tot prop (decreases rho) =
  match rho with [] -> True | (_, w) :: r -> vok n w /\ vok_env n r
and vok_list (n : nat) (l : list value) : Tot prop (decreases l) =
  match l with [] -> True | w :: r -> vok n w /\ vok_list n r
let lok (n : nat) (l : list value) : prop = forall_l (vok n) l
let eok (n : nat) (rho : lenv) : prop = forall_l (fun (p : name & value) -> vok n (snd p)) rho

let rec fold_lok (n : nat) (l : list value) : Lemma (vok_list n l <==> lok n l) =
  match l with [] -> () | _ :: r -> fold_lok n r
let rec fold_eok (n : nat) (rho : lenv) : Lemma (vok_env n rho <==> eok n rho) =
  match rho with [] -> () | _ :: r -> fold_eok n r

let rec vok_mono (v : value) (n m : nat)
  : Lemma (requires n <= m /\ vok n v) (ensures vok m v) (decreases v) =
  match v with
  | VCons a d -> vok_mono a n m; vok_mono d n m
  | VLam _ _ rho | VFrozen _ rho -> vok_env_mono rho n m
  | VPartial _ args -> vok_list_mono args n m
  | _ -> ()
and vok_env_mono (rho : lenv) (n m : nat)
  : Lemma (requires n <= m /\ vok_env n rho) (ensures vok_env m rho) (decreases rho) =
  match rho with [] -> () | (_, w) :: r -> vok_mono w n m; vok_env_mono r n m
and vok_list_mono (l : list value) (n m : nat)
  : Lemma (requires n <= m /\ vok_list n l) (ensures vok_list m l) (decreases l) =
  match l with [] -> () | w :: r -> vok_mono w n m; vok_list_mono r n m

let lok_mono (n m : nat) (l : list value) : Lemma (requires n <= m /\ lok n l) (ensures lok m l) =
  fold_lok n l; fold_lok m l; vok_list_mono l n m
let eok_mono (n m : nat) (l : lenv) : Lemma (requires n <= m /\ eok n l) (ensures eok m l) =
  fold_eok n l; fold_eok m l; vok_env_mono l n m

let rec lookup_ok (n : nat) (x : name) (rho : lenv) (v : value)
  : Lemma (requires eok n rho /\ lookup x rho == Some v) (ensures vok n v) =
  match rho with
  | (y, w) :: r -> if text_eqb x y then () else lookup_ok n x r v

let store_ok (s : store) : prop =
  forall_l (lok (length s.heap)) s.heap /\ eok (length s.heap) s.gvals
