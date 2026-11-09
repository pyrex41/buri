(* Port of rocq/JitLowerPrim.v (definitions; see the README for which lemmas are proved):
   the admitted primitives give related results on related arguments, or both raise.
   Encoding: Rocq's two-constructor Prop `PR` is a disjunction of existentials here (it has no
   recursive occurrence, so the two say the same). *)
module Buri.JitLowerPrim
open Buri.Lib
open Buri.Observation
open Buri.KLSyntax
open Buri.KLValue
open Buri.KLSemantics
open Buri.KLPort
open Buri.JitProfile
open Buri.JitLowerRel
module B = Buri.JitBytecode
module F = Buri.JitFloat

let exn_ok (x : exn) (msg : B.text) : prop = match x with
  | XUser t -> t == msg | _ -> True

let pR (sealed : list name) (e : B.env) (pt : B.tree (B.prim & nat)) (m : B.machine) (d : nat)
  (p : prim) (q : B.prim) (args : list value) (args' : list B.val_) (s : store) : prop =
  (exists v v'. prim_rule_r (jit_rules sealed) jit_profile p args s == PDone (ORet v s) /\
     B.prim_step e pt m d q args' == B.ret_to m d v' /\ inhabited (vr v v')) \/
  (exists x msg tv. prim_rule_r (jit_rules sealed) jit_profile p args s == PDone (OThrow x) /\
     B.prim_step e pt m d q args' == B.raise m msg tv /\ exn_ok x msg)

let vr_bool_eq (x y : bool) : Pure (vr (VBool x) (B.VBool y)) (requires x == y) (ensures fun _ -> True) = VR_bool x

let p_cons sealed e pt m d s a b a' b' (ha : vr a a') (hb : vr b b')
  : Lemma (pR sealed e pt m d PCons B.PCons [a; b] [a'; b'] s) =
  let dv : vr (VCons a b) (B.VPair a' b') = VR_cons a a' b b' ha hb in
  assert (inhabited (vr (VCons a b) (B.VPair a' b')))

let pr_ret_intro sealed e pt m d p q args args' s (v : value) (v' : B.val_) (dv : vr v v')
  : Lemma (requires prim_rule_r (jit_rules sealed) jit_profile p args s == PDone (ORet v s) /\
                    B.prim_step e pt m d q args' == B.ret_to m d v')
          (ensures pR sealed e pt m d p q args args' s) =
  assert (inhabited (vr v v'))

let pr_raise_intro sealed e pt m d p q args args' s (x : exn) (msg : B.text) (tv : B.val_)
  : Lemma (requires prim_rule_r (jit_rules sealed) jit_profile p args s == PDone (OThrow x) /\
                    B.prim_step e pt m d q args' == B.raise m msg tv /\ exn_ok x msg)
          (ensures pR sealed e pt m d p q args args' s) = ()

#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"
let p_hd sealed e pt m d s a a' (ha : vr a a') : Lemma (pR sealed e pt m d PHd B.PHd [a] [a'] s) =
  match ha with
  | VR_cons a1 a1' d1 d1' h1 _ -> pr_ret_intro sealed e pt m d PHd B.PHd [a] [a'] s a1 a1' h1
  | _ -> pr_raise_intro sealed e pt m d PHd B.PHd [a] [a'] s (XPrim PHd) (B.t "hd: ~S is not a pair") a'

let p_tl sealed e pt m d s a a' (ha : vr a a') : Lemma (pR sealed e pt m d PTl B.PTl [a] [a'] s) =
  match ha with
  | VR_cons a1 a1' d1 d1' _ h2 -> pr_ret_intro sealed e pt m d PTl B.PTl [a] [a'] s d1 d1' h2
  | _ -> pr_raise_intro sealed e pt m d PTl B.PTl [a] [a'] s (XPrim PTl) (B.t "tl: ~S is not a pair") a'

let p_consp sealed e pt m d s a a' (ha : vr a a') : Lemma (pR sealed e pt m d PConsP B.PConsp [a] [a'] s) =
  let b = (match a with VCons _ _ -> true | _ -> false) in
  pr_ret_intro sealed e pt m d PConsP B.PConsp [a] [a'] s (VBool b) (B.VBool b) (VR_bool b)

let p_numberp sealed e pt m d s a a' (ha : vr a a') : Lemma (pR sealed e pt m d PNumberP B.PNumberp [a] [a'] s) =
  let b = (match a with VNum _ -> true | _ -> false) in
  pr_ret_intro sealed e pt m d PNumberP B.PNumberp [a] [a'] s (VBool b) (B.VBool b) (VR_bool b)

let p_stringp sealed e pt m d s a a' (ha : vr a a') : Lemma (pR sealed e pt m d PStringP B.PStringp [a] [a'] s) =
  let b = (match a with VStr _ -> true | _ -> false) in
  pr_ret_intro sealed e pt m d PStringP B.PStringp [a] [a'] s (VBool b) (B.VBool b) (VR_bool b)
#pop-options

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"

let p_add sealed e pt m d s a b a' b' (ha : vr a a') (hb : vr b b')
  : Lemma (pR sealed e pt m d PAdd B.PAdd [a; b] [a'; b'] s) =
  let args = [a; b] in let args' = [a'; b'] in
  match ha with
  | VR_int x -> (match hb with
    | VR_int y ->
      if B.fix_fits (zadd x y) then pr_ret_intro sealed e pt m d PAdd B.PAdd args args' s (VNum (NInt (zadd x y))) (B.VFix (zadd x y)) (VR_int (zadd x y))
      else pr_raise_intro sealed e pt m d PAdd B.PAdd args args' s (XPrim PAdd) (B.t "integer overflow") B.VCleared
    | VR_real y -> pr_ret_intro sealed e pt m d PAdd B.PAdd args args' s (VNum (NFloat (F.add (F.of_Z x) y))) (B.VReal (F.add (F.of_Z x) y)) (VR_real _)
    | _ -> pr_raise_intro sealed e pt m d PAdd B.PAdd args args' s (XPrim PAdd) (B.t "~S is not a number") b')
  | VR_real x -> (match hb with
    | VR_int y -> pr_ret_intro sealed e pt m d PAdd B.PAdd args args' s (VNum (NFloat (F.add x (F.of_Z y)))) (B.VReal (F.add x (F.of_Z y))) (VR_real _)
    | VR_real y -> pr_ret_intro sealed e pt m d PAdd B.PAdd args args' s (VNum (NFloat (F.add x y))) (B.VReal (F.add x y)) (VR_real _)
    | _ -> pr_raise_intro sealed e pt m d PAdd B.PAdd args args' s (XPrim PAdd) (B.t "~S is not a number") b')
  | _ -> pr_raise_intro sealed e pt m d PAdd B.PAdd args args' s (XPrim PAdd) (B.t "~S is not a number") a'

let p_sub sealed e pt m d s a b a' b' (ha : vr a a') (hb : vr b b')
  : Lemma (pR sealed e pt m d PSub B.PSub [a; b] [a'; b'] s) =
  let args = [a; b] in let args' = [a'; b'] in
  match ha with
  | VR_int x -> (match hb with
    | VR_int y ->
      if B.fix_fits (zsub x y) then pr_ret_intro sealed e pt m d PSub B.PSub args args' s (VNum (NInt (zsub x y))) (B.VFix (zsub x y)) (VR_int (zsub x y))
      else pr_raise_intro sealed e pt m d PSub B.PSub args args' s (XPrim PSub) (B.t "integer overflow") B.VCleared
    | VR_real y -> pr_ret_intro sealed e pt m d PSub B.PSub args args' s (VNum (NFloat (F.sub (F.of_Z x) y))) (B.VReal (F.sub (F.of_Z x) y)) (VR_real _)
    | _ -> pr_raise_intro sealed e pt m d PSub B.PSub args args' s (XPrim PSub) (B.t "~S is not a number") b')
  | VR_real x -> (match hb with
    | VR_int y -> pr_ret_intro sealed e pt m d PSub B.PSub args args' s (VNum (NFloat (F.sub x (F.of_Z y)))) (B.VReal (F.sub x (F.of_Z y))) (VR_real _)
    | VR_real y -> pr_ret_intro sealed e pt m d PSub B.PSub args args' s (VNum (NFloat (F.sub x y))) (B.VReal (F.sub x y)) (VR_real _)
    | _ -> pr_raise_intro sealed e pt m d PSub B.PSub args args' s (XPrim PSub) (B.t "~S is not a number") b')
  | _ -> pr_raise_intro sealed e pt m d PSub B.PSub args args' s (XPrim PSub) (B.t "~S is not a number") a'

let p_mul sealed e pt m d s a b a' b' (ha : vr a a') (hb : vr b b')
  : Lemma (pR sealed e pt m d PMul B.PMul [a; b] [a'; b'] s) =
  let args = [a; b] in let args' = [a'; b'] in
  match ha with
  | VR_int x -> (match hb with
    | VR_int y ->
      if B.fix_fits (zmul x y) then pr_ret_intro sealed e pt m d PMul B.PMul args args' s (VNum (NInt (zmul x y))) (B.VFix (zmul x y)) (VR_int (zmul x y))
      else pr_raise_intro sealed e pt m d PMul B.PMul args args' s (XPrim PMul) (B.t "integer overflow") B.VCleared
    | VR_real y -> pr_ret_intro sealed e pt m d PMul B.PMul args args' s (VNum (NFloat (F.mul (F.of_Z x) y))) (B.VReal (F.mul (F.of_Z x) y)) (VR_real _)
    | _ -> pr_raise_intro sealed e pt m d PMul B.PMul args args' s (XPrim PMul) (B.t "~S is not a number") b')
  | VR_real x -> (match hb with
    | VR_int y -> pr_ret_intro sealed e pt m d PMul B.PMul args args' s (VNum (NFloat (F.mul x (F.of_Z y)))) (B.VReal (F.mul x (F.of_Z y))) (VR_real _)
    | VR_real y -> pr_ret_intro sealed e pt m d PMul B.PMul args args' s (VNum (NFloat (F.mul x y))) (B.VReal (F.mul x y)) (VR_real _)
    | _ -> pr_raise_intro sealed e pt m d PMul B.PMul args args' s (XPrim PMul) (B.t "~S is not a number") b')
  | _ -> pr_raise_intro sealed e pt m d PMul B.PMul args args' s (XPrim PMul) (B.t "~S is not a number") a'
#pop-options

#push-options "--z3rlimit 100 --fuel 2 --ifuel 3"

let p_pgt sealed e pt m d s a b a' b' (ha : vr a a') (hb : vr b b')
  : Lemma (pR sealed e pt m d PGt B.PGt [a; b] [a'; b'] s) =
  let args = [a; b] in let args' = [a'; b'] in
  let num_ret (n1 n2 : num) : Lemma (requires a == VNum n1 /\ b == VNum n2 /\
      B.prim_step e pt m d B.PGt args' == B.ret_to m d (B.VBool (num_cmp jit_profile PGt n1 n2)))
      (ensures pR sealed e pt m d PGt B.PGt args args' s) =
    let r = num_cmp jit_profile PGt n1 n2 in
    pr_ret_intro sealed e pt m d PGt B.PGt args args' s (VBool r) (B.VBool r) (VR_bool r) in
  match ha with
  | VR_int x -> (match hb with
    | VR_int y -> num_ret (NInt x) (NInt y)
    | VR_real y -> num_ret (NInt x) (NFloat y)
    | _ -> pr_raise_intro sealed e pt m d PGt B.PGt args args' s (XPrim PGt) (B.t "~S is not a number") b')
  | VR_real x -> (match hb with
    | VR_int y -> num_ret (NFloat x) (NInt y)
    | VR_real y -> num_ret (NFloat x) (NFloat y)
    | _ -> pr_raise_intro sealed e pt m d PGt B.PGt args args' s (XPrim PGt) (B.t "~S is not a number") b')
  | _ -> pr_raise_intro sealed e pt m d PGt B.PGt args args' s (XPrim PGt) (B.t "~S is not a number") a'

let p_plt sealed e pt m d s a b a' b' (ha : vr a a') (hb : vr b b')
  : Lemma (pR sealed e pt m d PLt B.PLt [a; b] [a'; b'] s) =
  let args = [a; b] in let args' = [a'; b'] in
  let num_ret (n1 n2 : num) : Lemma (requires a == VNum n1 /\ b == VNum n2 /\
      B.prim_step e pt m d B.PLt args' == B.ret_to m d (B.VBool (num_cmp jit_profile PLt n1 n2)))
      (ensures pR sealed e pt m d PLt B.PLt args args' s) =
    let r = num_cmp jit_profile PLt n1 n2 in
    pr_ret_intro sealed e pt m d PLt B.PLt args args' s (VBool r) (B.VBool r) (VR_bool r) in
  match ha with
  | VR_int x -> (match hb with
    | VR_int y -> num_ret (NInt x) (NInt y)
    | VR_real y -> num_ret (NInt x) (NFloat y)
    | _ -> pr_raise_intro sealed e pt m d PLt B.PLt args args' s (XPrim PLt) (B.t "~S is not a number") b')
  | VR_real x -> (match hb with
    | VR_int y -> num_ret (NFloat x) (NInt y)
    | VR_real y -> num_ret (NFloat x) (NFloat y)
    | _ -> pr_raise_intro sealed e pt m d PLt B.PLt args args' s (XPrim PLt) (B.t "~S is not a number") b')
  | _ -> pr_raise_intro sealed e pt m d PLt B.PLt args args' s (XPrim PLt) (B.t "~S is not a number") a'

let p_pge sealed e pt m d s a b a' b' (ha : vr a a') (hb : vr b b')
  : Lemma (pR sealed e pt m d PGe B.PGe [a; b] [a'; b'] s) =
  let args = [a; b] in let args' = [a'; b'] in
  let num_ret (n1 n2 : num) : Lemma (requires a == VNum n1 /\ b == VNum n2 /\
      B.prim_step e pt m d B.PGe args' == B.ret_to m d (B.VBool (num_cmp jit_profile PGe n1 n2)))
      (ensures pR sealed e pt m d PGe B.PGe args args' s) =
    let r = num_cmp jit_profile PGe n1 n2 in
    pr_ret_intro sealed e pt m d PGe B.PGe args args' s (VBool r) (B.VBool r) (VR_bool r) in
  match ha with
  | VR_int x -> (match hb with
    | VR_int y -> num_ret (NInt x) (NInt y)
    | VR_real y -> num_ret (NInt x) (NFloat y)
    | _ -> pr_raise_intro sealed e pt m d PGe B.PGe args args' s (XPrim PGe) (B.t "~S is not a number") b')
  | VR_real x -> (match hb with
    | VR_int y -> num_ret (NFloat x) (NInt y)
    | VR_real y -> num_ret (NFloat x) (NFloat y)
    | _ -> pr_raise_intro sealed e pt m d PGe B.PGe args args' s (XPrim PGe) (B.t "~S is not a number") b')
  | _ -> pr_raise_intro sealed e pt m d PGe B.PGe args args' s (XPrim PGe) (B.t "~S is not a number") a'

let p_ple sealed e pt m d s a b a' b' (ha : vr a a') (hb : vr b b')
  : Lemma (pR sealed e pt m d PLe B.PLe [a; b] [a'; b'] s) =
  let args = [a; b] in let args' = [a'; b'] in
  let num_ret (n1 n2 : num) : Lemma (requires a == VNum n1 /\ b == VNum n2 /\
      B.prim_step e pt m d B.PLe args' == B.ret_to m d (B.VBool (num_cmp jit_profile PLe n1 n2)))
      (ensures pR sealed e pt m d PLe B.PLe args args' s) =
    let r = num_cmp jit_profile PLe n1 n2 in
    pr_ret_intro sealed e pt m d PLe B.PLe args args' s (VBool r) (B.VBool r) (VR_bool r) in
  match ha with
  | VR_int x -> (match hb with
    | VR_int y -> num_ret (NInt x) (NInt y)
    | VR_real y -> num_ret (NInt x) (NFloat y)
    | _ -> pr_raise_intro sealed e pt m d PLe B.PLe args args' s (XPrim PLe) (B.t "~S is not a number") b')
  | VR_real x -> (match hb with
    | VR_int y -> num_ret (NFloat x) (NInt y)
    | VR_real y -> num_ret (NFloat x) (NFloat y)
    | _ -> pr_raise_intro sealed e pt m d PLe B.PLe args args' s (XPrim PLe) (B.t "~S is not a number") b')
  | _ -> pr_raise_intro sealed e pt m d PLe B.PLe args args' s (XPrim PLe) (B.t "~S is not a number") a'
#pop-options

(* Forall2 VR, as a derivation. *)
noeq type vrs : list value -> list B.val_ -> Type0 =
  | VRs_nil : vrs [] []
  | VRs_cons : a:value -> a':B.val_ -> l:list value -> l':list B.val_ -> vr a a' -> vrs l l' -> vrs (a :: l) (a' :: l')

#push-options "--z3rlimit 50 --fuel 3 --ifuel 2"
let prim_agree sealed e pt m d (p : prim) (q : B.prim) (args : list value) (args' : list B.val_) s (h : vrs args args')
  : Lemma (requires pmap p == Some q /\ length args = prim_arity p) (ensures pR sealed e pt m d p q args args' s) =
  match h with
  | VRs_cons a a' l l' ha h1 ->
    (match p with
     | PHd -> p_hd sealed e pt m d s a a' ha
     | PTl -> p_tl sealed e pt m d s a a' ha
     | PConsP -> p_consp sealed e pt m d s a a' ha
     | PNumberP -> p_numberp sealed e pt m d s a a' ha
     | PStringP -> p_stringp sealed e pt m d s a a' ha
     | _ ->
       (match h1 with
        | VRs_cons b b' _ _ hb _ ->
          (match p with
           | PAdd -> p_add sealed e pt m d s a b a' b' ha hb
           | PSub -> p_sub sealed e pt m d s a b a' b' ha hb
           | PMul -> p_mul sealed e pt m d s a b a' b' ha hb
           | PGt -> p_pgt sealed e pt m d s a b a' b' ha hb
           | PLt -> p_plt sealed e pt m d s a b a' b' ha hb
           | PGe -> p_pge sealed e pt m d s a b a' b' ha hb
           | PLe -> p_ple sealed e pt m d s a b a' b' ha hb
           | PCons -> p_cons sealed e pt m d s a b a' b' ha hb)))
#pop-options
