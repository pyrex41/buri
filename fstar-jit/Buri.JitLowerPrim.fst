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
