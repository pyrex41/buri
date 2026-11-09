(* Statements ported from Rocq whose proofs are NOT ported. Each is a type (a proposition as a
   type, or a prop); nothing here is assumed, and no module uses one except as an explicit
   hypothesis of an implication (as Rocq's JitLowerEquiv does with fundamental_statement). *)
module Buri.Unfinished
open Buri.Lib
open Buri.KLSyntax
open Buri.KLValue
open Buri.KLSemantics
open Buri.JitLowerStep
module B = Buri.JitBytecode

(* rocq/JitLowerStep.v, Theorem sim: from a related pair, the source takes steps and the bytecode
   keeps up, or both finish with related results. Proved in Rocq (about 1,100 lines with its
   lemmas); not proved here. Buri.JitLowerThm proves preservation and call_preservation from it. *)
let sim_statement (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) : Type0 =
  s:store -> c:config -> m:B.machine -> mS s c m -> out e pt sealed s c m
