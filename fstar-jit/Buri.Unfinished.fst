(* Every statement ported from Rocq whose proof is NOT ported, in one place. Each is defined in
   the module that ports its Rocq file (as Rocq defines them in place); this module names them,
   so `grep` here finds all of them. Nothing is assumed: a theorem that needs one takes it as an
   explicit hypothesis (an argument), as Rocq's JitLowerEquiv does with fundamental_statement.

   - (No longer unfinished.) rocq/JitLowerStep.v's Theorem sim is proved as
     Buri.JitLowerSimEval.sim, and Buri.JitLowerFinal proves preservation, related_progress,
     call_preservation and call_preservation_src_of_fundamental outright from it.
     Buri.JitLowerStep.sim_statement (the informative, Type-valued form) is still only a
     hypothesis, of JitLowerThm's Type-returning versions; it is kept for that comparison.
   - Buri.JitLowerEquiv.fundamental_statement: the fundamental property of KRef. NOT proved in
     Rocq either. store_refl_of_fundamental, adequacy_of_fundamental and
     call_preservation_src_of_fundamental take it as an argument.
   - The other JitLowerEquiv statements Rocq leaves unproved (eq_budget, jit_eq_per,
     sealed_stable, storehas_stable, VRel_down, VRel_wext, ERel_down, KRef_refl, KRef_scope and
     the compat_ lemmas other than compat_type) are NOT ported, not even as statements.
     compat_type_statement IS proved here (compat_type_proved); Rocq leaves it unproved. *)
module Buri.Unfinished
open Buri.KLSyntax
open Buri.KLValue
module B = Buri.JitBytecode

let sim (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) : Type0 = Buri.JitLowerStep.sim_statement e pt sealed
let fundamental (sealed : list name) (dd : list (name & fundef)) : prop = Buri.JitLowerEquiv.fundamental_statement sealed dd
