(* Every statement ported from Rocq whose proof is NOT ported, in one place. Each is defined in
   the module that ports its Rocq file (as Rocq defines them in place); this module names them,
   so `grep` here finds all of them. Nothing is assumed: a theorem that needs one takes it as an
   explicit hypothesis (an argument), as Rocq's JitLowerEquiv does with fundamental_statement.

   - Buri.JitLowerStep.sim_statement (rocq/JitLowerStep.v, Theorem sim): the one-step simulation.
     PROVED in Rocq (with about 1,100 lines of lemmas); not ported. JitLowerThm.preservation,
     related_progress, call_preservation and JitLowerEquiv.call_preservation_src_of_fundamental
     take it as an argument.
   - Buri.JitLowerEquiv.fundamental_statement: the fundamental property of KRef. NOT proved in
     Rocq either. store_refl_of_fundamental, adequacy_of_fundamental and
     call_preservation_src_of_fundamental take it as an argument.
   - Buri.JitLowerEquiv compatibility statements (the compat_ ones): NOT proved in Rocq; see the module
     for the one attempted here. *)
module Buri.Unfinished
open Buri.KLSyntax
open Buri.KLValue
module B = Buri.JitBytecode

let sim (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) : Type0 = Buri.JitLowerStep.sim_statement e pt sealed
let fundamental (sealed : list name) (dd : list (name & fundef)) : prop = Buri.JitLowerEquiv.fundamental_statement sealed dd
