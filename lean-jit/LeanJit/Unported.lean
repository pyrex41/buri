/-! What is not ported, collected in one place. Nothing here is an axiom or a `sorry`; the
statements below are comments because their definitions (from the unported files) do not
exist in Lean yet.

* `rocq/JitLowerPrim.v` (176 lines): the primitive cases of the simulation.
* `rocq/JitLowerStep.v` (1,242 lines): `MS`, `Com`, `FunRel`, `Out`, `msr`, and `sim`, the
  one-step simulation. (Its `Sstar` inductive is ported, in JitLowerEquiv.lean.)
* `rocq/JitLowerThm.v` (96 lines): `TN`, `Ends`, and
    `preservation : ∀ n s c m, MS s c m → (∃ c' m' k, Sstar c c' ∧ TN k m m' ∧ n ≤ k ∧ MS s c' m')
                                        ∨ (∃ m1, Ends s c ∧ TStar m m1)`
  and `call_preservation` (the same from a call entered at the top level).
* From `rocq/JitLowerEquiv.v` (670d29d): `call_preservation_src_statement`, `EndsSrc` and
  `call_preservation_src_of_fundamental` (need the three files above); `GVal_trans` and
  `GStore_trans` with `compose_world`/`wf_compose`; the premise checks (`fresh_ok`, `names`,
  `binders`, `scoped`, `D_compiled`) and their specifications; `eq_budget_statement`,
  `sealed_stable_statement`, `storehas_stable_statement`, and the compatibility statements
  other than `if` and `type` (which are proved in Lean, JitLowerEquivCompat/If).
* From `rocq/Observation.v`: behaviors, refinement and the determinism lemmas (unused by the
  Jit files).
-/
