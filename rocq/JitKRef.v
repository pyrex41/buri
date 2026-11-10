(* Shen/JIT Phase 2: KRef, the front passes' refinement relation, as a stable interface (K00).
   This file holds every Definition, Fixpoint, Inductive and *_statement that rocq/JitLowerEquiv.v
   held before K00 (at 4a7346e and 1297a73), each moved with its text byte-identical, under the
   same Section headers, Variables and local notations, so that each constant has exactly its old
   type and argument order. It holds NO proofs. The design notes below are those of
   JitLowerEquiv.v, unchanged except that the proofs they mention are now in the proof files.

   File map, the ownership contract of the KRef track. A statement lives here and only here; a
   proof file re-opens `Section Equiv` (and `Section Compose`) with the same Variables and the same
   local notations, so that after its Sections close each theorem has the type it would have had
   in this file. A change to this file is an interface change: every later statement's text stays
   byte-identical unless the change is reviewed as one.
   - JitKRef.v (this file): the interface. Worlds, GVal/GStore, ObsT, VRelF/VRel/SRel/KRel/ERel,
     KRef, the premise checks, every *_statement, EndsSrc and call_preservation_src_statement, and
     the index-local interface at the end (fv, fund_below, fund_gen_statement, PoutRel, PrimOutRel,
     prim_compat_statement).
   - JitKRefGround.v (exists): the premise specifications, runs/srun, worlds, GVal/GStore
     transitivity, VRelF_index, the ground lemmas, KRel_top, and Section FromFundamental
     (store_refl_of_fundamental, adequacy_of_fundamental, as implications from fundamental_statement).
   - JitKRefCompose.v (exists): VR_fo, the combine lemmas, call_preservation_src_of_fundamental.
   - JitLowerEquiv.v (exists): name preservation only. One abbreviation per old name, so that
     JitLowerEquiv.JitLowerEquiv.<name> still denotes the moved constant; no constants of its own.
   - JitKRefBase.v (exists): the relation's structure: VRel_down, VRel_wext, ERel_down, KRel
     monotonicity in index and world, SRel down in the index (SRel up in wext is false:
     SRel_wext_refuted; SRel_wext_cells is the true form), KRef_scope, sealed_stable and
     storehas_stable. fv against scoped is not yet proved there.
   - JitKRefCompatCtl.v (planned): the control compatibility lemmas, compat_lit, var, let, if,
     and, or, cond, type and trap, each from fund_below at its index.
   - JitKRefCompatClo.v (exists): compat_lambda and compat_freeze outright; app as
     compat_app_lt at index k and compat_app_of_fund (from fund_gen_statement and
     prim_compat_statement). compat_call and compat_defun are still planned (sealed_stable and
     storehas_stable are proved in JitKRefBase.v).
   - JitKRefPrim.v (exists): prim_compat_statement as prim_compat, with no hypothesis; the = case
     from JitEqBudgetCore.eq_budget_closed (each side's budget moved to S (length w), then a
     lockstep walk), not from eq_budget_statement.
   - JitKRefFund.v (planned): fund_gen_statement by induction on the index from the compatibility
     lemmas, then fundamental_statement, KRef_refl_statement, store_refl_statement and
     call_preservation_src_statement without the fundamental hypothesis.
   Each planned file owns the statements it names; none may add a Definition that changes a
   statement here, an axiom, or an Admitted. *)
(* Shen/JIT Phase 2, the lowerer's front passes (wave 1(c)): statements, reviewed and revised.
   lower.shen (934cfa5, as at d3348ce) lowers a body in three steps: share (b0 to b1, KLambda to KLambda),
   norm (b1 to a normal form n, read back as KLambda e), and emission (e to code c, which
   JitLowerRel.CompFn relates). The intermediate outputs are untrusted witnesses: a Rocq check
   decides each link for one definition. This file states what the two front links must
   establish, `KRef`, and the theorem that composes them with `call_preservation`.

   Each claim is a `Definition ..._statement : Prop`. Nothing is Admitted and nothing is assumed.
   Proved in JitKRefGround.v and JitKRefCompose.v: the premise checks' specifications, the ground relation's
   lemmas, KRel_top, and, AS IMPLICATIONS FROM fundamental_statement, store reflexivity,
   adequacy and the composition (call_preservation_src_of_fundamental). NOT proved: the
   fundamental property, the compatibility lemmas, the sealed-stability lemmas and the = budget
   lemma; each remains a statement.

   Design, in short (the report has the reasons):
   - `KRef` is REFINEMENT, not equivalence. Under `jit_rules`, step_r is not deterministic:
     step_r_resource lets any running state raise "out of memory" or "stack overflow"
     (KLPort.step_r_deterministic_tau needs resource_exn = None, and jit_rules maps both
     resources to Some). The target of a pass may raise one where the source does not, and a
     source can always raise one too, so the permission is in the step relation on both sides
     and KRef needs no separate clause for it.
   - It is a step-indexed Kripke logical relation. Congruence under lambda, freeze and dynamic
     calls needs two closures with differently rewritten bodies to be related, and inlining and
     `let` introduction give closures different captured environments. Worlds are partial
     bijections between heap locations, because under jit_rules every lambda and freeze
     allocates a cell (object_identity), and the passes make cells one-sided in both directions:
     share's (freeze Else) allocates one the source does not, norm's let-lambda and
     ((lambda X B) A) remove ones the source makes.
   - Observation is of terminal states only, after a trace of IO events: a value with its store,
     an exception with its store, or a wrong state. The index counts TARGET steps; the source
     may take any number, so inlining a sealed callee (fewer frames, fewer steps) is allowed.
   - Composition never uses transitivity of the logical relation (which does not hold in
     general for step-indexed relations). It applies each link's adequacy to the closed
     first-order observation and composes there, where the relation, `GStore`, is transitive.
   - KRef is PARTIAL CORRECTNESS: a terminating run of the target is matched. It does not say
     that a target diverges only when the source does. Termination is a separate relation, to be
     proved later with its own compatibility lemmas (OB-JIT-LOWER-TERM): roughly, a source run
     reaching a terminal state that is not a resource error is matched by a target run reaching
     one, so a diverging target has a diverging source by contraposition, constructively.

   What a front-end checker must REJECT, because the rewrite cannot satisfy KRef in Búri's
   KLambda (pass-capture's census: none fires at stage 0):
   - norm's (fn F) rewrites: ((fn F) X...) to (F X...) needs the kernel's fn in D, whose body uses
     trap-error and so is not accepted code, against Com's FunRel; the open-F rewrite calls
     shen-jit.arity?, which the KLambda store does not define;
   - open-call inlining guarded by shen-jit.inlined?, which the store does not define;
   - eval-kl to a call of shen-jit.eval-kl, which the store does not define. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck.
Import ListNotations.
Module JitKRef.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitLowerKont.JitLowerKont JitLowerPrim.JitLowerPrim
 JitLowerStep.JitLowerStep JitLowerThm.JitLowerThm JitLowerCheck.JitLowerCheck.
Module B := JitBytecode.JitBytecode.

Section Equiv.
(* `sealed` is the parameter of jit_rules: the names defun refuses. `D` is the per-definition
   list of function definitions the rewrites rely on (inlined sealed callees, protect, ...):
   only those, so that a store meeting it can also meet Com's FunRel. *)
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules sealed).
Notation P := jit_profile.

(* ---------- runs ---------- *)
(* Exactly n steps of the source semantics, with the IO events they perform. *)
Inductive runs : nat -> config -> trace -> config -> Prop :=
 | runs_0 c : runs 0 c [] c
 | runs_S n c l c1 t c2 : step_r R P c l c1 -> runs n c1 t c2 -> runs (S n) c (trace_of l ++ t) c2.

Definition srun (c : config) (t : trace) (c' : config) : Prop := star (step_r R P) c t c'.

(* ---------- worlds ---------- *)
(* (source location, target location): a partial bijection. A cell outside it on either side
   is one only that side allocated. *)
Definition world := list (nat * nat).
Definition wf_world (w : world) : Prop := NoDup (map fst w) /\ NoDup (map snd w).
Definition wext (w w' : world) : Prop := incl w w' /\ wf_world w'.

(* Closure identities (KLPort.closure_id) correspond, so = on closures answers alike. *)
Definition same_id (w : world) (r0 r : lenv) : Prop :=
 match closure_id r0, closure_id r with
 | Some l0, Some l => In (l0, l) w
 | None, None => True
 | _, _ => False end.

Definition StoreHas (s : store) : Prop := forall f d, In (f, d) D -> lookup f (gfuns s) = Some d.

(* ---------- the ground relation: what a whole run is compared by ---------- *)
(* Values: first-order data equal, vectors by the world, closures by kind and identity.
   Does NOT say: anything about a closure's body or environment beyond its identity. *)
Fixpoint GVal (w : world) (v0 v : value) {struct v0} : Prop :=
 match v0, v with
 | VNum a, VNum b => a = b
 | VSym a, VSym b => a = b
 | VBool a, VBool b => a = b
 | VStr a, VStr b => a = b
 | VNil, VNil => True
 | VCons a0 d0, VCons a d => GVal w a0 a /\ GVal w d0 d
 | VVec l0, VVec l => In (l0, l) w
 | VStream h0, VStream h => h0 = h
 | VLam _ _ r0, VLam _ _ r => same_id w r0 r
 | VFrozen _ r0, VFrozen _ r => same_id w r0 r
 | VPartial f0 as0, VPartial f as1 => f0 = f /\
     (fix go (l0 l : list value) {struct l0} : Prop := match l0, l with
      | [], [] => True
      | x0 :: r0, x :: r => GVal w x0 x /\ go r0 r
      | _, _ => False end) as0 as1
 | VExn x0, VExn x => x0 = x
 | _, _ => False end.

(* Stores: the same function table, the same global names in the same order with GVal-related
   values, and cells related by the world. Does NOT say: anything about cells outside the world
   (garbage, or cells only one side made). That the world maps old locations to themselves is
   said by the statements that use it (wext (id_world s) w). *)
Definition GStore (w : world) (s0 s : store) : Prop :=
 gfuns s0 = gfuns s /\
 Forall2 (fun p0 p => fst p0 = fst p /\ GVal w (snd p0) (snd p)) (gvals s0) (gvals s) /\
 (forall l0 l, In (l0, l) w -> exists c0 c, nth_error (heap s0) l0 = Some c0 /\
    nth_error (heap s) l = Some c /\ Forall2 (GVal w) c0 c).

(* ---------- observation ---------- *)
(* Every target run of fewer than k steps that reaches a terminal state is matched by a source
   run with the same IO trace to a terminal state of the same kind: a GVal-related value, the
   same exception, or a wrong state, with GStore-related stores, under a world extending w.
   Does NOT say: that a diverging target has a diverging source (partial correctness: see
   OB-JIT-LOWER-TERM), anything about infinite IO, or which wrong state. *)
Definition ObsT (k : nat) (w : world) (c0 c : config) : Prop :=
 forall n t c', (n < k)%nat -> runs n c t c' ->
  (forall v s, c' = Cfg (Ret v) [] s -> exists v0 s0 w',
     srun c0 t (Cfg (Ret v0) [] s0) /\ wext w w' /\ GVal w' v0 v /\ GStore w' s0 s) /\
  (forall x s, c' = Cfg (Throw x) [] s -> exists s0 w',
     srun c0 t (Cfg (Throw x) [] s0) /\ wext w w' /\ GStore w' s0 s) /\
  (forall why, next_r R P c' = MWrong why -> exists c0' why0,
     srun c0 t c0' /\ next_r R P c0' = MWrong why0).

(* ---------- the logical relation, generic in the value relation at lower indices ---------- *)
Section Gen.
Variable V : nat -> world -> value -> value -> Prop.

(* Related stores: as GStore, with V for values, and both meeting D.
   Does NOT relate cells outside the world. *)
Definition SRel_with (V1 : world -> value -> value -> Prop) (w : world) (s0 s : store) : Prop :=
 wf_world w /\ StoreHas s0 /\ StoreHas s /\ gfuns s0 = gfuns s /\
 Forall2 (fun p0 p => fst p0 = fst p /\ V1 w (snd p0) (snd p)) (gvals s0) (gvals s) /\
 (forall l0 l, In (l0, l) w -> exists c0 c, nth_error (heap s0) l0 = Some c0 /\
    nth_error (heap s) l = Some c /\ Forall2 (V1 w) c0 c).

(* Environments related on the scope g. Does NOT constrain names outside g. *)
Definition EnvRel_with (V1 : world -> value -> value -> Prop) (w : world) (g : list name) (rho0 rho : lenv) : Prop :=
 forall x, In x g -> exists v0 v, lookup x rho0 = Some v0 /\ lookup x rho = Some v /\ V1 w v0 v.

(* Continuations: given related values (or the same exception) and related stores, observably
   related, at every lower index and larger world. *)
Definition KRel_with (k : nat) (w : world) (K0 K : list frame) : Prop :=
 forall j, (j <= k)%nat -> forall w', wext w w' ->
  (forall v0 v s0 s, V j w' v0 v -> SRel_with (V j) w' s0 s -> ObsT j w' (Cfg (Ret v0) K0 s0) (Cfg (Ret v) K s)) /\
  (forall x s0 s, SRel_with (V j) w' s0 s -> ObsT j w' (Cfg (Throw x) K0 s0) (Cfg (Throw x) K s)).

(* Expressions: under related continuations and stores, the two evaluations are observably related. *)
Definition ERel_with (k : nat) (w : world) (rho0 : lenv) (e0 : expr) (rho : lenv) (e : expr) : Prop :=
 forall j, (j <= k)%nat -> forall w', wext w w' -> forall K0 K, KRel_with j w' K0 K ->
  forall s0 s, SRel_with (V j) w' s0 s -> ObsT j w' (Cfg (Eval rho0 e0) K0 s0) (Cfg (Eval rho e) K s).

(* Values at index k. A lambda or a frozen body is related by what it does when applied, at
   every lower index, so two bodies rewritten differently can be related.
   Does NOT relate a lambda to a partial application or to a frozen body, even where they would
   behave alike: = tells them apart. *)
Fixpoint VBody (k : nat) (w : world) (v0 v : value) {struct v0} : Prop :=
 match v0, v with
 | VNum a, VNum b => a = b
 | VSym a, VSym b => a = b
 | VBool a, VBool b => a = b
 | VStr a, VStr b => a = b
 | VNil, VNil => True
 | VCons a0 d0, VCons a d => VBody k w a0 a /\ VBody k w d0 d
 | VVec l0, VVec l => In (l0, l) w
 | VStream h0, VStream h => h0 = h
 | VLam x0 b0 r0, VLam x b r => same_id w r0 r /\
     forall j, (j < k)%nat -> forall w', wext w w' -> forall a0 a, V j w' a0 a ->
       ERel_with j w' ((x0, a0) :: r0) b0 ((x, a) :: r) b
 | VFrozen b0 r0, VFrozen b r => same_id w r0 r /\
     forall j, (j < k)%nat -> forall w', wext w w' -> ERel_with j w' r0 b0 r b
 | VPartial f0 as0, VPartial f as1 => f0 = f /\
     (fix gol (l0 l : list value) {struct l0} : Prop := match l0, l with
      | [], [] => True
      | x0 :: r0, x :: r => VBody k w x0 x /\ gol r0 r
      | _, _ => False end) as0 as1
 | VExn x0, VExn x => x0 = x
 | _, _ => False end.
End Gen.

(* The relations at every index up to k; VRelF k j is the value relation at j for j <= k. *)
Fixpoint VRelF (k : nat) : nat -> world -> value -> value -> Prop :=
 match k with
 | O => fun _ => VBody (fun _ _ _ _ => False) 0
 | S k' => fun j => if Nat.leb j k' then VRelF k' j else VBody (VRelF k') (S k')
 end.

Definition VRel (k : nat) : world -> value -> value -> Prop := VRelF k k.
Definition SRel (k : nat) : world -> store -> store -> Prop := SRel_with (VRel k).
Definition KRel (k : nat) : world -> list frame -> list frame -> Prop := KRel_with (VRelF k) k.
Definition ERel (k : nat) : world -> lenv -> expr -> lenv -> expr -> Prop := ERel_with (VRelF k) k.

(* ---------- KRef ---------- *)
(* `KRef g e0 e`: e refines e0 in scope g. From any environments related on g, any related
   stores meeting D and any related continuations, every terminal behavior of e, after any IO
   trace, is one of e0: a related value and store, the same exception and a related store, or a
   wrong state. The source and the target are both KLPort.step_r (jit_rules sealed) jit_profile,
   so either may raise a catchable resource error at any running state.
   Partial correctness. Does NOT say:
   - that e diverges only if e0 does: e may diverge silently where e0 returns (OB-JIT-LOWER-TERM);
   - that the two take comparable numbers of steps or have comparable continuations at any
     intermediate point (inlining changes both);
   - anything about IO beyond identical traces on terminating runs, or about stores outside D;
   - anything distinguishing a resource error from a user error: under jit_rules a resource
     error IS (XUser "out of memory") or (XUser "stack overflow"), so a target's
     (simple-error "stack overflow") refines any source that can reach a running state with a
     related store and continuation. *)
Definition KRef (g : list name) (e0 e : expr) : Prop :=
 forall k w rho0 rho, wf_world w -> EnvRel_with (VRel k) w g rho0 rho -> ERel k w rho0 e0 rho e.

(* ---------- premises, as decidable checks ---------- *)
(* Names the lowerer makes, in its namespace ns. `ns.fresh` is (concat Prefix N) with N counting
   from 1 per definition, so a reserved name is a prefix followed by decimal digits; the fixed names
   are norm's inlining marker and KLPort's closure-identity key. The namespace is a parameter:
   stage 0 runs lower.shen with shen-jit.lower. renamed to stage0.lower. (shen-jit's Makefile), so
   its names are stage0.lower.else1, stage0.lower.arg2, stage0.lower.inlining, ...; at run time
   they are shen-jit.lower.*. The lowerer's own definitions mention shen-jit.lower.inlining, so
   fresh_ok in the run-time namespace fails on them; in stage 0's it does not. *)
Definition ns_stage0 : name := of_string "stage0.lower.".
Definition ns_runtime : name := of_string "shen-jit.lower.".
Definition lowerer_prefixes (ns : name) : list name :=
 map (fun p => ns ++ of_string p) ["else"; "exception"; "arg"; "head"; "partial"]%string.
Definition lowerer_fixed (ns : name) : list name := [ns ++ of_string "inlining"; id_key].

Fixpoint prefixb (p t : text) : bool := match p, t with
 | [], _ => true
 | a :: p, b :: t => N.eqb a b && prefixb p t
 | _ :: _, [] => false end.
Definition digitb (c : N) : bool := (N.leb 48 c && N.leb c 57)%bool.
Definition fresh_shape (p x : name) : bool :=
 prefixb p x && negb (Nat.eqb (List.length x) (List.length p)) && forallb digitb (skipn (List.length p) x).
Definition reserved (ns x : name) : bool :=
 existsb (fun p => fresh_shape p x) (lowerer_prefixes ns) || existsb (text_eqb x) (lowerer_fixed ns).

(* Every name an expression mentions, in any position: binders, variables, symbol literals,
   called names and defun parameters. *)
Fixpoint names (e : expr) : list name := match e with
 | ENum _ | EStr _ | EBool _ | ENil => []
 | ESym s => [s]
 | EVar x => [x]
 | ELam x b => x :: names b
 | ELet x a b => x :: names a ++ names b
 | EIf c a b => names c ++ names a ++ names b
 | EAnd a b | EOr a b | ETrap a b => names a ++ names b
 | ECond cl => (fix go (l : list (expr * expr)) : list name := match l with
     | [] => [] | (c, b) :: l => names c ++ names b ++ go l end) cl
 | EFreeze b | EType b => names b
 | EDefun f ps b => f :: ps ++ names b
 | EApp h args => names h ++ (fix go (l : list expr) : list name := match l with
     | [] => [] | a :: l => names a ++ go l end) args
 | ECall f args => f :: (fix go (l : list expr) : list name := match l with
     | [] => [] | a :: l => names a ++ go l end) args
 end.

(* The fresh-name premise, for one definition: its source body and the bodies of every callee
   in D (inlining brings their names in). *)
Definition D_bodies : list expr :=
 flat_map (fun p => match snd p with FUser _ b => [b] | FPrim _ => [] end) D.
Definition fresh_ok (ns : name) (es : list expr) : bool :=
 forallb (fun e => forallb (fun x => negb (reserved ns x)) (names e)) es.

(* Binders. Búri's parse makes a keyword head a special form even where the keyword is bound;
   lower.shen tests `F in Scope` first and makes it a dynamic call. They agree when no binder is
   a keyword. *)
Fixpoint binders (e : expr) : list name := match e with
 | ELam x b => x :: binders b
 | ELet x a b => x :: binders a ++ binders b
 | EIf c a b => binders c ++ binders a ++ binders b
 | EAnd a b | EOr a b | ETrap a b => binders a ++ binders b
 | ECond cl => (fix go (l : list (expr * expr)) : list name := match l with
     | [] => [] | (c, b) :: l => binders c ++ binders b ++ go l end) cl
 | EFreeze b | EType b => binders b
 | EDefun _ ps b => ps ++ binders b
 | EApp h args => binders h ++ (fix go (l : list expr) : list name := match l with
     | [] => [] | a :: l => binders a ++ go l end) args
 | ECall _ args => (fix go (l : list expr) : list name := match l with
     | [] => [] | a :: l => binders a ++ go l end) args
 | _ => [] end.
Definition no_keyword_binders (e : expr) : bool := forallb (fun x => negb (keyword x)) (binders e).

(* D names only sealed functions, each once, so no defun can replace them during a run. KRel and
   SRel make promises only about stores meeting D, so every statement whose proof runs store code
   (a call, eval-kl, a partial application, a stored closure, a defun) takes D_wf: without it a
   defun of a D name mid-run leaves the stores outside those promises. *)
Definition D_wf : Prop := Forall (fun p => In (fst p) sealed) D /\ NoDup (map fst D).

(* Every user definition in D is code the emission relation accepts, given a code object for it:
   what lets a store meeting D also meet Com's FunRel. Decided by JitLowerCheck.check_fn. *)
Definition D_compiled (cs : list (name * B.code)) : bool :=
 forallb (fun p => match snd p with
   | FUser ps b => match lookup (fst p) cs with Some c => check_fn c ps b | None => false end
   | FPrim _ => true end) D.

(* Variables free in e are all in g. *)
Fixpoint scoped (g : list name) (e : expr) : bool := match e with
 | EVar x => bound g x
 | ELam x b => scoped (x :: g) b
 | ELet x a b => scoped g a && scoped (x :: g) b
 | EIf c a b => scoped g c && scoped g a && scoped g b
 | EAnd a b | EOr a b | ETrap a b => scoped g a && scoped g b
 | ECond cl => (fix go (l : list (expr * expr)) : bool := match l with
     | [] => true | (c, b) :: l => scoped g c && scoped g b && go l end) cl
 | EFreeze b | EType b => scoped g b
 | EDefun _ ps b => scoped ps b
 | EApp h args => scoped g h && forallb (scoped g) args
 | ECall _ args => forallb (scoped g) args
 | _ => true end.

(* Each of the store's locations to itself. *)
Definition id_world (s : store) : world := map (fun l => (l, l)) (seq 0 (List.length (heap s))).

(* ======================= statements (Phase B proves them) ======================= *)

(* --- the premises' own specifications --- *)
Definition fresh_ok_spec_statement : Prop := forall ns es,
 fresh_ok ns es = true <-> (forall e x, In e es -> In x (names e) -> reserved ns x = false).

Definition no_keyword_binders_spec_statement : Prop := forall e,
 no_keyword_binders e = true <-> (forall x, In x (binders e) -> keyword x = false).

Definition D_compiled_spec_statement : Prop := forall cs,
 D_compiled cs = true -> forall f ps b, In (f, FUser ps b) D -> exists c, lookup f cs = Some c /\ CompFn c ps b.

(* = on vectors compares contents with a budget of one more than the heap's length (KLPort
   eq_depth_r). Two related heaps differ in length by their one-sided cells, so the relation needs
   the answer not to depend on the budget past that bound. It needs numeric equality to be
   symmetric and transitive: for a profile whose inexact equality is a tolerance, a five-cell heap
   with a 2-cycle and a 3-cycle answers None at budget 6 and Some false at 7 (pass/eqbudget,
   bfa9d64, proved in Rocq). *)
Definition eq_budget_statement : Prop := forall P' h d a b,
 (forall x y, num_cmp P' PEqual x y = num_cmp P' PEqual y x) ->
 (forall x y z, num_cmp P' PEqual x y = true -> num_cmp P' PEqual y z = true -> num_cmp P' PEqual x z = true) ->
 Forall (lok (List.length h)) h -> vok (List.length h) a -> vok (List.length h) b ->
 (S (List.length h) <= d)%nat -> eq_depth_r R P' h d a b = kl_eq_r R P' h a b.

(* Shen/JIT's profile meets both hypotheses, so the fundamental property can use the budget
   statement at jit_profile. *)
Definition jit_eq_per_statement : Prop :=
 (forall x y, num_cmp jit_profile PEqual x y = num_cmp jit_profile PEqual y x) /\
 (forall x y z, num_cmp jit_profile PEqual x y = true -> num_cmp jit_profile PEqual y z = true ->
    num_cmp jit_profile PEqual x z = true).

(* Sealed definitions are never redefined: defun refuses a sealed name (jit_rules option 5), and
   gfuns changes only by defun, including through eval-kl, so this is a lemma, not a premise. *)
Definition sealed_stable_statement : Prop := forall c t c' f,
 srun c t c' -> In f sealed -> lookup f (gfuns (mem c')) = lookup f (gfuns (mem c)).

Definition storehas_stable_statement : Prop := forall c t c',
 D_wf -> srun c t c' -> StoreHas (mem c) -> StoreHas (mem c').

(* --- structure of the relation --- *)
Definition VRelF_index_statement : Prop := forall k j, (j <= k)%nat -> VRelF k j = VRel j.

Definition VRel_down_statement : Prop := forall k j w v0 v, (j <= k)%nat -> VRel k w v0 v -> VRel j w v0 v.
Definition VRel_wext_statement : Prop := forall k w w' v0 v, wext w w' -> VRel k w v0 v -> VRel k w' v0 v.
Definition ERel_down_statement : Prop := forall k j w rho0 e0 rho e,
 (j <= k)%nat -> ERel k w rho0 e0 rho e -> ERel j w rho0 e0 rho e.

(* The relation implies the ground one, and the ground one composes. *)
Definition VRel_ground_statement : Prop := forall k w v0 v, VRel k w v0 v -> GVal w v0 v.
Definition SRel_ground_statement : Prop := forall k w s0 s, SRel k w s0 s -> GStore w s0 s.
Definition compose_world (w1 w2 : world) : world :=
 flat_map (fun p => map (fun q => (fst p, snd q)) (filter (fun q => Nat.eqb (snd p) (fst q)) w2)) w1.
Definition GVal_trans_statement : Prop := forall w1 w2 a b c,
 wf_world w1 -> wf_world w2 -> GVal w1 a b -> GVal w2 b c -> GVal (compose_world w1 w2) a c /\ wf_world (compose_world w1 w2).
Definition GStore_trans_statement : Prop := forall w1 w2 s0 s1 s,
 wf_world w1 -> wf_world w2 -> GStore w1 s0 s1 -> GStore w2 s1 s -> GStore (compose_world w1 w2) s0 s.

(* The empty continuation is related to itself: what makes KRef observable. *)
Definition KRel_top_statement : Prop := forall k w, wf_world w -> KRel k w [] [].

(* The fundamental property, which gives reflexivity: every expression is related to itself in
   environments related on every name. Needed because a real store's globals and cells hold
   closures (the property vector's lambda forms), and the two links start from the same store. *)
Definition EnvRelAll (k : nat) (w : world) (rho0 rho : lenv) : Prop :=
 Forall2 (fun p0 p => fst p0 = fst p /\ VRel k w (snd p0) (snd p)) rho0 rho.
Definition fundamental_statement : Prop := forall k w rho0 rho e,
 D_wf -> wf_world w -> EnvRelAll k w rho0 rho -> ERel k w rho0 e rho e.
(* Not a corollary of fundamental_statement as stated: a closure captures the whole environment,
   and KRef relates only g. Phase B needs the fundamental lemma in a scoped form too. *)
Definition KRef_refl_statement : Prop := forall g e, D_wf -> scoped g e = true -> KRef g e e.
(* A well-formed store (KLValue.store_ok: every value points into its heap) meeting D is related
   to itself at the identity world. *)
Definition store_refl_statement : Prop := forall k s,
 D_wf -> StoreHas s -> store_ok s -> SRel k (id_world s) s s.

(* --- compatibility: one statement per constructor the passes rewrite under --- *)
Definition compat_lit_statement : Prop := forall g e v, lit_val e = Some v -> KRef g e e.
Definition compat_var_statement : Prop := forall g x, In x g -> KRef g (EVar x) (EVar x).
Definition compat_let_statement : Prop := forall g x a0 a b0 b,
 KRef g a0 a -> KRef (x :: g) b0 b -> KRef g (ELet x a0 b0) (ELet x a b).
Definition compat_if_statement : Prop := forall g c0 c a0 a b0 b,
 KRef g c0 c -> KRef g a0 a -> KRef g b0 b -> KRef g (EIf c0 a0 b0) (EIf c a b).
Definition compat_and_statement : Prop := forall g a0 a b0 b,
 KRef g a0 a -> KRef g b0 b -> KRef g (EAnd a0 b0) (EAnd a b).
Definition compat_or_statement : Prop := forall g a0 a b0 b,
 KRef g a0 a -> KRef g b0 b -> KRef g (EOr a0 b0) (EOr a b).
Definition compat_cond_statement : Prop := forall g cl0 cl,
 Forall2 (fun p0 p => KRef g (fst p0) (fst p) /\ KRef g (snd p0) (snd p)) cl0 cl ->
 KRef g (ECond cl0) (ECond cl).
Definition compat_type_statement : Prop := forall g a0 a, KRef g a0 a -> KRef g (EType a0) (EType a).
Definition compat_trap_statement : Prop := forall g a0 a h0 h,
 D_wf -> KRef g a0 a -> KRef g h0 h -> KRef g (ETrap a0 h0) (ETrap a h).
Definition compat_lambda_statement : Prop := forall g x b0 b,
 KRef (x :: g) b0 b -> KRef g (ELam x b0) (ELam x b).
Definition compat_freeze_statement : Prop := forall g b0 b, KRef g b0 b -> KRef g (EFreeze b0) (EFreeze b).
(* Named calls cover `do`, `thaw` and `protect`, which Búri's KLambda has as ordinary calls. *)
Definition compat_call_statement : Prop := forall g f as0 as1,
 D_wf -> Forall2 (KRef g) as0 as1 -> KRef g (ECall f as0) (ECall f as1).
Definition compat_app_statement : Prop := forall g h0 h as0 as1,
 D_wf -> KRef g h0 h -> Forall2 (KRef g) as0 as1 -> KRef g (EApp h0 as0) (EApp h as1).
(* A defun is not rewritten under (lower.shen rejects a nested defun): only reflexivity. *)
Definition compat_defun_statement : Prop := forall g f ps b, D_wf -> KRef g (EDefun f ps b) (EDefun f ps b).
Definition KRef_scope_statement : Prop := forall g g' e0 e, incl g g' -> KRef g e0 e -> KRef g' e0 e.

(* --- adequacy: what one link says about a whole run from the same start --- *)
(* From the same environment of first-order values and the same store, a target run to a value
   or an exception is matched by a source run to the same value or exception, with GStore-related
   final stores. Uses store_refl_statement, so fundamental_statement, for the store. *)
Inductive fo : value -> Prop :=
 | fo_num n : fo (VNum n) | fo_sym x : fo (VSym x) | fo_bool b : fo (VBool b)
 | fo_str t : fo (VStr t) | fo_nil : fo VNil | fo_cons a d : fo a -> fo d -> fo (VCons a d).

Definition adequacy_statement : Prop := forall g e0 e rho s,
 D_wf -> KRef g e0 e -> Forall (fun p => fo (snd p)) rho -> (forall x, In x g -> exists v, lookup x rho = Some v) ->
 StoreHas s -> store_ok s ->
 (forall v s', srun (Cfg (Eval rho e) [] s) [] (Cfg (Ret v) [] s') -> fo v ->
    exists s0 w, srun (Cfg (Eval rho e0) [] s) [] (Cfg (Ret v) [] s0) /\ wext (id_world s) w /\ GStore w s0 s') /\
 (forall x s', srun (Cfg (Eval rho e) [] s) [] (Cfg (Throw x) [] s') ->
    exists s0 w, srun (Cfg (Eval rho e0) [] s) [] (Cfg (Throw x) [] s0) /\ wext (id_world s) w /\ GStore w s0 s').

Definition srun_nil_Sstar_statement : Prop := forall c c', srun c [] c' <-> Sstar sealed c c'.

(* ---------- composition with call_preservation ---------- *)
Section Compose.
Variables (E : B.env) (pt : B.tree (B.prim * nat)).

(* Ends (JitLowerThm) with one difference, visible here: the source's final store is related to
   the starting one by GStore under a world that maps each of s's locations to itself, instead of
   being it. b0 may allocate closure cells e never makes (a removed ((lambda X B) A), let-lambda or
   let-frozen), so equality is not available. As in Ends, m1 is a parameter: the machine the
   bytecode's run reaches is the one that finishes. *)
Inductive EndsSrc (s : store) (c : config) (m1 : B.machine) : Prop :=
 | ES_ok v v' m2 s0 w : Sstar sealed c (Cfg (Ret v) [] s0) -> wext (id_world s) w -> GStore w s0 s ->
     B.next E pt m1 = B.MFinal (B.FReturn v') m2 -> VR v v' -> EndsSrc s c m1
 | ES_err x l msg tv m2 s0 w : Sstar sealed c (Cfg (Throw x) [] s0) -> wext (id_world s) w -> GStore w s0 s ->
     B.next E pt m1 = B.MFinal (B.FError (B.VExn l)) m2 ->
     B.tget l (B.m_heap m2) = Some (B.OExn msg tv) -> exn_ok x msg -> EndsSrc s c m1.

(* call_preservation with the source body b0 where it had b. Its hypotheses are kept verbatim
   (Com, CompFn of the emitted e, the argument count, entered); the two front links, D, and
   store_ok s are added.
   The first disjunct still speaks of e's configuration and MS: the bytecode is in step
   with a run of e, and that disjunct says nothing about b0. The second is about b0.
   Does NOT say:
   - that b0 diverges when the bytecode does. call_preservation ties the bytecode's divergence to
     e's run (MS at every n); the gap is KRef's partial correctness: e may diverge silently where
     b0 returns (OB-JIT-LOWER-TERM);
   - that b0's final store equals s;
   - anything about b0 against the SOURCE store. Under Com's FunRel every function s defines is
     accepted code, so the callees b0 calls are the LOWERED bodies (each definition's e), not the
     kernel's source definitions. Composing definitions with each other needs gfuns related by
     KRef rather than equal, which is not this theorem. *)
Definition call_preservation_src_statement : Prop :=
 forall s m c ps b0 b1 e args n,
  D_wf -> KRef ps b0 b1 -> KRef ps b1 e -> StoreHas s -> store_ok s ->
  Com s m -> CompFn c ps e -> List.length ps = List.length args -> entered m c args ->
  let c0 := Cfg (Eval (combine ps args) b0) [] s in
  let ce := Cfg (Eval (combine ps args) e) [] s in
  (exists c' m' k, Sstar sealed ce c' /\ TN E pt k m m' /\ (n <= k)%nat /\ MS s c' m') \/
  (exists m1, EndsSrc s c0 m1 /\ TStar E pt m m1).
End Compose.

(* ======================= the index-local interface (K00) ======================= *)
(* Statements only. Nothing below is proved; JitKRefPrim and JitKRefFund own the proofs. *)

(* Variables free in e. Binders and defun parameters scope as in `scoped`, so that scoped g e = true
   says every name in fv e is in g. *)
Fixpoint fv (e : expr) : list name := match e with
 | EVar x => [x]
 | ELam x b => filter (fun y => negb (text_eqb y x)) (fv b)
 | ELet x a b => fv a ++ filter (fun y => negb (text_eqb y x)) (fv b)
 | EIf c a b => fv c ++ fv a ++ fv b
 | EAnd a b | EOr a b | ETrap a b => fv a ++ fv b
 | ECond cl => (fix go (l : list (expr * expr)) : list name := match l with
     | [] => [] | (c, b) :: l => fv c ++ fv b ++ go l end) cl
 | EFreeze b | EType b => fv b
 | EDefun _ _ _ => []
 | EApp h args => fv h ++ (fix go (l : list expr) : list name := match l with
     | [] => [] | a :: l => fv a ++ go l end) args
 | ECall _ args => (fix go (l : list expr) : list name := match l with
     | [] => [] | a :: l => fv a ++ go l end) args
 | ENum _ | EStr _ | ESym _ | EBool _ | ENil => [] end.

(* The fundamental property at every index below k, for one expression against itself, in
   environments related on a scope g that covers its free variables, or where a free variable is
   bound on neither side. This is the hypothesis a compatibility lemma at index k may use for the
   bodies of closures it meets (VBody quantifies over j < k).
   Does NOT relate an expression to a different one, or say anything about names bound on one side
   only. *)
Definition fund_below (k : nat) : Prop :=
 forall j, (j < k)%nat -> forall w g rho0 rho e, wf_world w -> EnvRel_with (VRel j) w g rho0 rho ->
  (forall x, In x (fv e) -> In x g \/ (lookup x rho0 = None /\ lookup x rho = None)) ->
  ERel j w rho0 e rho e.

(* The generalized fundamental property, by induction on the index. It takes D_wf, as
   fundamental_statement and every compatibility statement whose proof runs store code do: without
   it a defun of a D name mid-run leaves the stores outside SRel's promises (see D_wf). *)
Definition fund_gen_statement : Prop := D_wf -> forall k, fund_below (S k).

(* A primitive's outcome on the two sides (KLSemantics.pout). A value: related values and stores
   at a world extending w. An exception: the same one (the store is the one the primitive was
   given, related at w already). Wrong on both sides, whatever the reasons. eval-kl's expression:
   the same one, evaluated in the empty environment on both sides. A resource failure: the same
   resource.
   Does NOT relate different outcome kinds, and does NOT allow the target to fail for a resource
   where the source does not: jit_profile has no heap limit, so absvector never fails for one. *)
Definition PoutRel (k : nat) (w : world) (o0 o : pout) : Prop :=
 match o0, o with
 | ORet v0 s0, ORet v s => exists w', wext w w' /\ VRel k w' v0 v /\ SRel k w' s0 s
 | OThrow x0, OThrow x => x0 = x
 | OWrong _, OWrong _ => True
 | OEval e0, OEval e => e0 = e
 | OFail r0, OFail r => r0 = r
 | _, _ => False end.

(* A primitive's result (KLSemantics.presult): both done with related outcomes, or the same IO
   request with continuations whose outcomes are related for every response. *)
Definition PrimOutRel (k : nat) (w : world) (p0 p : presult) : Prop :=
 match p0, p with
 | PDone o0, PDone o => PoutRel k w o0 o
 | PIO q0 c0, PIO q c => q0 = q /\ forall r, PoutRel k w (c0 r) (c r)
 | _, _ => False end.

(* Every table primitive under jit_rules, and every port primitive jit_rules gives (none while
   port_prim is off: JitProfile.jit_port_prims_off), maps related arguments and stores to related
   results. Proved as JitKRefPrim.prim_compat; its = case rests on
   JitEqBudgetCore.eq_budget_closed, not on eq_budget_statement. *)
Definition prim_compat_statement : Prop := forall k w,
 (forall p args0 args s0 s, Forall2 (VRel k w) args0 args -> SRel k w s0 s ->
    PrimOutRel k w (prim_rule_r R P p args0 s0) (prim_rule_r R P p args s)) /\
 (forall g n rule args0 args s0 s, port_prim R g = Some (n, rule) ->
    Forall2 (VRel k w) args0 args -> SRel k w s0 s ->
    PrimOutRel k w (rule P args0 s0) (rule P args s)).
End Equiv.
End JitKRef.
