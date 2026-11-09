(* Shen/JIT Phase 2, the lowerer's front passes (wave 1(c)): statements, reviewed and revised.
   lower.shen (d3348ce) lowers a body in three steps: share (b0 to b1, KLambda to KLambda),
   norm (b1 to a normal form n, read back as KLambda e), and emission (e to code c, which
   JitLowerRel.CompFn relates). The intermediate outputs are untrusted witnesses: a Rocq check
   decides each link for one definition. This file states what the two front links must
   establish, `KRef`, and the theorem that composes them with `call_preservation`.

   Each claim is a `Definition ..._statement : Prop`. Nothing is Admitted and nothing is assumed.
   Proved at the end of the file: the premise checks' specifications, the ground relation's
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
Module JitLowerEquiv.
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
(* ======================= proofs (Phase B, part B) ======================= *)
(* Proved here: the premises' specifications, the ground relation's lemmas, KRel_top, and, as
   explicit implications from fundamental_statement, store reflexivity and adequacy. The
   fundamental property itself and the compatibility lemmas are NOT proved here. *)

(* --- premise specifications --- *)
Theorem fresh_ok_spec : fresh_ok_spec_statement.
Proof.
 intros ns es. unfold fresh_ok. rewrite forallb_forall. split.
 - intros H e x Ie Ix. specialize (H e Ie). rewrite forallb_forall in H.
   apply negb_true_iff. apply H. exact Ix.
 - intros H e Ie. rewrite forallb_forall. intros x Ix. apply negb_true_iff. eapply H; eauto.
Qed.

Theorem no_keyword_binders_spec : no_keyword_binders_spec_statement.
Proof.
 intros e. unfold no_keyword_binders. rewrite forallb_forall. split.
 - intros H x I. apply negb_true_iff. apply H. exact I.
 - intros H x I. apply negb_true_iff. apply H. exact I.
Qed.

Theorem D_compiled_spec : D_compiled_spec_statement.
Proof.
 intros cs H f ps b I. unfold D_compiled in H. rewrite forallb_forall in H.
 specialize (H _ I). cbn in H. destruct (lookup f cs) as [c|]; [|discriminate].
 exists c. split; [reflexivity|]. apply check_fn_sound. exact H.
Qed.

(* --- runs --- *)
Lemma runs_srun : forall n c t c', runs n c t c' -> srun c t c'.
Proof. intros n c t c' H; induction H; [constructor|econstructor; eauto]. Qed.

Lemma srun_runs : forall c t c', srun c t c' -> exists n, runs n c t c'.
Proof.
 intros c t c' H; induction H as [c|c l c1 t c2 St _ [n IH]]; [exists 0%nat; constructor|].
 exists (S n). econstructor; eauto.
Qed.

Theorem srun_nil_Sstar : srun_nil_Sstar_statement.
Proof.
 intros c c'. split.
 - intro H. remember [] as t eqn:Et. unfold srun in H.
   induction H as [c|c l c1 t c2 St H IH]; [constructor|].
   destruct l as [|ev]; [|discriminate]. econstructor; [exact St|]. apply IH. exact Et.
 - intro H. induction H as [c|c c1 c2 St H IH]; [constructor|].
   change (@nil event) with (trace_of Tau ++ []). econstructor; [exact St|exact IH].
Qed.

Lemma step_from_ret_top : forall v s l c1, step_r R P (Cfg (Ret v) [] s) l c1 ->
 l = Tau /\ exists x r, resource_exn R r = Some x /\ c1 = Cfg (Throw x) [] s.
Proof.
 intros v s l c1 H. inversion H; subst; cbn in *; try discriminate.
 split; [reflexivity|]. eauto.
Qed.

Lemma no_step_from_throw_top : forall x s l c1, step_r R P (Cfg (Throw x) [] s) l c1 -> False.
Proof. intros x s l c1 H. inversion H; subst; cbn in *; discriminate. Qed.

(* --- worlds --- *)
Lemma wext_refl : forall w, wf_world w -> wext w w.
Proof. intros w H. split; [intros a A; exact A|exact H]. Qed.

Lemma In_compose : forall w1 w2 a b c, In (a, b) w1 -> In (b, c) w2 -> In (a, c) (compose_world w1 w2).
Proof.
 intros w1 w2 a b c I1 I2. unfold compose_world. apply in_flat_map. exists (a, b). split; [exact I1|].
 apply in_map_iff. exists (b, c). split; [reflexivity|]. apply filter_In. split; [exact I2|]. cbn. apply Nat.eqb_refl.
Qed.

Lemma In_compose_inv : forall w1 w2 a c, In (a, c) (compose_world w1 w2) -> exists b, In (a, b) w1 /\ In (b, c) w2.
Proof.
 intros w1 w2 a c I. unfold compose_world in I. apply in_flat_map in I as [[a' b] [I1 I2]].
 apply in_map_iff in I2 as [[b' c'] [E I3]]. cbn in E. inversion E; subst.
 apply filter_In in I3 as [I3 B]. cbn in B. apply Nat.eqb_eq in B. subst. eauto.
Qed.

Lemma nodup_fst_uniq : forall (w : world) a b b', NoDup (map fst w) -> In (a, b) w -> In (a, b') w -> b = b'.
Proof.
 induction w as [|[x y] w IH]; cbn; intros a b b' N I1 I2; [contradiction|].
 inversion N as [|? ? NI N']; subst.
 destruct I1 as [E1|I1]; destruct I2 as [E2|I2].
 - inversion E1; inversion E2; subst; reflexivity.
 - inversion E1; subst. exfalso. apply NI. apply in_map_iff. exists (a, b'). auto.
 - inversion E2; subst. exfalso. apply NI. apply in_map_iff. exists (a, b). auto.
 - eapply IH; eauto.
Qed.

Lemma nodup_snd_uniq : forall (w : world) a a' b, NoDup (map snd w) -> In (a, b) w -> In (a', b) w -> a = a'.
Proof.
 induction w as [|[x y] w IH]; cbn; intros a a' b N I1 I2; [contradiction|].
 inversion N as [|? ? NI N']; subst.
 destruct I1 as [E1|I1]; destruct I2 as [E2|I2].
 - inversion E1; inversion E2; subst; reflexivity.
 - inversion E1; subst. exfalso. apply NI. apply in_map_iff. exists (a', b). auto.
 - inversion E2; subst. exfalso. apply NI. apply in_map_iff. exists (a, b). auto.
 - eapply IH; eauto.
Qed.

Lemma filter_fst_nil : forall (w : world) b, ~ In b (map fst w) -> filter (fun q => Nat.eqb b (fst q)) w = [].
Proof.
 induction w as [|[x y] w IH]; cbn; intros b N; [reflexivity|].
 destruct (Nat.eqb b x) eqn:E; [apply Nat.eqb_eq in E; subst; exfalso; apply N; left; reflexivity|].
 apply IH. intro I; apply N; right; exact I.
Qed.

Lemma filter_fst_small : forall (w : world) b, NoDup (map fst w) ->
 filter (fun q => Nat.eqb b (fst q)) w = [] \/ exists q, filter (fun q => Nat.eqb b (fst q)) w = [q].
Proof.
 induction w as [|[x y] w IH]; cbn; intros b N; [left; reflexivity|].
 inversion N as [|? ? NI N']; subst.
 destruct (Nat.eqb b x) eqn:E.
 - apply Nat.eqb_eq in E; subst. right. exists (x, y). rewrite filter_fst_nil; [reflexivity|exact NI].
 - apply IH. exact N'.
Qed.

Lemma wf_compose : forall w1 w2, wf_world w1 -> wf_world w2 -> wf_world (compose_world w1 w2).
Proof.
 intros w1 w2 [F1 S1] [F2 S2]. induction w1 as [|[a b] w1 IH]; [split; constructor|].
 cbn in F1, S1. inversion F1 as [|? ? NF F1']; inversion S1 as [|? ? NS S1']; subst.
 destruct (IH F1' S1') as [IF IS].
 unfold compose_world. cbn [flat_map]. fold (compose_world w1 w2). cbn [fst snd].
 destruct (filter_fst_small w2 b F2) as [E|[q E]]; rewrite E; cbn [map app].
 - split; assumption.
 - assert (Iq : In q (filter (fun q => Nat.eqb b (fst q)) w2)) by (rewrite E; left; reflexivity).
   apply filter_In in Iq as [Iq Bq]. apply Nat.eqb_eq in Bq. destruct q as [b' c]. cbn in Bq. subst b'.
   split; cbn; constructor; try assumption.
   + intro I. apply in_map_iff in I as [[a' c'] [Ea I]]. cbn in Ea. subst a'.
     apply In_compose_inv in I as [b'' [J1 _]]. apply NF. apply in_map_iff. exists (a, b''). auto.
   + intro I. apply in_map_iff in I as [[a' c'] [Ec I]]. cbn in Ec. subst c'.
     apply In_compose_inv in I as [b'' [J1 J2]].
     assert (b'' = b) by (eapply nodup_snd_uniq; [exact S2|exact J2|exact Iq]). subst b''.
     apply NS. apply in_map_iff. exists (a', b). auto.
Qed.

Lemma wext_compose_id : forall s w1 w2, wext (id_world s) w1 -> wext (id_world s) w2 ->
 wext (id_world s) (compose_world w1 w2).
Proof.
 intros s w1 w2 [I1 W1] [I2 W2]. split; [|apply wf_compose; assumption].
 intros [a b] I. assert (a = b) as <-.
 { unfold id_world in I. apply in_map_iff in I as [l [E _]]. inversion E; reflexivity. }
 eapply In_compose; [apply I1|apply I2]; exact I.
Qed.

Lemma id_world_wf : forall s, wf_world (id_world s).
Proof.
 intro s. unfold id_world, wf_world. rewrite !map_map. cbn. rewrite !map_id. split; apply seq_NoDup.
Qed.

Lemma id_world_in : forall s l, (l < List.length (heap s))%nat -> In (l, l) (id_world s).
Proof. intros s l L. unfold id_world. apply in_map_iff. exists l. split; [reflexivity|]. apply in_seq. lia. Qed.

Lemma id_world_inv : forall s a b, In (a, b) (id_world s) -> a = b /\ (a < List.length (heap s))%nat.
Proof.
 intros s a b I. unfold id_world in I. apply in_map_iff in I as [l [E I]]. inversion E; subst.
 apply in_seq in I. split; [reflexivity|lia].
Qed.

(* --- the ground relation --- *)
Lemma same_id_trans : forall w1 w2 r0 r1 r, same_id w1 r0 r1 -> same_id w2 r1 r ->
 same_id (compose_world w1 w2) r0 r.
Proof.
 intros w1 w2 r0 r1 r H1 H2. unfold same_id in *.
 destruct (closure_id r0), (closure_id r1), (closure_id r); try contradiction; auto.
 eapply In_compose; eauto.
Qed.

Lemma GVal_partial : forall w f0 f as0 as1,
 GVal w (VPartial f0 as0) (VPartial f as1) <-> f0 = f /\ Forall2 (GVal w) as0 as1.
Proof.
 intros w f0 f as0 as1. cbn [GVal]. split; intros [E H]; split; try exact E.
 - revert as1 H; induction as0 as [|x0 as0 IH]; intros [|x as1] H; cbn in H; try contradiction; [constructor|].
   destruct H as [H1 H2]. constructor; [exact H1|apply IH; exact H2].
 - induction H; cbn; tauto.
Qed.

Lemma GVal_trans : GVal_trans_statement.
Proof.
 intros w1 w2 a b c W1 W2 H1 H2. split; [|apply wf_compose; assumption].
 revert b c H1 H2. induction a using value_rect'; intros b' c' H1 H2;
  destruct b'; try (cbn in H1; contradiction); destruct c'; try (cbn in H2; contradiction).
 11: { apply GVal_partial. apply GVal_partial in H1 as [E1 F1]. apply GVal_partial in H2 as [E2 F2].
   split; [congruence|]. revert args0 args1 F1 F2. induction H as [|x l Px Pl IH]; intros l1 l2 F1 F2.
   + inversion F1; subst. inversion F2; subst. constructor.
   + inversion F1; subst. inversion F2; subst. constructor; eauto. }
 all: cbn in *; try (subst; reflexivity); auto.
 - destruct H1, H2. split; eauto.
 - eapply In_compose; eauto.
 - eapply same_id_trans; eauto.
 - eapply same_id_trans; eauto.
Qed.

Lemma Forall2_trans_gen : forall {A B C} (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) (R3 : A -> C -> Prop) l1 l2 l3,
 (forall a b c, R1 a b -> R2 b c -> R3 a c) -> Forall2 R1 l1 l2 -> Forall2 R2 l2 l3 -> Forall2 R3 l1 l3.
Proof.
 intros A B C R1 R2 R3 l1 l2 l3 T F1. revert l3. induction F1; intros l3 F2; inversion F2; subst; constructor; eauto.
Qed.

Theorem GStore_trans : GStore_trans_statement.
Proof.
 intros w1 w2 s0 s1 s W1 W2 [G1 [V1 H1]] [G2 [V2 H2]]. split; [congruence|split].
 - eapply Forall2_trans_gen; [|exact V1|exact V2].
   intros [x0 a] [x1 b] [x c] [E1 A] [E2 B]; cbn in *. split; [congruence|]. eapply GVal_trans; eauto.
 - intros l0 l I. apply In_compose_inv in I as [b [I1 I2]].
   destruct (H1 _ _ I1) as (c0 & c1 & N0 & N1 & F1). destruct (H2 _ _ I2) as (c1' & c & N1' & N & F2).
   rewrite N1 in N1'. inversion N1'; subst. exists c0, c. split; [exact N0|split; [exact N|]].
   eapply Forall2_trans_gen; [|exact F1|exact F2]. intros a b' c'' A B. eapply GVal_trans; eauto.
Qed.

Lemma GVal_fo : forall w v0 v, fo v -> GVal w v0 v -> v0 = v.
Proof.
 intros w v0 v F. revert v0. induction F; intros v0 G; destruct v0; cbn in G; try contradiction; subst; try reflexivity.
 destruct G as [G1 G2]. f_equal; auto.
Qed.

(* --- the index family --- *)
Lemma leb_S_false : forall k, Nat.leb (S k) k = false.
Proof. intro k. apply Nat.leb_gt. lia. Qed.

Lemma VRel_unfold : forall k, VRel k = VBody (match k with O => fun _ _ _ _ => False | S k' => VRelF k' end) k.
Proof.
 intros [|k]; [reflexivity|]. unfold VRel.
 change (VRelF (S k) (S k)) with (if Nat.leb (S k) k then VRelF k (S k) else VBody (VRelF k) (S k)).
 rewrite leb_S_false. reflexivity.
Qed.

Theorem VRelF_index : VRelF_index_statement.
Proof.
 intro k. induction k as [|k IH]; intros j L.
 - assert (j = 0%nat) by lia. subst. reflexivity.
 - change (VRelF (S k) j) with (if Nat.leb j k then VRelF k j else VBody (VRelF k) (S k)).
   destruct (Nat.leb j k) eqn:E.
   + apply Nat.leb_le in E. apply IH. exact E.
   + apply Nat.leb_gt in E. assert (j = S k) by lia. subst.
     unfold VRel. change (VRelF (S k) (S k)) with (if Nat.leb (S k) k then VRelF k (S k) else VBody (VRelF k) (S k)).
     rewrite leb_S_false. reflexivity.
Qed.

Lemma VBody_partial : forall V k w f0 f as0 as1,
 VBody V k w (VPartial f0 as0) (VPartial f as1) <-> f0 = f /\ Forall2 (VBody V k w) as0 as1.
Proof.
 intros V k w f0 f as0 as1. cbn [VBody]. split; intros [E H]; split; try exact E.
 - revert as1 H; induction as0 as [|x0 as0 IH]; intros [|x as1] H; cbn in H; try contradiction; [constructor|].
   destruct H as [H1 H2]. constructor; [exact H1|apply IH; exact H2].
 - induction H; cbn; tauto.
Qed.

Lemma VBody_ground : forall V k w v0 v, VBody V k w v0 v -> GVal w v0 v.
Proof.
 intros V k w v0. induction v0 using value_rect'; intros v' H'; destruct v'; try (cbn in H'; contradiction).
 11: { apply GVal_partial. apply VBody_partial in H' as [E F]. split; [exact E|].
   revert args0 F. induction H as [|x l Px Pl IH]; intros l1 F; inversion F; subst; constructor; auto. }
 all: cbn in *; auto; try (destruct H'; auto; fail).
Qed.

Theorem VRel_ground : VRel_ground_statement.
Proof. intros k w v0 v H. rewrite VRel_unfold in H. eapply VBody_ground; exact H. Qed.

Lemma SRel_with_ground : forall (V1 : world -> value -> value -> Prop) w s0 s,
 (forall a b, V1 w a b -> GVal w a b) -> SRel_with V1 w s0 s -> GStore w s0 s.
Proof.
 intros V1 w s0 s G (W & H0 & H1 & Gf & Gv & Hp). split; [exact Gf|split].
 - eapply Forall2_impl; [|exact Gv]. intros [x a] [y b] [E A]; split; auto.
 - intros l0 l I. destruct (Hp _ _ I) as (c0 & c & N0 & N & F). exists c0, c. repeat split; auto.
   eapply Forall2_impl; [|exact F]. auto.
Qed.

Theorem SRel_ground : SRel_ground_statement.
Proof. intros k w s0 s H. eapply SRel_with_ground; [|exact H]. intros a b; apply VRel_ground. Qed.

Lemma SRel_with_wf : forall (V1 : world -> value -> value -> Prop) w s0 s, SRel_with V1 w s0 s -> wf_world w.
Proof. intros V1 w s0 s H; apply H. Qed.

(* --- the empty continuation --- *)
Lemma obs_top_throw : forall j w x s0 s, wf_world w -> GStore w s0 s ->
 ObsT j w (Cfg (Throw x) [] s0) (Cfg (Throw x) [] s).
Proof.
 intros j w x s0 s W G n t c' L Hr. inversion Hr as [c|n' c l c1 t' c2 St Hr']; subst.
 - split; [|split].
   + intros v s' E; discriminate.
   + intros x' s' E. inversion E; subst. exists s0, w. split; [constructor|split; [apply wext_refl; exact W|exact G]].
   + intros why N. cbn in N. discriminate.
 - exfalso. eapply no_step_from_throw_top; exact St.
Qed.

Lemma obs_top_ret : forall j w v0 v s0 s, wf_world w -> GVal w v0 v -> GStore w s0 s ->
 ObsT j w (Cfg (Ret v0) [] s0) (Cfg (Ret v) [] s).
Proof.
 intros j w v0 v s0 s W Gv G n t c' L Hr. inversion Hr as [c|n' c l c1 t' c2 St Hr']; subst.
 - split; [|split].
   + intros v' s' E. inversion E; subst. exists v0, s0, w. split; [constructor|split; [apply wext_refl; exact W|auto]].
   + intros x s' E; discriminate.
   + intros why N. cbn in N. discriminate.
 - destruct (step_from_ret_top _ _ _ _ St) as [-> [x [r [Rx ->]]]].
   inversion Hr' as [c|n'' c l c1 t'' c2 St' _]; subst.
   + split; [|split].
     * intros v' s' E; discriminate.
     * intros x' s' E. inversion E; subst. exists s0, w. split; [|split; [apply wext_refl; exact W|exact G]].
       change (trace_of Tau ++ []) with (trace_of Tau ++ @nil event). econstructor; [|constructor].
       eapply (step_r_resource _ _ (Cfg (Ret v0) [] s0) r); [reflexivity|exact Rx].
     * intros why N. cbn in N. discriminate.
   + exfalso. eapply no_step_from_throw_top; exact St'.
Qed.

Theorem KRel_top : KRel_top_statement.
Proof.
 intros k w _ j L w' [I W]. split.
 - intros v0 v s0 s HV HS. rewrite (VRelF_index k j L) in HV, HS.
   apply obs_top_ret; [exact W|apply VRel_ground with (k := j); exact HV|].
   eapply SRel_with_ground; [|exact HS]. intros a b; apply VRel_ground.
 - intros x s0 s HS. rewrite (VRelF_index k j L) in HS.
   apply obs_top_throw; [exact W|]. eapply SRel_with_ground; [|exact HS]. intros a b; apply VRel_ground.
Qed.

(* --- transport between index families --- *)
Lemma KRel_with_ext : forall V V' j w K0 K, (forall i, (i <= j)%nat -> V i = V' i) ->
 KRel_with V j w K0 K -> KRel_with V' j w K0 K.
Proof.
 intros V V' j w K0 K Eq H i L w' Hw. destruct (H i L w' Hw) as [A B].
 rewrite <- (Eq i L). split; assumption.
Qed.

Lemma ERel_with_ext : forall V V' j w r0 e0 r e, (forall i, (i <= j)%nat -> V i = V' i) ->
 ERel_with V j w r0 e0 r e -> ERel_with V' j w r0 e0 r e.
Proof.
 intros V V' j w r0 e0 r e Eq H j' L w' Hw K0 K HK s0 s HS.
 rewrite <- (Eq j' L) in HS. apply H; auto.
 eapply KRel_with_ext; [|exact HK]. intros i Li. symmetry. apply Eq. lia.
Qed.

(* --- reflexivity of values and stores, from the fundamental property --- *)
Section FromFundamental.
Hypothesis F : fundamental_statement.

Lemma same_id_refl : forall n w rho, eok n rho -> (forall l, (l < n)%nat -> In (l, l) w) -> same_id w rho rho.
Proof.
 intros n w rho E H. unfold same_id. destruct rho as [|[kk vv] rr]; cbn; [exact I|].
 destruct vv; try exact I. destruct (text_eqb kk id_key); [|exact I].
 apply H. inversion E; subst. exact H2.
Qed.

Lemma Forall2_refl_env : forall (Q : value -> Prop) (R2 : value -> value -> Prop) (rho : lenv),
 Forall (fun p => Q (snd p)) rho -> (forall v, Q v -> R2 v v) ->
 Forall2 (fun p0 p => fst p0 = fst p /\ R2 (snd p0) (snd p)) rho rho.
Proof. intros Q R2 rho H T. induction H; constructor; auto. Qed.

Lemma vrefl : D_wf -> forall v n k w, wf_world w -> (forall l, (l < n)%nat -> In (l, l) w) -> vok n v -> VRel k w v v.
Proof.
 intros DW v. induction v using value_rect'; intros nb k w W Hw Ok; rewrite VRel_unfold.
 11: { apply VBody_partial. split; [reflexivity|]. cbn in Ok. apply fold_lok in Ok.
   induction H as [|x l Px Pl IH]; [constructor|]. inversion Ok; subst. constructor; [|apply IH; auto].
   rewrite <- (VRel_unfold k). eapply Px; eauto. }
 all: cbn [VBody]; auto; try (apply Hw; exact Ok).
 - cbn in Ok. destruct Ok as [O1 O2].
   split; rewrite <- (VRel_unfold k); [eapply IHv1|eapply IHv2]; eauto.
 - cbn in Ok. apply fold_eok in Ok. split; [eapply same_id_refl; eauto|].
   destruct k as [|k]; [intros j L; lia|].
   intros j L w' [Iw' W'] a0 a A. cbv beta iota in A |- *.
   rewrite (VRelF_index k j ltac:(lia)) in A.
   eapply ERel_with_ext with (V := VRelF j); [intros i Li; rewrite !VRelF_index by lia; reflexivity|].
   apply F; [exact DW|exact W'|]. constructor; [split; [reflexivity|exact A]|].
   clear -H Ok Iw' W' Hw DW. induction H as [|[y u] rr Pu Prr IH]; [constructor|].
   inversion Ok; subst. constructor; [split; [reflexivity|]|apply IH; auto].
   cbn in *. apply (Pu nb); [exact W'|intros l Ll; apply Iw'; apply Hw; exact Ll|assumption].
 - cbn in Ok. apply fold_eok in Ok. split; [eapply same_id_refl; eauto|].
   destruct k as [|k]; [intros j L; lia|].
   intros j L w' [Iw' W']. cbv beta iota.
   eapply ERel_with_ext with (V := VRelF j); [intros i Li; rewrite !VRelF_index by lia; reflexivity|].
   apply F; [exact DW|exact W'|].
   clear -H Ok Iw' W' Hw DW. induction H as [|[y u] rr Pu Prr IH]; [constructor|].
   inversion Ok; subst. constructor; [split; [reflexivity|]|apply IH; auto].
   cbn in *. apply (Pu nb); [exact W'|intros l Ll; apply Iw'; apply Hw; exact Ll|assumption].
Qed.

Theorem store_refl_of_fundamental : store_refl_statement.
Proof.
 intros k s DW HS [Hh Hg]. unfold SRel, SRel_with.
 split; [apply id_world_wf|split; [exact HS|split; [exact HS|split; [reflexivity|split]]]].
 - eapply Forall2_refl_env; [exact Hg|]. intros v Ov. eapply vrefl; [exact DW|apply id_world_wf| |exact Ov].
   intros l L; apply id_world_in; exact L.
 - intros l0 l I. apply id_world_inv in I as [<- L].
   destruct (nth_error (heap s) l0) as [c|] eqn:N; [|apply nth_error_None in N; lia].
   exists c, c. split; [reflexivity|split; [reflexivity|]].
   assert (Oc : lok (List.length (heap s)) c).
   { rewrite Forall_forall in Hh. apply Hh. eapply nth_error_In; exact N. }
   clear -Oc DW F. induction Oc as [|x c Ox Oc IH]; constructor; [|exact IH].
   eapply vrefl; [exact DW|apply id_world_wf| |exact Ox]. intros l L; apply id_world_in; exact L.
Qed.

Lemma fo_vok : forall n v, fo v -> vok n v.
Proof. intros n v H; induction H; cbn; auto. Qed.

Lemma lookup_In : forall x (rho : lenv) v, lookup x rho = Some v -> In (x, v) rho.
Proof.
 induction rho as [|[y u] rho IH]; cbn; intros v E; [discriminate|].
 destruct (text_eqb x y) eqn:T; [apply text_eqb_eq in T; subst; inversion E; subst; left; reflexivity|right; auto].
Qed.

Theorem adequacy_of_fundamental : adequacy_statement.
Proof.
 intros g e0 e rho s DW HK Hfo Hdom HS Hok.
 assert (Main : forall n t c', runs n (Cfg (Eval rho e) [] s) t c' -> ObsT (S n) (id_world s) (Cfg (Eval rho e0) [] s) (Cfg (Eval rho e) [] s)).
 { intros n t c' _. eapply (HK (S n) (id_world s) rho rho (id_world_wf s)).
   - intros x Ix. destruct (Hdom x Ix) as [v Lv]. exists v, v. split; [exact Lv|split; [exact Lv|]].
     eapply vrefl with (n := 0%nat); [exact DW|apply id_world_wf|intros l L; lia|].
     apply fo_vok. apply lookup_In in Lv. rewrite Forall_forall in Hfo. exact (Hfo _ Lv).
   - apply le_n.
   - apply wext_refl, id_world_wf.
   - apply KRel_top, id_world_wf.
   - exact (store_refl_of_fundamental (S n) s DW HS Hok). }
 split.
 - intros v s' Hr Fv. destruct (srun_runs _ _ _ Hr) as [n Hn].
   destruct (Main _ _ _ Hn n [] _ (Nat.lt_succ_diag_r n) Hn) as [A _].
   destruct (A v s' eq_refl) as (v0 & s0 & w' & S0 & Wx & Gv & Gs).
   rewrite (GVal_fo _ _ _ Fv Gv) in S0. exists s0, w'. auto.
 - intros x s' Hr. destruct (srun_runs _ _ _ Hr) as [n Hn].
   destruct (Main _ _ _ Hn n [] _ (Nat.lt_succ_diag_r n) Hn) as [_ [B _]].
   destruct (B x s' eq_refl) as (s0 & w' & S0 & Wx & Gs). exists s0, w'. auto.
Qed.
End FromFundamental.

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
(* The composition, as an explicit implication from the fundamental property: it is proved here
   that fundamental_statement implies call_preservation_src_statement. The fundamental property is
   NOT proved here. *)
Lemma VR_fo : forall v v', VR v v' -> fo v.
Proof. intros v v' H; induction H; constructor; auto. Qed.

Lemma ArgsAt_fo : forall st a args, ArgsAt st a args -> Forall fo args.
Proof. intros st a args H; induction H; constructor; [eapply VR_fo; eauto|auto]. Qed.

Lemma combine_fo : forall (ps : list name) args, Forall fo args -> Forall (fun p => fo (snd p)) (combine ps args).
Proof.
 induction ps as [|x ps IH]; intros [|v args] H; cbn; try apply Forall_nil.
 inversion H; subst. apply Forall_cons; [exact H2|apply IH; exact H3].
Qed.

Lemma lookup_combine : forall (ps : list name) (args : list value) x,
 List.length ps = List.length args -> In x ps -> exists v, lookup x (combine ps args) = Some v.
Proof.
 induction ps as [|y ps IH]; intros [|v args] x L I; cbn in *; try contradiction; try discriminate.
 destruct (text_eqb x y) eqn:T; [eauto|]. destruct I as [Ex|I].
 - subst. rewrite text_eqb_refl in T. discriminate.
 - apply IH; [lia|exact I].
Qed.

Theorem call_preservation_src_of_fundamental : fundamental_statement -> call_preservation_src_statement.
Proof.
 intros F s m c ps b0 b1 e args n DW K01 K1e HS Hok Cm Cf L En c0 ce.
 pose proof (call_preservation E pt sealed s m c ps e args n Cm Cf L En) as CP. cbv zeta in CP.
 destruct CP as [H|[m1 [HE HT]]]; [left; exact H|right; exists m1; split; [|exact HT]].
 assert (Hfo : Forall (fun p => fo (snd p)) (combine ps args)).
 { apply combine_fo. destruct En as [_ [_ [_ Aa]]]. eapply ArgsAt_fo; exact Aa. }
 assert (Hdom : forall x, In x ps -> exists v, lookup x (combine ps args) = Some v) by (intros; apply lookup_combine; auto).
 destruct (adequacy_of_fundamental F ps b1 e (combine ps args) s DW K1e Hfo Hdom HS Hok) as [A1 B1].
 destruct (adequacy_of_fundamental F ps b0 b1 (combine ps args) s DW K01 Hfo Hdom HS Hok) as [A0 B0].
 destruct HE as [v v' m2 Ss Nf Vr|x l msg tv m2 Ss Nf Lh Xo].
 - apply srun_nil_Sstar in Ss. pose proof (VR_fo _ _ Vr) as Fv.
   destruct (A1 v s Ss Fv) as (s1 & w2 & S1 & W2 & G2).
   destruct (A0 v s1 S1 Fv) as (s0 & w1 & S0 & W1 & G1).
   eapply ES_ok with (s0 := s0) (w := compose_world w1 w2); [apply srun_nil_Sstar; exact S0| | |exact Nf|exact Vr].
   + apply wext_compose_id; assumption.
   + eapply GStore_trans; [exact (proj2 W1)|exact (proj2 W2)|exact G1|exact G2].
 - apply srun_nil_Sstar in Ss.
   destruct (B1 x s Ss) as (s1 & w2 & S1 & W2 & G2).
   destruct (B0 x s1 S1) as (s0 & w1 & S0 & W1 & G1).
   eapply ES_err with (s0 := s0) (w := compose_world w1 w2); [apply srun_nil_Sstar; exact S0| | |exact Nf|exact Lh|exact Xo].
   + apply wext_compose_id; assumption.
   + eapply GStore_trans; [exact (proj2 W1)|exact (proj2 W2)|exact G1|exact G2].
Qed.
End Compose.
End Equiv.
End JitLowerEquiv.
