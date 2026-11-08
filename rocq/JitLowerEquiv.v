(* Shen/JIT Phase 2, the lowerer's front passes: STATEMENTS ONLY (wave 1(c), Phase A).
   lower.shen (d3348ce) lowers a body in three steps: share (b0 to b1, KLambda to KLambda),
   norm (b1 to a normal form n, read back as KLambda e), and emission (e to code c, which
   JitLowerRel.CompFn relates). The intermediate outputs are untrusted witnesses: a Rocq check
   decides each link for one definition. This file states what the two front links must
   establish, `KRef`, and the theorem that composes them with `call_preservation`.

   Nothing here is proved, nothing is Admitted and nothing is assumed. Each claim is a
   `Definition ..._statement : Prop`; Phase B proves them. The definitions are ordinary
   definitions, which is all this file adds to the global context.

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
     first-order observation and composes there, where the relation, `GStore`, is transitive. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm.
Import ListNotations.
Module JitLowerEquiv.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitLowerKont.JitLowerKont JitLowerPrim.JitLowerPrim
 JitLowerStep.JitLowerStep JitLowerThm.JitLowerThm.
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
(* Values: first-order data equal, vectors by the world, closures only by kind.
   Does NOT say: anything about a closure's body or environment. *)
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
 | VLam _ _ _, VLam _ _ _ => True
 | VFrozen _ _, VFrozen _ _ => True
 | VPartial f0 as0, VPartial f as1 => f0 = f /\
     (fix go (l0 l : list value) {struct l0} : Prop := match l0, l with
      | [], [] => True
      | x0 :: r0, x :: r => GVal w x0 x /\ go r0 r
      | _, _ => False end) as0 as1
 | VExn x0, VExn x => x0 = x
 | _, _ => False end.

(* Stores: the same function table, the same global names in the same order with GVal-related
   values, and cells related by the world. Does NOT say: anything about cells outside the world
   (garbage, or cells only one side made), or that the world maps an old location to itself. *)
Definition GStore (w : world) (s0 s : store) : Prop :=
 gfuns s0 = gfuns s /\
 Forall2 (fun p0 p => fst p0 = fst p /\ GVal w (snd p0) (snd p)) (gvals s0) (gvals s) /\
 (forall l0 l, In (l0, l) w -> exists c0 c, nth_error (heap s0) l0 = Some c0 /\
    nth_error (heap s) l = Some c /\ Forall2 (GVal w) c0 c).

(* ---------- observation ---------- *)
(* Every target run of fewer than k steps that reaches a terminal state is matched by a source
   run with the same IO trace to a terminal state of the same kind: a GVal-related value, the
   same exception, or a wrong state, with GStore-related stores.
   Does NOT say: that a diverging target has a diverging source (termination-insensitive, see the
   report), anything about infinite IO, or which wrong state. *)
Definition Obs (k : nat) (c0 c : config) : Prop :=
 forall n t c', (n < k)%nat -> runs n c t c' ->
  (forall v s, c' = Cfg (Ret v) [] s -> exists v0 s0 w,
     srun c0 t (Cfg (Ret v0) [] s0) /\ wf_world w /\ GVal w v0 v /\ GStore w s0 s) /\
  (forall x s, c' = Cfg (Throw x) [] s -> exists s0 w,
     srun c0 t (Cfg (Throw x) [] s0) /\ wf_world w /\ GStore w s0 s) /\
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
  (forall v0 v s0 s, V j w' v0 v -> SRel_with (V j) w' s0 s -> Obs j (Cfg (Ret v0) K0 s0) (Cfg (Ret v) K s)) /\
  (forall x s0 s, SRel_with (V j) w' s0 s -> Obs j (Cfg (Throw x) K0 s0) (Cfg (Throw x) K s)).

(* Expressions: under related continuations and stores, the two evaluations are observably related. *)
Definition ERel_with (k : nat) (w : world) (rho0 : lenv) (e0 : expr) (rho : lenv) (e : expr) : Prop :=
 forall j, (j <= k)%nat -> forall w', wext w w' -> forall K0 K, KRel_with j w' K0 K ->
  forall s0 s, SRel_with (V j) w' s0 s -> Obs j (Cfg (Eval rho0 e0) K0 s0) (Cfg (Eval rho e) K s).

(* Values at index k. A lambda or a frozen body is related by what it does when applied, at
   every lower index, so two bodies rewritten differently can be related.
   Does NOT relate a lambda to a partial application or to a frozen body, even where they would
   behave alike: = tells them apart. *)
Definition VBody (k : nat) (w : world) : value -> value -> Prop :=
 fix go (v0 v : value) {struct v0} : Prop :=
 match v0, v with
 | VNum a, VNum b => a = b
 | VSym a, VSym b => a = b
 | VBool a, VBool b => a = b
 | VStr a, VStr b => a = b
 | VNil, VNil => True
 | VCons a0 d0, VCons a d => go a0 a /\ go d0 d
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
      | x0 :: r0, x :: r => go x0 x /\ gol r0 r
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
   Does NOT say: that e diverges only if e0 does; that the two take comparable numbers of steps
   or have comparable continuations at any intermediate point (inlining changes both); anything
   about IO beyond identical traces on terminating runs; anything about states outside D. *)
Definition KRef (g : list name) (e0 e : expr) : Prop :=
 forall k w rho0 rho, wf_world w -> EnvRel_with (VRel k) w g rho0 rho -> ERel k w rho0 e0 rho e.

(* ---------- premises, as decidable checks ---------- *)
(* Names the lowerer makes. `shen-jit.lower.fresh` is (concat Prefix N) with N counting from 1
   per definition, so a reserved name is a prefix followed by decimal digits; the fixed names are
   norm's inlining marker and KLPort's closure-identity key. *)
Definition lowerer_prefixes : list name :=
 map of_string ["shen-jit.lower.else"; "shen-jit.lower.exception"; "shen-jit.lower.arg";
                "shen-jit.lower.head"; "shen-jit.lower.partial"]%string.
Definition lowerer_fixed : list name := [of_string "shen-jit.lower.inlining"; id_key].

Fixpoint prefixb (p t : text) : bool := match p, t with
 | [], _ => true
 | a :: p, b :: t => N.eqb a b && prefixb p t
 | _ :: _, [] => false end.
Definition digitb (c : N) : bool := (N.leb 48 c && N.leb c 57)%bool.
Definition fresh_shape (p x : name) : bool :=
 prefixb p x && negb (Nat.eqb (List.length x) (List.length p)) && forallb digitb (skipn (List.length p) x).
Definition reserved (x : name) : bool :=
 existsb (fun p => fresh_shape p x) lowerer_prefixes || existsb (text_eqb x) lowerer_fixed.

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
Definition fresh_ok (es : list expr) : bool :=
 forallb (fun e => forallb (fun x => negb (reserved x)) (names e)) es.

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

(* D names only sealed functions, so no defun can replace them during a run. KRel and SRel make
   promises only about stores meeting D, so every statement whose proof runs store code (a call,
   eval-kl, a partial application, a stored closure, a defun) takes D_sealed: without it a defun
   of a D name mid-run leaves the stores outside those promises. *)
Definition D_sealed : Prop := Forall (fun p => In (fst p) sealed) D.

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

(* Every location a store's cells and globals mention is a cell of it, closures' identities included. *)
Definition id_world (s : store) : world := map (fun l => (l, l)) (seq 0 (List.length (heap s))).

(* ======================= statements (Phase B proves them) ======================= *)

(* --- the premises' own specifications --- *)
Definition fresh_ok_spec_statement : Prop := forall es,
 fresh_ok es = true <-> (forall e x, In e es -> In x (names e) -> reserved x = false).

Definition no_keyword_binders_spec_statement : Prop := forall e,
 no_keyword_binders e = true <-> (forall x, In x (binders e) -> keyword x = false).

(* Sealed definitions are never redefined: defun refuses a sealed name (jit_rules option 5), and
   gfuns changes only by defun, including through eval-kl, so this is a lemma, not a premise. *)
Definition sealed_stable_statement : Prop := forall c t c' f,
 srun c t c' -> In f sealed -> lookup f (gfuns (mem c')) = lookup f (gfuns (mem c)).

Definition storehas_stable_statement : Prop := forall c t c',
 D_sealed -> srun c t c' -> StoreHas (mem c) -> StoreHas (mem c').

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
 D_sealed -> wf_world w -> EnvRelAll k w rho0 rho -> ERel k w rho0 e rho e.
(* Not a corollary of fundamental_statement as stated: a closure captures the whole environment,
   and KRef relates only g. Phase B needs the fundamental lemma in a scoped form too. *)
Definition KRef_refl_statement : Prop := forall g e, D_sealed -> scoped g e = true -> KRef g e e.
(* Every location a value mentions, through pairs, partial applications and closure
   environments (closure identities included), is below n. *)
Fixpoint locs_below (n : nat) (v : value) {struct v} : Prop :=
 match v with
 | VVec l => (l < n)%nat
 | VCons a d => locs_below n a /\ locs_below n d
 | VLam _ _ r | VFrozen _ r => (fix go (r : lenv) : Prop := match r with
     | [] => True | (_, x) :: r => locs_below n x /\ go r end) r
 | VPartial _ xs => (fix go (xs : list value) : Prop := match xs with
     | [] => True | x :: xs => locs_below n x /\ go xs end) xs
 | _ => True end.
Definition store_closed (s : store) : Prop :=
 Forall (fun p => locs_below (List.length (heap s)) (snd p)) (gvals s) /\
 Forall (Forall (locs_below (List.length (heap s)))) (heap s).
(* A closed store meeting D is related to itself at the identity world. *)
Definition store_refl_statement : Prop := forall k s,
 D_sealed -> StoreHas s -> store_closed s -> SRel k (id_world s) s s.

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
 D_sealed -> KRef g a0 a -> KRef g h0 h -> KRef g (ETrap a0 h0) (ETrap a h).
Definition compat_lambda_statement : Prop := forall g x b0 b,
 KRef (x :: g) b0 b -> KRef g (ELam x b0) (ELam x b).
Definition compat_freeze_statement : Prop := forall g b0 b, KRef g b0 b -> KRef g (EFreeze b0) (EFreeze b).
(* Named calls cover `do`, `thaw` and `protect`, which Búri's KLambda has as ordinary calls. *)
Definition compat_call_statement : Prop := forall g f as0 as1,
 D_sealed -> Forall2 (KRef g) as0 as1 -> KRef g (ECall f as0) (ECall f as1).
Definition compat_app_statement : Prop := forall g h0 h as0 as1,
 D_sealed -> KRef g h0 h -> Forall2 (KRef g) as0 as1 -> KRef g (EApp h0 as0) (EApp h as1).
(* A defun is not rewritten under (lower.shen rejects a nested defun): only reflexivity. *)
Definition compat_defun_statement : Prop := forall g f ps b, D_sealed -> KRef g (EDefun f ps b) (EDefun f ps b).
Definition KRef_scope_statement : Prop := forall g g' e0 e, incl g g' -> KRef g e0 e -> KRef g' e0 e.

(* --- adequacy: what one link says about a whole run from the same start --- *)
(* From the same environment of first-order values and the same store, a target run to a value
   or an exception is matched by a source run to the same value or exception, with GStore-related
   final stores. Uses store_refl_statement, so fundamental_statement, for the store. *)
Inductive fo : value -> Prop :=
 | fo_num n : fo (VNum n) | fo_sym x : fo (VSym x) | fo_bool b : fo (VBool b)
 | fo_str t : fo (VStr t) | fo_nil : fo VNil | fo_cons a d : fo a -> fo d -> fo (VCons a d).

Definition adequacy_statement : Prop := forall g e0 e rho s,
 D_sealed -> KRef g e0 e -> Forall (fun p => fo (snd p)) rho -> (forall x, In x g -> exists v, lookup x rho = Some v) ->
 StoreHas s -> store_closed s ->
 (forall v s', srun (Cfg (Eval rho e) [] s) [] (Cfg (Ret v) [] s') -> fo v ->
    exists s0 w, srun (Cfg (Eval rho e0) [] s) [] (Cfg (Ret v) [] s0) /\ wf_world w /\ GStore w s0 s') /\
 (forall x s', srun (Cfg (Eval rho e) [] s) [] (Cfg (Throw x) [] s') ->
    exists s0 w, srun (Cfg (Eval rho e0) [] s) [] (Cfg (Throw x) [] s0) /\ wf_world w /\ GStore w s0 s').

Definition srun_nil_Sstar_statement : Prop := forall c c', srun c [] c' <-> Sstar sealed c c'.

(* ---------- composition with call_preservation ---------- *)
Section Compose.
Variables (E : B.env) (pt : B.tree (B.prim * nat)).

(* Ends (JitLowerThm) with one difference, visible here: the source's final store is related to
   the starting one by GStore under some world, instead of being it. b0 may allocate closure
   cells e never makes (a removed ((lambda X B) A), let-lambda or let-frozen), so equality is
   not available. Like Ends, the machine m1 of each constructor is bound inside it. *)
Inductive EndsSrc (s : store) (c : config) : Prop :=
 | ES_ok v v' m1 m2 s0 w : Sstar sealed c (Cfg (Ret v) [] s0) -> wf_world w -> GStore w s0 s ->
     B.next E pt m1 = B.MFinal (B.FReturn v') m2 -> VR v v' -> EndsSrc s c
 | ES_err x l msg tv m1 m2 s0 w : Sstar sealed c (Cfg (Throw x) [] s0) -> wf_world w -> GStore w s0 s ->
     B.next E pt m1 = B.MFinal (B.FError (B.VExn l)) m2 ->
     B.tget l (B.m_heap m2) = Some (B.OExn msg tv) -> exn_ok x msg -> EndsSrc s c.

(* call_preservation with the source body b0 where it had b. Its hypotheses are kept verbatim
   (Com, CompFn of the emitted e, the argument count, entered); the two front links, D, and
   store_closed (no value in s names a cell s lacks; expected of reachable stores, not proved) are added.
   The first disjunct still speaks of e's configuration and MS: the bytecode is in step
   with a run of e, and that disjunct says nothing about b0. The second is about b0.
   Does NOT say: that b0 diverges when the bytecode does (neither does call_preservation); that
   b0's final store equals s. *)
Definition call_preservation_src_statement : Prop :=
 forall s m c ps b0 b1 e args n,
  D_sealed -> KRef ps b0 b1 -> KRef ps b1 e -> StoreHas s -> store_closed s ->
  Com s m -> CompFn c ps e -> List.length ps = List.length args -> entered m c args ->
  let c0 := Cfg (Eval (combine ps args) b0) [] s in
  let ce := Cfg (Eval (combine ps args) e) [] s in
  (exists c' m' k, Sstar sealed ce c' /\ TN E pt k m m' /\ (n <= k)%nat /\ MS s c' m') \/
  (exists m1, EndsSrc s c0 /\ TStar E pt m m1).
End Compose.
End Equiv.
End JitLowerEquiv.
