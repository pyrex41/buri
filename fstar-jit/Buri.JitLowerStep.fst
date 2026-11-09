(* Port of rocq/JitLowerStep.v: the definitions of the one-step simulation (measure, source and
   target step closures, function table relation, MS, Out) and the small lemmas the
   multi-step theorem uses. The simulation theorem `sim` itself (Rocq: about 1,100 lines of
   proof) is not proved here: its statement is in Buri.Unfinished.
   Encoding: Sstar, TStar, MS and Out are informative F* types. Out's disjunction
   `TPlus m m' \/ (m' = m /\ msr c' < msr c)` is an `either`, because the multi-step proof
   branches on it to build a Type-valued result (a Rocq Prop can be case-split into a Prop). *)
module Buri.JitLowerStep
open Buri.Lib
open Buri.Observation
open Buri.KLSyntax
open Buri.KLValue
open Buri.KLSemantics
open Buri.KLPort
open Buri.JitProfile
open Buri.JitLowerRel
open Buri.JitLowerKont
open Buri.JitLowerPrim
module B = Buri.JitBytecode

(* ---------- a measure ---------- *)
let rec esize (e : expr) : Tot nat (decreases e) = match e with
  | ELet _ a b -> 2 + esize a + esize b
  | EIf c a b -> 3 + esize c + esize a + esize b
  | EAnd a b | EOr a b -> 3 + esize a + esize b
  | ECond cl -> 1 + esize_cl cl
  | EType a -> 1 + esize a
  | ECall _ args -> 1 + esize_l args
  | _ -> 1
and esize_cl (l : list (expr & expr)) : Tot nat (decreases l) = match l with
  | [] -> 0 | (c, b) :: l' -> 2 + esize c + esize b + esize_cl l'
and esize_l (l : list expr) : Tot nat (decreases l) = match l with
  | [] -> 0 | a :: l' -> 1 + esize a + esize_l l'
let fsize (f : frame) : nat = match f with
  | KLet _ b _ -> 1 + esize b
  | KIf a b _ -> 1 + esize a + esize b
  | KAnd b _ | KOr b _ -> 2 + esize b
  | KAndR | KOrR -> 1
  | KCond b rest _ -> 1 + esize b + esize (ECond rest)
  | KCallArgs f _ es _ -> esize (ECall f es)
  | _ -> 1
let rec ksize (k : list frame) : nat = match k with [] -> 0 | f :: k -> fsize f + ksize k
let msr (c : config) : nat = match c.ctl with
  | Eval _ e -> 1 + esize e + ksize c.kont
  | _ -> 1 + ksize c.kont

let rr (sealed : list name) = jit_rules sealed
let pr = jit_profile

noeq type sstar (sealed : list name) : config -> config -> Type0 =
  | SS_refl : c:config -> sstar sealed c c
  | SS_step : c:config -> c1:config -> c2:config -> step_r (rr sealed) pr c Tau c1 -> sstar sealed c1 c2 ->
      sstar sealed c c2

let rec sstar_trans (#sealed : list name) (#a #b #c : config) (h : sstar sealed a b) (k : sstar sealed b c)
  : Tot (sstar sealed a c) (decreases h) =
  match h with
  | SS_refl _ -> k
  | SS_step _ c1 _ st rest -> SS_step a c1 c st (sstar_trans rest k)

let s1 (#sealed : list name) (c c' c2 : config) (h : squash (next_r (rr sealed) pr c == MTau c')) (k : sstar sealed c' c2)
  : sstar sealed c c2 = SS_step c c' c2 (Step_r_tau c c' ()) k
let s1' (#sealed : list name) (c c' : config) (h : squash (next_r (rr sealed) pr c == MTau c'))
  : sstar sealed c c' = s1 c c' c' h (SS_refl c')

let tS (e : B.env) (pt : B.tree (B.prim & nat)) (m m' : B.machine) : prop = B.next e pt m == B.MTau m'
noeq type tStar (e : B.env) (pt : B.tree (B.prim & nat)) : B.machine -> B.machine -> Type0 =
  | TS_refl : m:B.machine -> tStar e pt m m
  | TS_step : m:B.machine -> m1:B.machine -> m2:B.machine -> squash (tS e pt m m1) -> tStar e pt m1 m2 ->
      tStar e pt m m2
noeq type tPlus (e : B.env) (pt : B.tree (B.prim & nat)) (m m' : B.machine) : Type0 =
  | TPlus : m1:B.machine -> squash (tS e pt m m1) -> tStar e pt m1 m' -> tPlus e pt m m'

let rec tStar_trans (#e : B.env) (#pt : B.tree (B.prim & nat)) (#a #b #c : B.machine)
  (h : tStar e pt a b) (k : tStar e pt b c) : Tot (tStar e pt a c) (decreases h) =
  match h with
  | TS_refl _ -> k
  | TS_step _ m1 _ t rest -> TS_step a m1 c () (tStar_trans rest k)
let tPlus_star (#e : B.env) (#pt : B.tree (B.prim & nat)) (#a #b : B.machine) (h : tPlus e pt a b) : tStar e pt a b =
  match h with TPlus m1 _ rest -> TS_step a m1 b () rest

(* The function table, for this store. It reads only the machine's function table and heap, so it
   is stated over those two (funRel_gh), which makes funRel_same a congruence. *)
let funRel_gh (s : store) (gfun : B.tree B.val_) (heap : B.tree B.obj) : prop =
  (forall f ps b. lookup f s.gfuns == Some (FUser ps b) ==> (exists l c caps.
     B.tget (B.sym_of_text f) gfun == Some (B.VClo l) /\
     B.tget l heap == Some (B.OClo c caps) /\
     B.code_arity c = length ps /\ B.code_entry c == None /\ compFn c ps b)) /\
  (forall f. lookup f s.gfuns == None ==> (forall l. ~(B.tget (B.sym_of_text f) gfun == Some (B.VClo l)))) /\
  (forall f p. lookup f s.gfuns == Some (FPrim p) ==> prim_of_name f == Some p) /\
  (forall f p. prim_of_name f == Some p ==> lookup f s.gfuns == Some (FPrim p))
let funRel (s : store) (m : B.machine) : prop = funRel_gh s m.B.m_gfun m.B.m_heap
let com (s : store) (m : B.machine) : prop = m.B.m_handlers == [] /\ funRel s m

let funRel_same (s : store) (m m' : B.machine)
  : Lemma (requires m'.B.m_gfun == m.B.m_gfun /\ m'.B.m_heap == m.B.m_heap /\ funRel s m) (ensures funRel s m') = ()

let fp (m : B.machine) = m.B.m_fp
let st (m : B.machine) = m.B.m_stack
let code (m : B.machine) = m.B.m_code
let cs (m : B.machine) = m.B.m_conts

noeq type mS (s : store) : config -> B.machine -> Type0 =
  | MS_eval : g:env -> top:nat -> e:expr -> dst:dest -> r2:list B.instr -> rho:lenv -> k:list frame ->
      w:(nat -> prop) -> m:B.machine ->
      squash (com s m) -> comp (code m) g top e dst m.B.m_rest r2 -> squash (menv (fp m) (st m) g rho) ->
      squash (envBelow g top) -> squash (above (fp m) top w) -> kC (code m) (fp m) (st m) (cs m) w dst r2 k ->
      mS s (cfg (Eval rho e) k s) m
  | MS_test : g:env -> top:nat -> e:expr -> l:nat -> r2:list B.instr -> rho:lenv -> k:list frame ->
      w:(nat -> prop) -> m:B.machine ->
      squash (com s m) -> compT (code m) g top e l m.B.m_rest r2 -> squash (menv (fp m) (st m) g rho) ->
      squash (envBelow g top) -> squash (above (fp m) top w) -> tK (code m) (fp m) (st m) (cs m) w true l r2 k ->
      mS s (cfg (Eval rho e) k s) m
  | MS_op : g:env -> top:nat -> e:expr -> o:B.operand -> top2:nat -> r2:list B.instr -> rho:lenv ->
      k:list frame -> w:(nat -> prop) -> m:B.machine ->
      squash (com s m) -> compOp (code m) g top e o top2 m.B.m_rest r2 -> squash (menv (fp m) (st m) g rho) ->
      squash (envBelow g top) -> squash (above (fp m) top w) -> kD (code m) (fp m) (st m) (cs m) w o r2 k ->
      mS s (cfg (Eval rho e) k s) m
  | MS_ret : v:value -> v':B.val_ -> o:B.operand -> k:list frame -> w:(nat -> prop) -> m:B.machine ->
      squash (com s m) -> squash (read_o (code m) (fp m) (st m) o == Some v') -> vr v v' ->
      kD (code m) (fp m) (st m) (cs m) w o m.B.m_rest k ->
      mS s (cfg (Ret v) k s) m

noeq type out (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (c : config) (m : B.machine) : Type0 =
  | O_step : c':config -> m':B.machine -> sstar sealed c c' ->
      either (tPlus e pt m m') (squash (m' == m /\ msr c' < msr c)) -> mS s c' m' -> out e pt sealed s c m
  | O_ok : v:value -> v':B.val_ -> m1:B.machine -> m2:B.machine -> sstar sealed c (cfg (Ret v) [] s) ->
      tStar e pt m m1 -> squash (B.next e pt m1 == B.MFinal (B.FReturn v') m2) -> vr v v' -> out e pt sealed s c m
  | O_err : x:exn -> l:pos -> msg:B.text -> tv:B.val_ -> m1:B.machine -> m2:B.machine ->
      sstar sealed c (cfg (Throw x) [] s) -> tStar e pt m m1 ->
      squash (B.next e pt m1 == B.MFinal (B.FError (B.VExn l)) m2) ->
      squash (B.tget l m2.B.m_heap == Some (B.OExn msg tv)) -> squash (exn_ok x msg) -> out e pt sealed s c m

(* rocq/JitLowerStep.v, Theorem sim, as a type: the one-step simulation. Proved in Rocq, NOT
   proved in this port; theorems that need it take it as an explicit argument. Buri.Unfinished
   lists it. *)
let sim_statement (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) : Type0 =
  s:store -> c:config -> m:B.machine -> mS s c m -> out e pt sealed s c m

(* ---------- the lemmas the multi-step theorem uses ---------- *)
let menv_at (fp : nat) (st : B.tree B.val_) (g : env) (rho : lenv) (x : name) (s : nat)
  : Lemma (requires menv fp st g rho /\ lookup x g == Some s)
          (ensures exists v v'. lookup x rho == Some v /\ slotv st (fp + s) == Some v' /\ vrp v v') =
()

let rec menv_bind (ps : list name) (args : list value) (f : nat) (s0 : B.tree B.val_) (i : nat)
  (a : argsAt s0 (f + i) args)
  : Lemma (requires length ps = length args) (ensures menv f s0 (bind ps i) (combine ps args)) (decreases ps) =
  match ps with
  | [] -> ()
  | p :: ps' ->
    match a with
    | AA_cons _ v v' vs _ dv rest ->
      menv_bind ps' vs f s0 (i + 1) rest;
      vrp_of_vr dv;
      introduce forall (x : name). (match lookup x (bind ps i) with
        | Some s -> exists v v'. lookup x (combine ps args) == Some v /\ slotv s0 (f + s) == Some v' /\ vrp v v'
        | None -> True)
      with begin
        assert (args == v :: vs);
        if text_eqb x p then ()
        else (assert (lookup x (bind ps i) == lookup x (bind ps' (i + 1)));
              assert (lookup x (combine ps args) == lookup x (combine ps' vs)))
      end

let rec bind_below (ps : list name) (i : nat) : Lemma (envBelow (bind ps i) (i + length ps)) =
  match ps with
  | [] -> ()
  | p :: ps' -> bind_below ps' (i + 1)
