(* Port of rocq/JitLowerThm.v: preservation over many steps, and its statement for a function
   call. Both are proved here FROM the one-step simulation, which is an explicit hypothesis
   (`sim : sim_statement e pt sealed`, Buri.Unfinished), because `sim` is not ported.
   Encoding: Rocq's conclusion `(exists c' m' k, ...) \/ (exists m1, Ends s c /\ TStar m m1)` is
   the informative type `pres_result` for `preservation` (a total function: induction on n and
   on msr, as Rocq's nested induction), and its inhabitation for `call_preservation`. *)
module Buri.JitLowerThm
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
open Buri.JitLowerStep
open Buri.Unfinished
module B = Buri.JitBytecode

noeq type tN (e : B.env) (pt : B.tree (B.prim & nat)) : nat -> B.machine -> B.machine -> Type0 =
  | TN_0 : m:B.machine -> tN e pt 0 m m
  | TN_S : n:nat -> m:B.machine -> m1:B.machine -> m2:B.machine -> squash (tS e pt m m1) -> tN e pt n m1 m2 ->
      tN e pt (n + 1) m m2

(* As in Rocq, the machines inside Ends are its own: Ends does not say they are on m's run. *)
noeq type ends (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (c : config) : Type0 =
  | E_ok : v:value -> v':B.val_ -> m1:B.machine -> m2:B.machine -> sstar sealed c (cfg (Ret v) [] s) ->
      squash (B.next e pt m1 == B.MFinal (B.FReturn v') m2) -> vr v v' -> ends e pt sealed s c
  | E_err : x:exn -> l:pos -> msg:B.text -> tv:B.val_ -> m1:B.machine -> m2:B.machine ->
      sstar sealed c (cfg (Throw x) [] s) -> squash (B.next e pt m1 == B.MFinal (B.FError (B.VExn l)) m2) ->
      squash (B.tget l m2.B.m_heap == Some (B.OExn msg tv)) -> squash (exn_ok x msg) -> ends e pt sealed s c

let rec tStar_tN (#e : B.env) (#pt : B.tree (B.prim & nat)) (#a #b : B.machine) (h : tStar e pt a b)
  : Tot (n : nat & tN e pt n a b) (decreases h) =
  match h with
  | TS_refl _ -> (| 0, TN_0 a |)
  | TS_step _ m1 _ _ rest -> let (| n, t |) = tStar_tN rest in (| n + 1, TN_S n a m1 b () t |)

let rec tN_app (#e : B.env) (#pt : B.tree (B.prim & nat)) (#j #k : nat) (#a #b #c : B.machine)
  (h : tN e pt j a b) (t : tN e pt k b c) : Tot (tN e pt (j + k) a c) (decreases h) =
  match h with
  | TN_0 _ -> t
  | TN_S n _ m1 _ _ rest -> TN_S (n + k) a m1 c () (tN_app rest t)

let ends_prefix (#e : B.env) (#pt : B.tree (B.prim & nat)) (#sealed : list name) (#s : store) (#c #c' : config)
  (ss : sstar sealed c c') (en : ends e pt sealed s c') : ends e pt sealed s c =
  match en with
  | E_ok v v' m1 m2 s2 _ dv -> E_ok v v' m1 m2 (sstar_trans ss s2) () dv
  | E_err x l msg tv m1 m2 s2 _ _ _ -> E_err x l msg tv m1 m2 (sstar_trans ss s2) () () ()

(* After n steps of the bytecode: still related, or the run has ended as the source's does. *)
noeq type pres_result (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (n : nat) (s : store)
  (c : config) (m : B.machine) : Type0 =
  | Still : c':config -> m':B.machine -> k:nat -> sstar sealed c c' -> tN e pt k m m' -> squash (n <= k) ->
      mS s c' m' -> pres_result e pt sealed n s c m
  | Ended : m1:B.machine -> ends e pt sealed s c -> tStar e pt m m1 -> pres_result e pt sealed n s c m

let rec preservation (#e : B.env) (#pt : B.tree (B.prim & nat)) (#sealed : list name)
  (sim : sim_statement e pt sealed) (n : nat) (s : store) (c : config) (m : B.machine) (h : mS s c m)
  : Tot (pres_result e pt sealed n s c m) (decreases %[n; msr c]) =
  if n = 0 then Still c m 0 (SS_refl c) (TN_0 m) () h else
  match sim s c m h with
  | O_step c' m' ss (Inl (TPlus m1 _ ts)) ms ->
    (match preservation sim (n - 1) s c' m' ms with
     | Still c2 m2 k s2 t2 _ m2s ->
       let (| j, tj |) = tStar_tN ts in
       Still c2 m2 ((j + k) + 1) (sstar_trans ss s2) (TN_S (j + k) m m1 m2 () (tN_app tj t2)) () m2s
     | Ended m2 en t2 ->
       Ended m2 (ends_prefix ss en) (TS_step m m1 m2 () (tStar_trans ts t2)))
  | O_step c' m' ss (Inr _) ms ->
    (match preservation sim n s c' m ms with
     | Still c2 m2 k s2 t2 _ m2s -> Still c2 m2 k (sstar_trans ss s2) t2 () m2s
     | Ended m2 en t2 -> Ended m2 (ends_prefix ss en) t2)
  | O_ok v v' m1 m2 ss ts _ dv -> Ended m1 (E_ok v v' m1 m2 ss () dv) ts
  | O_err x l msg tv m1 m2 ss ts _ _ _ -> Ended m1 (E_err x l msg tv m1 m2 ss () () ()) ts

(* A step the bytecode can take is matched: no related state is stuck, and none takes IO. *)
noeq type progress_result (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store)
  (c : config) (m : B.machine) : Type0 =
  | P_step : m':B.machine -> tPlus e pt m m' -> progress_result e pt sealed s c m
  | P_ends : m1:B.machine -> ends e pt sealed s c -> tStar e pt m m1 -> progress_result e pt sealed s c m
  | P_src : c':config -> sstar sealed c c' -> squash (msr c' < msr c) -> mS s c' m -> progress_result e pt sealed s c m

let related_progress (#e : B.env) (#pt : B.tree (B.prim & nat)) (#sealed : list name)
  (sim : sim_statement e pt sealed) (s : store) (c : config) (m : B.machine) (h : mS s c m)
  : progress_result e pt sealed s c m =
  match sim s c m h with
  | O_step c' m' ss (Inl tp) ms -> P_step m' tp
  | O_step c' m' ss (Inr _) ms -> P_src c' ss () ms
  | O_ok v v' m1 m2 ss ts _ dv -> P_ends m1 (E_ok v v' m1 m2 ss () dv) ts
  | O_err x l msg tv m1 m2 ss ts _ _ _ -> P_ends m1 (E_err x l msg tv m1 m2 ss () () ()) ts

(* ---------- a call from the top level ---------- *)
let entered (m : B.machine) (c : B.code) (args : list value) : prop =
  m.B.m_code == c /\ m.B.m_rest == B.code_ins c /\ m.B.m_conts == [] /\
  inhabited (argsAt m.B.m_stack (m.B.m_fp + 2) args)

let call_preservation (#e : B.env) (#pt : B.tree (B.prim & nat)) (#sealed : list name)
  (sim : sim_statement e pt sealed) (s : store) (m : B.machine) (c : B.code) (ps : list name) (b : expr)
  (args : list value) (n : nat)
  : Lemma (requires com s m /\ compFn c ps b /\ length ps = length args /\ entered m c args)
          (ensures inhabited (pres_result e pt sealed n s (cfg (Eval (combine ps args) b) [] s) m)) =
  let g = bind ps 2 in
  let top = 2 + length ps in
  let w : nat -> prop = fun a -> m.B.m_fp + (2 + length ps) <= a in
  eliminate exists (r' : list B.instr). inhabited (comp c g top b DRet (B.code_ins c) r')
  with begin
    eliminate exists (cf : comp c g top b DRet (B.code_ins c) r'). True
    with begin
      eliminate exists (aa : argsAt m.B.m_stack (m.B.m_fp + 2) args). True
      with begin
        menv_bind ps args m.B.m_fp m.B.m_stack 2 aa;
        bind_below ps 2;
        let kc : kC c m.B.m_fp m.B.m_stack [] w DRet r' [] = KC_ret c m.B.m_fp m.B.m_stack [] w r' [] () (RK_top m.B.m_fp m.B.m_stack) in
        let h : mS s (cfg (Eval (combine ps args) b) [] s) m =
          MS_eval g top b DRet r' (combine ps args) [] w m () cf () () () kc in
        let res = preservation sim n s (cfg (Eval (combine ps args) b) [] s) m h in
        assert (inhabited (pres_result e pt sealed n s (cfg (Eval (combine ps args) b) [] s) m))
      end
    end
  end
