(* rocq/JitLowerThm.v's theorems, proved OUTRIGHT: from Buri.JitLowerSimEval.sim (the port of
   rocq/JitLowerStep.v's Theorem sim), not from a hypothesis. Also
   JitLowerEquiv.call_preservation_src_of_fundamental with only fundamental_statement as hypothesis,
   as in Rocq. Results are inhabitation of the informative result types (Rocq: Props). *)
module Buri.JitLowerFinal
open Buri.Lib
open Buri.Observation
open Buri.KLSyntax
open Buri.KLValue
open Buri.KLSemantics
open Buri.JitLowerRel
open Buri.JitLowerKont
open Buri.JitLowerStep
open Buri.JitLowerThm
open Buri.JitLowerSim
open Buri.JitLowerSimEval
module B = Buri.JitBytecode
module Q = Buri.JitLowerEquiv

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec preservation (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (n : nat) (s : store)
  (c : config) (m : B.machine) (h : mS s c m)
  : Lemma (ensures inhabited (pres_result e pt sealed n s c m)) (decreases %[n; msr c]) =
  if n = 0 then inhabits (Still #e #pt #sealed #n #s #c #m c m 0 (SS_refl c) (TN_0 m) () h) else begin
    sim e pt sealed s c m h;
    eliminate exists (o : out e pt sealed s c m). True
    with (match o with
      | O_step c' m' ss (Inl (TPlus m1 _ ts)) ms ->
        preservation e pt sealed (n - 1) s c' m' ms;
        eliminate exists (r : pres_result e pt sealed (n - 1) s c' m'). True
        with (match r with
          | Still c2 m2 k s2 t2 _ m2s ->
            let (| j, tj |) = tStar_tN ts in
            inhabits (Still #e #pt #sealed #n #s #c #m c2 m2 ((j + k) + 1) (sstar_trans ss s2)
              (TN_S (j + k) m m1 m2 () (tN_app tj t2)) () m2s)
          | Ended m2 en t2 ->
            inhabits (Ended #e #pt #sealed #n #s #c #m m2 (ends_prefix ss en) (TS_step m m1 m2 () (tStar_trans ts t2))))
      | O_step c' m' ss (Inr _) ms ->
        preservation e pt sealed n s c' m ms;
        eliminate exists (r : pres_result e pt sealed n s c' m). True
        with (match r with
          | Still c2 m2 k s2 t2 _ m2s -> inhabits (Still #e #pt #sealed #n #s #c #m c2 m2 k (sstar_trans ss s2) t2 () m2s)
          | Ended m2 en t2 -> inhabits (Ended #e #pt #sealed #n #s #c #m m2 (ends_prefix ss en) t2))
      | O_ok v v' m1 m2 ss ts _ dv -> inhabits (Ended #e #pt #sealed #n #s #c #m m1 (E_ok v v' m2 ss () dv) ts)
      | O_err x l msg tv m1 m2 ss ts _ _ _ ->
        inhabits (Ended #e #pt #sealed #n #s #c #m m1 (E_err x l msg tv m2 ss () () ()) ts))
  end
#pop-options

let related_progress (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (c : config)
  (m : B.machine) (h : mS s c m) : Lemma (inhabited (progress_result e pt sealed s c m)) =
  sim e pt sealed s c m h;
  eliminate exists (o : out e pt sealed s c m). True
  with (match o with
    | O_step c' m' ss (Inl tp) ms -> inhabits (P_step #e #pt #sealed #s #c #m m' tp)
    | O_step c' m' ss (Inr _) ms -> inhabits (P_src #e #pt #sealed #s #c #m c' ss () ms)
    | O_ok v v' m1 m2 ss ts _ dv -> inhabits (P_ends #e #pt #sealed #s #c #m m1 (E_ok v v' m2 ss () dv) ts)
    | O_err x l msg tv m1 m2 ss ts _ _ _ -> inhabits (P_ends #e #pt #sealed #s #c #m m1 (E_err x l msg tv m2 ss () () ()) ts))

let call_preservation (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (m : B.machine)
  (c : B.code) (ps : list name) (b : expr) (args : list value) (n : nat)
  : Lemma (requires com s m /\ compFn c ps b /\ length ps = length args /\ entered m c args)
          (ensures inhabited (pres_result e pt sealed n s (cfg (Eval (combine ps args) b) [] s) m)) =
  let g = bind ps 2 in
  let top = 2 + length ps in
  let w : nat -> prop = fun a -> m.B.m_fp + (2 + length ps) <= a in
  eliminate exists (r' : list B.instr). inhabited (comp c g top b DRet (B.code_ins c) r')
  with eliminate exists (cf : comp c g top b DRet (B.code_ins c) r'). True
  with eliminate exists (aa : argsAt m.B.m_stack (m.B.m_fp + 2) args). True
  with begin
    menv_bind ps args m.B.m_fp m.B.m_stack 2 aa;
    bind_below ps 2;
    let kc : kC c m.B.m_fp m.B.m_stack [] w DRet r' [] = KC_ret c m.B.m_fp m.B.m_stack [] w r' [] () (RK_top m.B.m_fp m.B.m_stack) in
    let h : mS s (cfg (Eval (combine ps args) b) [] s) m = MS_eval g top b DRet r' (combine ps args) [] w m () cf () () () kc in
    preservation e pt sealed n s (cfg (Eval (combine ps args) b) [] s) m h
  end

let call_preservation_src_of_fundamental (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name)
  (dd : list (name & fundef)) (fF : squash (Q.fundamental_statement sealed dd))
  (s : store) (m : B.machine) (c : B.code) (ps : list name) (b0 b1 eb : expr) (args : list value) (n : nat)
  : Lemma (requires Q.d_wf sealed dd /\ Q.kRef sealed dd ps b0 b1 /\ Q.kRef sealed dd ps b1 eb /\ Q.storeHas dd s /\
                    store_ok s /\ com s m /\ compFn c ps eb /\ length ps = length args /\ entered m c args)
          (ensures inhabited (Q.pres_src_result e pt sealed n s (cfg (Eval (combine ps args) eb) [] s)
                                                         (cfg (Eval (combine ps args) b0) [] s) m)) =
  call_preservation e pt sealed s m c ps eb args n;
  Q.call_preservation_src_of_fundamental #e #pt #sealed dd fF s m c ps b0 b1 eb args n
