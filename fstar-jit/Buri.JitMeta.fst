(* Port of rocq/JitMeta.v: basic metatheory of the bytecode semantics. *)
module Buri.JitMeta
open Buri.Lib
open Buri.JitFloat
open Buri.JitBytecode

noeq type step (e : env) (pt : tree (prim & nat)) : machine -> option (jreq & jres) -> machine -> Type0 =
  | StepTau : m:machine -> m':machine -> squash (next e pt m == MTau m') -> step e pt m None m'
  | StepIO : m:machine -> q:jreq -> k:(jres -> machine) -> r:jres -> squash (next e pt m == MIO q k) ->
      step e pt m (Some (q, r)) (k r)
let final_in (e : env) (pt : tree (prim & nat)) (m : machine) (o : final) : prop =
  exists m'. next e pt m == MFinal o m'
let stuck_in (e : env) (pt : tree (prim & nat)) (m : machine) (w : stuck) : prop = next e pt m == MStuck w

let step_deterministic_tau (e : env) (pt : tree (prim & nat)) (m m1 m2 : machine) (h1 : step e pt m None m1) (h2 : step e pt m None m2)
  : Lemma (m1 == m2) =
  match h1 with StepTau _ _ _ -> (match h2 with StepTau _ _ _ -> ())

let step_deterministic_io (e : env) (pt : tree (prim & nat)) (m : machine) (q1 q2 : jreq) (r1 r2 : jres) (m1 m2 : machine)
  (h1 : step e pt m (Some (q1, r1)) m1) (h2 : step e pt m (Some (q2, r2)) m2)
  : Lemma (q1 == q2 /\ (r1 == r2 ==> m1 == m2)) =
  match h1 with StepIO _ _ k1 _ _ -> (match h2 with StepIO _ _ k2 _ _ -> ())

let step_tau_excludes_io (e : env) (pt : tree (prim & nat)) (m m1 : machine) (q : jreq) (r : jres) (m2 : machine) (h1 : step e pt m None m1) (h2 : step e pt m (Some (q, r)) m2)
  : Lemma False =
  match h1 with StepTau _ _ _ -> (match h2 with StepIO _ _ _ _ _ -> ())

let move_classification e pt m
  : Lemma ((exists m'. next e pt m == MTau m') \/ (exists q k. next e pt m == MIO q k) \/
           (exists o m'. next e pt m == MFinal o m') \/ (exists w. next e pt m == MStuck w)) =
  match next e pt m with
  | MTau _ | MIO _ _ | MFinal _ _ | MStuck _ -> ()

let final_not_stuck e pt m o w : Lemma (requires final_in e pt m o /\ stuck_in e pt m w) (ensures False) = ()
let step_not_stuck (e : env) (pt : tree (prim & nat)) (m : machine) (l : option (jreq & jres)) (m' : machine) (w : stuck) (h : step e pt m l m') : Lemma (requires stuck_in e pt m w) (ensures False) =
  match h with StepTau _ _ _ -> () | StepIO _ _ _ _ _ -> ()
let final_unique e pt m o1 o2 : Lemma (requires final_in e pt m o1 /\ final_in e pt m o2) (ensures o1 == o2) = ()

(* Rocq: destruct p; destruct args into up to three operands; reflexivity. *)
#push-options "--z3rlimit 60 --ifuel 2 --fuel 4"
let excluded_prims_stuck e pt m d p args
  : Lemma (requires is_excluded p = true) (ensures prim_step e pt m d p args == MStuck (RExcluded p)) = ()
#pop-options

let next_empty_rest e pt m : Lemma (requires m.m_rest == []) (ensures next e pt m == MStuck RFallOff) = ()

let rec tget_tset_same (#a : Type) (k : pos) (x : a) (m : tree a)
  : Lemma (ensures tget k (tset k x m) == Some x) (decreases k) =
  if k = 1 then () else
  match m with
  | Leaf -> tget_tset_same (k / 2) x Leaf
  | Node l _ r -> if k % 2 = 0 then tget_tset_same (k / 2) x l else tget_tset_same (k / 2) x r

let tget_leaf (#a : Type) (k : pos) : Lemma (tget k (Leaf #a) == None) = ()

let rec tget_tset_other (#a : Type) (k j : pos) (x : a) (m : tree a)
  : Lemma (requires k <> j) (ensures tget k (tset j x m) == tget k m) (decreases k) =
  if k = 1 || j = 1 then () else
  match m with
  | Leaf -> if (k % 2 = j % 2) then tget_tset_other (k / 2) (j / 2) x Leaf else ()
  | Node l _ r ->
    if k % 2 = 0 && j % 2 = 0 then tget_tset_other (k / 2) (j / 2) x l
    else if k % 2 = 1 && j % 2 = 1 then tget_tset_other (k / 2) (j / 2) x r
    else ()

let move_writes e pt m d s v r
  : Lemma (requires m.m_rest == IMove d s :: r /\ sread (set_rest m r) s == Some v)
          (ensures exists m'. next e pt m == MTau m' /\ m'.m_rest == r /\
                   tget (skey (m.m_fp + d)) m'.m_stack == Some v) =
  tget_tset_same (skey (m.m_fp + d)) v m.m_stack

let jump_if_false_requires_boolean e pt m o l r v
  : Lemma (requires m.m_rest == IJumpIfFalse o l :: r /\ read_op (set_rest m r) o == Some v /\
                    (forall b. v =!= VBool b))
          (ensures next e pt m == raise_v (set_rest m r) "~S is not a boolean" v) = ()

let return_at_top m v : Lemma (requires m.m_conts == []) (ensures do_return m v == MFinal (FReturn v) m) = ()

let raise_no_handler_final m msg v
  : Lemma (requires m.m_handlers == []) (ensures exists e m'. raise m msg v == MFinal (FError e) m') =
  let (l, m') = alloc m (OExn msg v) in
  assert (raise m msg v == MFinal (FError (VExn l)) m')

let install_sealed_refused pt m d name c
  : Lemma (requires tget name m.m_sealed == Some ())
          (ensures install pt m d (VPair (VSym s_defun) (VPair (VSym name) (VPair c VNil))) ==
                   raise_v m "~S is sealed and cannot be redefined" (VSym name)) = ()
