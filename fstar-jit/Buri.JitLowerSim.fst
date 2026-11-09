(* Port of the proof part of rocq/JitLowerStep.v: the one-step simulation `sim` and its lemmas.
   Definitions (MS, Out, msr, ...) are in Buri.JitLowerStep. Section variables E, pt, sealed are
   explicit parameters `e`, `pt`, `sealed`. Rocq's inversion on Comp/KD/TK derivations is a match
   on the F* derivation; Rocq's `reflexivity` steps of next_r and B.next are SMT unfoldings.
   GENERATED from Buri.JitLowerSim.fst.tpl by gen_sim.sh: percent-delimited pattern shorthands are expanded to
   full constructor patterns, with arities read from the declarations. *)
module Buri.JitLowerSim
open Buri.Lib
open Buri.Observation
open Buri.KLSyntax
open Buri.KLValue
open Buri.KLSemantics
open Buri.KLPort
open Buri.JitProfile
open Buri.JitLowerRel
open Buri.JitLowerKont
open Buri.JitLowerStable
open Buri.JitLowerPrim
open Buri.JitLowerStep
module B = Buri.JitBytecode
module M = Buri.JitMeta

let out_t (#e : B.env) (#pt : B.tree (B.prim & nat)) (#sealed : list name) (#s : store) (#c : config)
  (m m1 : B.machine) (t : squash (tS e pt m m1)) (o : out e pt sealed s c m1) : out e pt sealed s c m =
  match o with
  | O_step c' m' ss (Inl (TPlus m2 _ ts)) ms -> O_step c' m' ss (Inl (TPlus m1 () (TS_step m1 m2 m' () ts))) ms
  | O_step c' m' ss (Inr _) ms -> O_step c' m' ss (Inl (TPlus m1 () (TS_refl m1))) ms
  | O_ok v v' m2 m3 ss ts _ dv -> O_ok v v' m2 m3 ss (TS_step m m1 m2 () ts) () dv
  | O_err x l msg tv m2 m3 ss ts _ _ _ -> O_err x l msg tv m2 m3 ss (TS_step m m1 m2 () ts) () () ()

let out_s (#e : B.env) (#pt : B.tree (B.prim & nat)) (#sealed : list name) (#s : store)
  (c c1 : config) (m : B.machine) (h : squash (next_r (rr sealed) pr c == MTau c1 /\ msr c1 < msr c))
  (o : out e pt sealed s c1 m) : out e pt sealed s c m =
  match o with
  | O_step c' m' ss (Inl tp) ms -> O_step c' m' (s1 c c1 c' () ss) (Inl tp) ms
  | O_step c' m' ss (Inr _) ms -> O_step c' m' (s1 c c1 c' () ss) (Inr ()) ms
  | O_ok v v' m2 m3 ss ts _ dv -> O_ok v v' m2 m3 (s1 c c1 _ () ss) ts () dv
  | O_err x l msg tv m2 m3 ss ts _ _ _ -> O_err x l msg tv m2 m3 (s1 c c1 _ () ss) ts () () ()

(* ---------- frames never catch here ---------- *)
let not_trap (f : frame) : prop = match f with KTrap _ _ -> False | _ -> True
let notrap (k : list frame) : prop = forall_l not_trap k

let rec kD_notrap (#c : B.code) (#fp : nat) (#st : B.tree B.val_) (#cs : list B.cont) (#w : nat -> prop)
  (#o : B.operand) (#r : list B.instr) (#k : list frame) (d : kD c fp st cs w o r k)
  : Lemma (ensures notrap k) (decreases d) =
  match d with
  | KD_ret _ _ _ _ _ _ _ _ _ rk -> rK_notrap rk
  | KD_jump _ _ _ _ _ _ _ _ _ _ _ d1 -> kD_notrap d1
  | KD_label _ _ _ _ _ _ _ _ _ d1 -> kD_notrap d1
  | KD_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ kc -> kC_notrap kc
  | KD_lett _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tk -> tK_notrap tk
  | KD_test _ _ _ _ _ _ _ _ _ tk -> tK_notrap tk
  | KD_prim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ kd -> kD_notrap kd
  | KD_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ kd -> kD_notrap kd
  | KD_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rk -> rK_notrap rk
and tK_notrap (#c : B.code) (#fp : nat) (#st : B.tree B.val_) (#cs : list B.cont) (#w : nat -> prop)
  (#gd : bool) (#l : nat) (#r : list B.instr) (#k : list frame) (d : tK c fp st cs w gd l r k)
  : Lemma (ensures notrap k) (decreases d) =
  match d with
  | TK_if _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ kc1 _ -> kC_notrap kc1
  | TK_cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ kc1 _ -> kC_notrap kc1
  | TK_and _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tk -> tK_notrap tk
  | TK_andr _ _ _ _ _ _ _ _ _ _ _ tk -> tK_notrap tk
  | TK_or _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tk1 _ -> tK_notrap tk1
  | TK_orr _ _ _ _ _ _ _ _ _ _ _ tk -> tK_notrap tk
  | TK_jump _ _ _ _ _ _ _ _ _ _ _ _ tk -> tK_notrap tk
  | TK_label _ _ _ _ _ _ _ _ _ _ tk -> tK_notrap tk
  | TK_value _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ kd _ -> kD_notrap kd
and kC_notrap (#c : B.code) (#fp : nat) (#st : B.tree B.val_) (#cs : list B.cont) (#w : nat -> prop)
  (#dst : dest) (#r : list B.instr) (#k : list frame) (d : kC c fp st cs w dst r k)
  : Lemma (ensures notrap k) (decreases d) =
  match d with
  | KC_ret _ _ _ _ _ _ _ _ rk -> rK_notrap rk
  | KC_slot _ _ _ _ _ _ _ _ _ kd -> kD_notrap kd
and rK_notrap (#fp : nat) (#st : B.tree B.val_) (#cs : list B.cont) (#k : list frame) (d : rK fp st cs k)
  : Lemma (ensures notrap k) (decreases d) =
  match d with
  | RK_top _ _ -> ()
  | RK_call _ _ _ _ _ _ _ _ _ _ _ kd _ -> kD_notrap kd

let rec unwind (sealed : list name) (x : exn) (k : list frame) (s : store)
  : Pure (sstar sealed (cfg (Throw x) k s) (cfg (Throw x) [] s)) (requires notrap k) (ensures fun _ -> True) (decreases k) =
  match k with
  | [] -> SS_refl _
  | f :: k' -> s1 (cfg (Throw x) k s) (cfg (Throw x) k' s) _ () (unwind sealed x k' s)

let raise_final (m : B.machine) (msg : B.text) (v : B.val_)
  : Lemma (requires m.B.m_handlers == [])
          (ensures B.raise m msg v == B.MFinal (B.FError (B.VExn m.B.m_next)) (snd (B.alloc m (B.OExn msg v))) /\
                   B.tget m.B.m_next (snd (B.alloc m (B.OExn msg v))).B.m_heap == Some (B.OExn msg v)) =
  M.tget_tset_same m.B.m_next (B.OExn msg v) m.B.m_heap

let finish_raise (#e : B.env) (#pt : B.tree (B.prim & nat)) (#sealed : list name) (s : store) (c : config)
  (m m1 : B.machine) (x : exn) (k : list frame) (msg : B.text) (tv : B.val_)
  (ss : sstar sealed c (cfg (Throw x) k s))
  : Pure (out e pt sealed s c m)
    (requires m1.B.m_handlers == [] /\ B.next e pt m == B.raise m1 msg tv /\ notrap k /\ exn_ok x msg)
    (ensures fun _ -> True) =
  raise_final m1 msg tv;
  O_err x m1.B.m_next msg tv m (snd (B.alloc m1 (B.OExn msg tv))) (sstar_trans ss (unwind sealed x k s)) (TS_refl m) () () ()

(* The simulation's results are stated as `iout` (an Out derivation exists), as Rocq's Out is a
   Prop: FunRel holds CompFn as a proposition, and building MS for a called function needs its
   derivation, which only a proof (ghost) context can take out of a proposition. *)
let iout (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (c : config) (m : B.machine) : prop =
  inhabited (out e pt sealed s c m)
let inhabits (#t : Type0) (x : t) : Lemma (inhabited t) = ()

let iout_t (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (c : config) (m m1 : B.machine)
  : Lemma (requires tS e pt m m1 /\ iout e pt sealed s c m1) (ensures iout e pt sealed s c m) =
  eliminate exists (o : out e pt sealed s c m1). True with inhabits (out_t m m1 () o)
let iout_s (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (c c1 : config) (m : B.machine)
  : Lemma (requires next_r (rr sealed) pr c == MTau c1 /\ msr c1 < msr c /\ iout e pt sealed s c1 m)
          (ensures iout e pt sealed s c m) =
  eliminate exists (o : out e pt sealed s c1 m). True with inhabits (out_s c c1 m () o)

(* ---------- bytecode steps ---------- *)
let wr (m : B.machine) (r : list B.instr) (d : nat) (v : B.val_) : B.machine =
  B.set_stack (B.set_rest m r) (B.swrite (B.set_rest m r) d v)

let com_same (s : store) (m m' : B.machine)
  : Lemma (requires com s m /\ m'.B.m_handlers == m.B.m_handlers /\ m'.B.m_gfun == m.B.m_gfun /\ m'.B.m_heap == m.B.m_heap)
          (ensures com s m') = ()

let slot_facts (st0 : B.tree B.val_) (b : nat) (v : B.val_)
  : Lemma (slotv (B.tset (B.skey b) v st0) b == Some v /\
           (forall (a : nat). a <> b ==> slotv (B.tset (B.skey b) v st0) a == slotv st0 a)) =
  slotv_same st0 b v;
  introduce forall (a : nat). a <> b ==> slotv (B.tset (B.skey b) v st0) a == slotv st0 a
  with introduce _ ==> _ with slotv_other st0 a b v

let ms_write (#s : store) (#m : B.machine) (#r2 : list B.instr) (#d : nat) (#v : value) (#v' : B.val_)
  (#w : nat -> prop) (#k : list frame)
  (kc : kC (code m) (fp m) (st m) (cs m) w (DSlot d) r2 k) (dv : vr v v')
  : Pure (mS s (cfg (Ret v) k s) (wr m r2 d v')) (requires com s m) (ensures fun _ -> True) =
  match kc with
  | KC_slot _ _ _ _ _ _ _ _ _ kd ->
    let m' = wr m r2 d v' in
    slot_facts (st m) (fp m + d) v';
    com_same s m m';
    MS_ret v v' (B.OSlot d) k w m' () () dv (kD_stable kd (st m'))

let lit_step (sl : list name) (rho : lenv) (e : expr) (k : list frame) (s0 : store) (v : value)
  : Lemma (requires lit_val e == Some v) (ensures next_r (rr sl) pr (cfg (Eval rho e) k s0) == MTau (cfg (Ret v) k s0)) =
  match e with ENum _ | EStr _ | ESym _ | EBool _ | ENil -> ()

let esize_pos (e : expr) : Lemma (1 <= esize e) = ()

let menv_cons (f : nat) (s0 : B.tree B.val_) (g : env) (rho : lenv) (x : name) (d : nat) (v : value) (v' : B.val_)
  : Lemma (requires menv f s0 g rho /\ slotv s0 (f + d) == Some v' /\ vrp v v')
          (ensures menv f s0 ((x, d) :: g) ((x, v) :: rho)) =
  introduce forall (y : name). (match lookup y ((x, d) :: g) with
    | Some s -> exists v v'. lookup y ((x, v) :: rho) == Some v /\ slotv s0 (f + s) == Some v' /\ vrp v v'
    | None -> True)
  with (if text_eqb y x then () else ())
let envBelow_cons (g : env) (top : nat) (x : name) (d : nat)
  : Lemma (requires envBelow g top /\ d < top) (ensures envBelow ((x, d) :: g) top) =
  introduce forall (y : name) (s : nat). lookup y ((x, d) :: g) == Some s ==> s < top
  with introduce _ ==> _ with (if text_eqb y x then () else ())
let envBelow_mono (g : env) (a b : nat) : Lemma (requires envBelow g a /\ a <= b) (ensures envBelow g b) = ()
let prot_below (g : env) (f top : nat) (w : nat -> prop)
  : Lemma (requires envBelow g top /\ (forall (a : nat). w a ==> f + top <= a)) (ensures prot g f w) = ()

let w_top (f t : nat) (a : nat) : prop = f + t <= a

let rec compOp_mono (#c : B.code) (#g : env) (#top : nat) (#e : expr) (#o : B.operand) (#top2 : nat)
  (#r #r' : list B.instr) (d : compOp c g top e o top2 r r')
  : Lemma (ensures top <= top2 /\ o_below top2 o) (decreases d) =
  match d with
  | O_type _ _ _ _ _ _ _ d1 -> compOp_mono d1
  | _ -> ()

let rec firstn_len (#a : Type) (l : list a) (n : nat) : Lemma (requires length l = n) (ensures firstn n l == l) =
  match l with [] -> () | _ :: r -> firstn_len r (n - 1)
let rec skipn_len (#a : Type) (l : list a) (n : nat) : Lemma (requires length l = n) (ensures skipn n l == []) =
  match l with [] -> () | _ :: r -> skipn_len r (n - 1)

(* ---------- a call: the bytecode enters a function the source calls ---------- *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let enter_out (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (c0 : config) (k0 : list frame)
  (m0 m' : B.machine) (f : name) (args : list value) (k1 : list frame) (ps : list name) (b : expr) (l : pos)
  (c : B.code) (caps : list B.val_) (n : nat) (st0 : B.tree B.val_) (fp0 : nat) (ks : list B.cont)
  (rk : rK fp0 st0 ks k1) (aa : argsAt st0 (fp0 + 2) args)
  : Lemma (requires com s m' /\ next_r (rr sealed) pr c0 == call_named_r (rr sealed) pr f args k1 s /\
                    running_state c0 = true /\ c0.kont == k0 /\ c0.mem == s /\ notrap k0 /\ notrap k1 /\
                    lookup f s.gfuns == Some (FUser ps b) /\ B.tget l m'.B.m_heap == Some (B.OClo c caps) /\
                    B.code_arity c = length ps /\ B.code_entry c == None /\ compFn c ps b /\
                    n = length args /\ B.next e pt m0 == B.enter e m' (B.VClo l) n st0 fp0 ks)
          (ensures iout e pt sealed s c0 m0) =
  let m2 = B.set_ctl m' st0 fp0 c (B.code_ins c) ks in
  if n = B.code_arity c then begin
    if e.B.e_stack (fp0 + B.code_frame c) then begin
      let x = XUser (of_string "stack overflow") in
      let st1 : step_r (rr sealed) pr c0 Tau (cfg (Throw x) c0.kont c0.mem) = Step_r_resource c0 RStack x () () in
      inhabits (finish_raise #e #pt #sealed s c0 m0 m2 x k0 (B.t "stack overflow") B.VCleared
        (SS_step c0 (cfg (Throw x) k0 s) (cfg (Throw x) k0 s) st1 (SS_refl _)))
    end else begin
      firstn_len args (length ps); skipn_len args (length ps);
      let m1 = B.set_rest m2 (B.code_ins c) in
      let w = w_top fp0 (2 + length ps) in
      let c' = cfg (Eval (combine ps args) b) k1 s in
      assert (next_r (rr sealed) pr c0 == MTau c');
      menv_bind ps args fp0 st0 2 aa;
      bind_below ps 2;
      com_same s m' m1;
      eliminate exists (r' : list B.instr). inhabited (comp c (bind ps 2) (2 + length ps) b DRet (B.code_ins c) r')
      with eliminate exists (cf : comp c (bind ps 2) (2 + length ps) b DRet (B.code_ins c) r'). True
      with begin
        let kc : kC c fp0 st0 ks w DRet r' k1 = KC_ret c fp0 st0 ks w r' k1 () rk in
        let ms : mS s c' m1 = MS_eval (bind ps 2) (2 + length ps) b DRet r' (combine ps args) k1 w m1 () cf () () () kc in
        inhabits (O_step #e #pt #sealed #s #c0 #m0 c' m1 (s1' c0 c' ()) (Inl (TPlus m1 () (TS_refl m1))) ms)
      end
    end
  end else begin
    let c' = cfg (Throw XArity) k1 s in
    assert (next_r (rr sealed) pr c0 == MTau c');
    let msg : B.text = (match B.code_name c with
      | B.VSym sy -> app (B.text_of_sym sy) (app (B.t ": expected ") (app (Buri.JitFloat.z_digits (B.code_arity c))
                       (app (B.t (if B.code_arity c = 1 then " argument, got " else " arguments, got "))
                       (Buri.JitFloat.z_digits n))))
      | _ -> B.t "wrong number of arguments") in
    inhabits (finish_raise #e #pt #sealed s c0 m0 m2 XArity k1 msg B.VCleared (s1' c0 c' ()))
  end
#pop-options

let undefined_out (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (c0 : config)
  (m0 m' : B.machine) (f : name) (args : list value) (k1 : list frame) (g0 : either B.val_ B.move -> B.move)
  : Lemma (requires com s m' /\ next_r (rr sealed) pr c0 == call_named_r (rr sealed) pr f args k1 s /\
                    lookup f s.gfuns == None /\ notrap k1 /\
                    B.next e pt m0 == g0 (B.callee_named m' (B.sym_of_text f)) /\ (forall mv. g0 (Inr mv) == mv))
          (ensures iout e pt sealed s c0 m0) =
  let c' = cfg (Throw (XUndefinedFun f)) k1 s in
  assert (next_r (rr sealed) pr c0 == MTau c');
  assert (B.callee_named m' (B.sym_of_text f) == Inr (B.raise_v m' "undefined function ~S" (B.VSym (B.sym_of_text f))));
  inhabits (finish_raise #e #pt #sealed s c0 m0 m' (XUndefinedFun f) k1 (B.t "undefined function ~S")
    (B.VSym (B.sym_of_text f)) (s1' c0 c' ()))

let rec argsAt_snoc (#s0 : B.tree B.val_) (#a : nat) (#vs : list value) (aa : argsAt s0 a vs) (v : value) (v' : B.val_)
  (dv : vr v v')
  : Pure (argsAt s0 a (app vs [v])) (requires slotv s0 (a + length vs) == Some v') (ensures fun _ -> True) (decreases aa) =
  match aa with
  | AA_nil _ -> AA_cons a v v' [] () dv (AA_nil (a + 1))
  | AA_cons _ x x' xs _ dx rest -> AA_cons a x x' (app xs [v]) () dx (argsAt_snoc rest v v' dv)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let named_call (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (c0 : config) (k0 : list frame)
  (m : B.machine) (f : name) (args : list value) (k1 : list frame) (i : B.instr) (d a n : nat) (r1 : list B.instr)
  (w1 : nat -> prop) (aa : argsAt (st m) (fp m + a + 2) args) (kd : kD (code m) (fp m) (st m) (cs m) w1 (B.OSlot d) r1 k1)
  : Lemma (requires com s m /\ next_r (rr sealed) pr c0 == call_named_r (rr sealed) pr f args k1 s /\
                    running_state c0 = true /\ c0.kont == k0 /\ c0.mem == s /\ notrap k0 /\ not_prim_name f /\
                    m.B.m_rest == i :: r1 /\ call_instr i d a (B.sym_of_text f) n /\ n = length args /\
                    above (fp m) a w1 /\ w1 (fp m + d))
          (ensures iout e pt sealed s c0 m) =
  let m' = B.set_rest m r1 in
  com_same s m m';
  assert (B.next e pt m == B.do_call e m' d a n r1 (B.callee_named m' (B.sym_of_text f)));
  kD_notrap kd;
  match lookup f s.gfuns with
  | Some (FPrim p) -> ()
  | Some (FUser ps b) ->
    eliminate exists (l : pos) (c : B.code) (caps : list B.val_).
      B.tget (B.sym_of_text f) m.B.m_gfun == Some (B.VClo l) /\ B.tget l m.B.m_heap == Some (B.OClo c caps) /\
      B.code_arity c = length ps /\ B.code_entry c == None /\ compFn c ps b
    with begin
      let st0 = B.tset (B.skey (fp m + a + 1)) (B.VClo l) (st m) in
      let fp0 = fp m + a in
      slot_facts (st m) (fp m + a + 1) (B.VClo l);
      let kd' = kD_stable kd st0 in
      let rk : rK fp0 st0 (B.mkCont (code m) r1 d a :: cs m) k1 = RK_call fp0 st0 (code m) r1 d a (cs m) k1 w1 () () kd' () in
      let aa' = argsAt_stable (st m) st0 (fp m + a + 2) args aa in
      enter_out e pt sealed s c0 k0 m m' f args k1 ps b l c caps n st0 fp0 (B.mkCont (code m) r1 d a :: cs m) rk aa'
    end
  | None -> undefined_out e pt sealed s c0 m m' f args k1 (fun cv -> B.do_call e m' d a n r1 cv)
#pop-options
