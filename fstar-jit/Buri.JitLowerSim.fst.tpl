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
  | %%KD_ret 10=rk%% -> rK_notrap rk
  | %%KD_jump 12=d1%% -> kD_notrap d1
  | %%KD_label 10=d1%% -> kD_notrap d1
  | %%KD_let 24=kc%% -> kC_notrap kc
  | %%KD_lett 24=tk%% -> tK_notrap tk
  | %%KD_test 10=tk%% -> tK_notrap tk
  | %%KD_prim 36=kd%% -> kD_notrap kd
  | %%KD_call 33=kd%% -> kD_notrap kd
  | %%KD_tail 38=rk%% -> rK_notrap rk
and tK_notrap (#c : B.code) (#fp : nat) (#st : B.tree B.val_) (#cs : list B.cont) (#w : nat -> prop)
  (#gd : bool) (#l : nat) (#r : list B.instr) (#k : list frame) (d : tK c fp st cs w gd l r k)
  : Lemma (ensures notrap k) (decreases d) =
  match d with
  | %%TK_if 27=kc1%% -> kC_notrap kc1
  | %%TK_cond 27=kc1%% -> kC_notrap kc1
  | %%TK_and 22=tk%% -> tK_notrap tk
  | %%TK_andr 12=tk%% -> tK_notrap tk
  | %%TK_or 25=tk1%% -> tK_notrap tk1
  | %%TK_orr 12=tk%% -> tK_notrap tk
  | %%TK_jump 13=tk%% -> tK_notrap tk
  | %%TK_label 11=tk%% -> tK_notrap tk
  | %%TK_value 19=kd%% -> kD_notrap kd
and kC_notrap (#c : B.code) (#fp : nat) (#st : B.tree B.val_) (#cs : list B.cont) (#w : nat -> prop)
  (#dst : dest) (#r : list B.instr) (#k : list frame) (d : kC c fp st cs w dst r k)
  : Lemma (ensures notrap k) (decreases d) =
  match d with
  | %%KC_ret 9=rk%% -> rK_notrap rk
  | %%KC_slot 10=kd%% -> kD_notrap kd
and rK_notrap (#fp : nat) (#st : B.tree B.val_) (#cs : list B.cont) (#k : list frame) (d : rK fp st cs k)
  : Lemma (ensures notrap k) (decreases d) =
  match d with
  | %%RK_top%% -> ()
  | %%RK_call 12=kd%% -> kD_notrap kd

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
  | %%KC_slot 10=kd%% ->
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
  | %%O_type 8=d1%% -> compOp_mono d1
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

(* ---------- the moves before a tail call ---------- *)
let rec loc_notin (ms : list (nat & nat)) (i : nat) : Lemma (requires ~(mem_l i (map fst ms))) (ensures loc ms i = i) =
  match ms with [] -> () | (u, v) :: ms' -> loc_notin ms' i
let rec loc_in (ms : list (nat & nat)) (u v : nat)
  : Lemma (requires nodup_l (map fst ms) /\ mem_l (u, v) ms) (ensures loc ms u = v) =
  match ms with
  | (x, y) :: ms' ->
    if x = u then (if y = v then () else (Buri.JitLowerEquiv.mem_map fst u ms'; assert (mem_l u (map fst ms'))))
    else loc_in ms' u v
let rec loc_lim (ms : list (nat & nat)) (j lim : nat)
  : Lemma (requires forall_l (fun (x : nat & nat) -> fst x < lim /\ lim <= snd x) ms) (ensures loc ms j = j \/ lim <= loc ms j) =
  match ms with [] -> () | (u, v) :: ms' -> if u = j then () else loc_lim ms' j lim

let rec paramAt_read (#f : nat) (#s0 : B.tree B.val_) (#ms : list (nat & nat)) (#i : nat) (#vs : list value)
  (p : paramAt f s0 ms i vs) (j : nat)
  : Lemma (requires i <= j /\ j < i + length vs) (ensures Some? (slotv s0 (f + loc ms j))) (decreases p) =
  match p with
  | PA_cons _ _ _ vs' _ _ rest -> if j = i then () else paramAt_read rest j

let moves_cons (u v : nat) (ms : list (nat & nat)) (r : list B.instr)
  : Lemma (app (moves ((u, v) :: ms)) r == B.IMove u v :: app (moves ms) r) = ()

let rec iout_tstar (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (c : config)
  (m m2 : B.machine) (t : tStar e pt m m2)
  : Lemma (requires iout e pt sealed s c m2) (ensures iout e pt sealed s c m) (decreases t) =
  match t with
  | TS_refl _ -> ()
  | TS_step _ m1 _ _ rest -> iout_tstar e pt sealed s c m1 m2 rest; iout_t e pt sealed s c m m1

let moves_inv (m m2 : B.machine) (ms : list (nat & nat)) (r : list B.instr) (lim : nat) : prop =
  m2.B.m_rest == r /\ fp m2 == fp m /\ code m2 == code m /\ cs m2 == cs m /\
  m2.B.m_handlers == m.B.m_handlers /\ m2.B.m_gfun == m.B.m_gfun /\ m2.B.m_heap == m.B.m_heap /\
  (forall (j : nat). j < lim ==> slotv (st m2) (fp m + j) == slotv (st m) (fp m + loc ms j)) /\
  (forall (a : nat). a < fp m ==> slotv (st m2) a == slotv (st m) a)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec run_moves (e : B.env) (pt : B.tree (B.prim & nat)) (ms : list (nat & nat)) (r : list B.instr) (m : B.machine) (lim : nat)
  : Pure (m2 : B.machine & tStar e pt m m2)
    (requires m.B.m_rest == app (moves ms) r /\ forall_l (fun (x : nat & nat) -> fst x < lim /\ lim <= snd x) ms /\
              nodup_l (map fst ms) /\ (forall x. mem_l x ms ==> Some? (slotv (st m) (fp m + snd x))))
    (ensures fun res -> moves_inv m (dfst res) ms r lim) (decreases ms) =
  match ms with
  | [] -> (| m, TS_refl m |)
  | (u, v) :: ms' ->
    moves_cons u v ms' r;
    let Some x = slotv (st m) (fp m + v) in
    let m1 = wr m (app (moves ms') r) u x in
    slot_facts (st m) (fp m + u) x;
    assert (tS e pt m m1);
    Buri.JitLowerEquiv.mem_map fst u ms';
    let (| m2, t2 |) = run_moves e pt ms' r m1 lim in
    introduce forall (j : nat). j < lim ==> slotv (st m2) (fp m + j) == slotv (st m) (fp m + loc ms j)
    with introduce _ ==> _ with begin
      if u = j then loc_notin ms' j else loc_lim ms' j lim
    end;
    (| m2, TS_step m m1 m2 () t2 |)
#pop-options

let rec pA_to_AA (#f : nat) (#s0 : B.tree B.val_) (#ms : list (nat & nat)) (#i : nat) (#vs : list value)
  (s2 : B.tree B.val_) (p : paramAt f s0 ms i vs)
  : Pure (argsAt s2 (f + i) vs)
    (requires forall (j : nat). i <= j /\ j < i + length vs ==> slotv s2 (f + j) == slotv s0 (f + loc ms j))
    (ensures fun _ -> True) (decreases p) =
  match p with
  | PA_nil _ -> AA_nil (f + i)
  | PA_cons _ v v' vs' _ dv rest -> AA_cons (f + i) v v' vs' () dv (pA_to_AA s2 rest)

let rec paramAt_snoc (#f : nat) (#s0 : B.tree B.val_) (#ms : list (nat & nat)) (#i : nat) (#vs : list value)
  (p : paramAt f s0 ms i vs) (v : value) (v' : B.val_) (dv : vr v v')
  : Pure (paramAt f s0 ms i (app vs [v])) (requires slotv s0 (f + loc ms (i + length vs)) == Some v')
    (ensures fun _ -> True) (decreases p) =
  match p with
  | PA_nil _ -> PA_cons i v v' [] () dv (PA_nil (i + 1))
  | PA_cons _ x x' xs _ dx rest -> PA_cons i x x' (app xs [v]) () dx (paramAt_snoc rest v v' dv)

let rec paramAt_ms (#f : nat) (#s0 : B.tree B.val_) (#ms : list (nat & nat)) (#i : nat) (#vs : list value)
  (ms2 : list (nat & nat)) (p : paramAt f s0 ms i vs)
  : Pure (paramAt f s0 ms2 i vs)
    (requires forall (j : nat). i <= j /\ j < i + length vs ==> loc ms2 j == loc ms j) (ensures fun _ -> True) (decreases p) =
  match p with
  | PA_nil _ -> PA_nil i
  | PA_cons _ v v' vs' _ dv rest -> PA_cons i v v' vs' () dv (paramAt_ms ms2 rest)

let rec forall_l_weaken (ms : list (nat & nat)) (lim : nat)
  : Lemma (requires forall_l (fun (x : nat & nat) -> 2 <= fst x /\ fst x < lim /\ lim <= snd x) ms)
          (ensures forall_l (fun (x : nat & nat) -> fst x < lim /\ lim <= snd x) ms /\
                   (forall x. mem_l x ms ==> 2 <= fst x /\ fst x < lim /\ lim <= snd x)) =
  match ms with [] -> () | _ :: r -> forall_l_weaken r lim

#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
let tail_fire (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (c0 : config) (k0 : list frame)
  (m : B.machine) (f : name) (args : list value) (k1 : list frame) (ms : list (nat & nat)) (i : B.instr) (n : nat)
  (r1 : list B.instr) (lim : nat) (pa : paramAt (fp m) (st m) ms 2 args) (rk : rK (fp m) (st m) (cs m) k1)
  : Lemma (requires com s m /\ next_r (rr sealed) pr c0 == call_named_r (rr sealed) pr f args k1 s /\
                    running_state c0 = true /\ c0.kont == k0 /\ c0.mem == s /\ notrap k0 /\ not_prim_name f /\
                    m.B.m_rest == app (moves ms) (i :: r1) /\ tail_instr i 0 (B.sym_of_text f) n /\
                    n = length args /\ lim = n + 2 /\
                    forall_l (fun (x : nat & nat) -> 2 <= fst x /\ fst x < lim /\ lim <= snd x) ms /\ nodup_l (map fst ms))
          (ensures iout e pt sealed s c0 m) =
  forall_l_weaken ms lim;
  introduce forall x. mem_l x ms ==> Some? (slotv (st m) (fp m + snd x))
  with introduce _ ==> _ with begin
    loc_in ms (fst x) (snd x);
    paramAt_read pa (fst x)
  end;
  let (| m2, t |) = run_moves e pt ms (i :: r1) m lim in
  let m' = B.set_rest m2 r1 in
  com_same s m m';
  assert (B.next e pt m2 == B.do_tail e m' 0 n (B.callee_named m' (B.sym_of_text f)));
  rK_notrap rk;
  (match lookup f s.gfuns with
   | Some (FPrim p) -> ()
   | Some (FUser ps b) ->
     eliminate exists (l : pos) (c : B.code) (caps : list B.val_).
       B.tget (B.sym_of_text f) m'.B.m_gfun == Some (B.VClo l) /\ B.tget l m'.B.m_heap == Some (B.OClo c caps) /\
       B.code_arity c = length ps /\ B.code_entry c == None /\ compFn c ps b
     with begin
       let st0 = B.tset (B.skey (fp m2 + 1)) (B.VClo l) (st m2) in
       slot_facts (st m2) (fp m2 + 1) (B.VClo l);
       let rk' = rK_stable rk st0 in
       let aa = pA_to_AA st0 pa in
       enter_out e pt sealed s c0 k0 m2 m' f args k1 ps b l c caps n st0 (fp m2) (cs m2) rk' aa
     end
   | None -> undefined_out e pt sealed s c0 m2 m' f args k1 (fun cv -> B.do_tail e m' 0 n cv));
  iout_tstar e pt sealed s c0 m m2 t
#pop-options

(* ---------- starting an argument of a tail call ---------- *)
let rec kill_lookup_gen (g : env) (s0 : nat) (x : name) (l : env)
  : Lemma (lookup x (filter (fun (p : name & nat) -> not (slot_is (lookup (fst p) g) s0)) l) ==
           (if slot_is (lookup x g) s0 then None else lookup x l)) =
  match l with
  | [] -> ()
  | (y, u) :: l' -> text_eqb_eq x y; kill_lookup_gen g s0 x l'
let kill_lookup (g : env) (s0 : nat) (x : name)
  : Lemma (lookup x (kill s0 g) == (if slot_is (lookup x g) s0 then None else lookup x g)) =
  kill_lookup_gen g s0 x g
let kill_sub (g : env) (s0 : nat) (x : name) (u : nat)
  : Lemma (requires lookup x (kill s0 g) == Some u) (ensures lookup x g == Some u /\ u <> s0) = kill_lookup g s0 x
let menv_kill (f : nat) (s1 : B.tree B.val_) (g : env) (rho : lenv) (s0 : nat)
  : Lemma (requires menv f s1 g rho) (ensures menv f s1 (kill s0 g) rho) =
  introduce forall (x : name). (match lookup x (kill s0 g) with
    | Some s -> exists v v'. lookup x rho == Some v /\ slotv s1 (f + s) == Some v' /\ vrp v v'
    | None -> True)
  with kill_lookup g s0 x
let envBelow_kill (g : env) (t s0 : nat) : Lemma (requires envBelow g t) (ensures envBelow (kill s0 g) t) =
  introduce forall (x : name) (u : nat). lookup x (kill s0 g) == Some u ==> u < t
  with introduce _ ==> _ with kill_sub g s0 x u

let w_tail (f s t : nat) (a : nat) : prop = a = f + s \/ f + t <= a

let rec loc_range2 (ms : list (nat & nat)) (j n t : nat)
  : Lemma (requires forall_l (fun (x : nat & nat) -> n + 2 <= snd x /\ snd x < t) ms)
          (ensures loc ms j = j \/ (n + 2 <= loc ms j /\ loc ms j < t)) =
  match ms with [] -> () | (u, v) :: ms' -> if u = j then () else loc_range2 ms' j n t
let rec ta_forall (ms : list (nat & nat)) (s0 n t : nat)
  : Lemma (requires forall_l (fun (x : nat & nat) -> 2 <= fst x /\ fst x < s0 /\ n + 2 <= snd x /\ snd x < t) ms)
          (ensures forall_l (fun (m : nat & nat) -> 2 <= fst m /\ fst m < s0 + 1 /\ n + 2 <= snd m /\ snd m < t) ms /\
                   forall_l (fun (m : nat & nat) -> 2 <= fst m /\ fst m < s0 + 1 /\ n + 2 <= snd m /\ snd m < t + 1) ms /\
                   forall_l (fun (x : nat & nat) -> n + 2 <= snd x /\ snd x < t) ms /\
                   ~(mem_l s0 (map fst ms))) =
  match ms with [] -> () | _ :: r -> ta_forall r s0 n t

#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
let ta_start (#s : store) (m : B.machine) (rho : lenv) (a : expr) (es : list expr) (ms : list (nat & nat))
  (r1 : list B.instr) (i : B.instr) (s0 t : nat) (f : name) (vals : list value) (k1 : list frame) (g : env) (n : nat)
  (ct : compTA (code m) g s0 t (a :: es) ms m.B.m_rest (i :: r1))
  (pa : paramAt (fp m) (st m) ms 2 (rev vals)) (rk : rK (fp m) (st m) (cs m) k1)
  : Pure (mS s (cfg (Eval rho a) (KCallArgs f vals es rho :: k1) s) m)
    (requires com s m /\ menv (fp m) (st m) g rho /\ envBelow g t /\ not_prim_name f /\ s0 = 2 + length vals /\
              n = length vals + 1 + length es /\ n + 2 <= t /\ tail_instr i 0 (B.sym_of_text f) n /\
              forall_l (fun (x : nat & nat) -> 2 <= fst x /\ fst x < s0 /\ n + 2 <= snd x /\ snd x < t) ms /\
              nodup_l (map fst ms))
    (ensures fun _ -> True) =
  ta_forall ms s0 n t; rev_length vals;
  loc_notin ms s0;
  introduce forall (j : nat). loc ms j = j \/ (n + 2 <= loc ms j /\ loc ms j < t) with loc_range2 ms j n t;
  let k = KCallArgs f vals es rho :: k1 in
  match ct with
  | %%TA_same 4=x 10=cta%% ->
    let w = w_top (fp m) t in
    prot_below g (fp m) t w;
    let kd = KD_tail (code m) (fp m) (st m) (cs m) w (B.OSlot s0) m.B.m_rest f vals es rho k1 g s0 t t ms n i r1
      () () () () () () () () cta () () () () () () pa () rk in
    MS_op g t (EVar x) (B.OSlot s0) t m.B.m_rest rho k w m () (O_var g t x s0 m.B.m_rest () ()) () () () kd
  | %%TA_temp 8=r1' 10=cmp 11=cta%% ->
    let w = w_top (fp m) t in
    prot_below g (fp m) t w;
    let ms2 = (s0, t) :: ms in
    let pa2 = paramAt_ms ms2 pa in
    let kd = KD_tail (code m) (fp m) (st m) (cs m) w (B.OSlot t) r1' f vals es rho k1 g s0 (t + 1) t ms2 n i r1
      () () () () () () () () cta () () () () () () pa2 () rk in
    MS_eval g (t + 1) a (DSlot t) r1' rho k w m () cmp () () () (KC_slot (code m) (fp m) (st m) (cs m) w t r1' k () kd)
  | %%TA_direct 8=r1' 10=cmp 11=cta%% ->
    let w1 = w_tail (fp m) s0 t in
    menv_kill (fp m) (st m) g rho s0;
    envBelow_kill g t s0;
    introduce forall (x : name) (u : nat). lookup x (kill s0 g) == Some u ==> ~(w1 (fp m + u))
    with introduce _ ==> _ with kill_sub g s0 x u;
    let kd = KD_tail (code m) (fp m) (st m) (cs m) w1 (B.OSlot s0) r1' f vals es rho k1 (kill s0 g) s0 t t ms n i r1
      () () () () () () () () cta () () () () () () pa () rk in
    MS_eval g t a (DSlot s0) r1' rho k w1 m () cmp () () () (KC_slot (code m) (fp m) (st m) (cs m) w1 s0 r1' k () kd)
#pop-options

(* ---------- instruction by instruction ---------- *)
let n_const (e : B.env) (pt : B.tree (B.prim & nat)) (m : B.machine) (d k : nat) (r : list B.instr) (v : B.val_)
  : Lemma (requires m.B.m_rest == B.IConst d k :: r /\ konst (code m) k == Some v) (ensures tS e pt m (wr m r d v)) = ()
let n_move (e : B.env) (pt : B.tree (B.prim & nat)) (m : B.machine) (d s0 : nat) (r : list B.instr) (v : B.val_)
  : Lemma (requires m.B.m_rest == B.IMove d s0 :: r /\ slotv (st m) (fp m + s0) == Some v) (ensures tS e pt m (wr m r d v)) = ()
let n_jump (e : B.env) (pt : B.tree (B.prim & nat)) (m : B.machine) (l : nat) (r r1 : list B.instr)
  : Lemma (requires m.B.m_rest == B.IJump l :: r /\ lbl (code m) l == Some r1) (ensures tS e pt m (B.set_rest m r1)) = ()
let n_label (e : B.env) (pt : B.tree (B.prim & nat)) (m : B.machine) (l : nat) (r : list B.instr)
  : Lemma (requires m.B.m_rest == B.ILabel l :: r) (ensures tS e pt m (B.set_rest m r)) = ()
let n_ret (e : B.env) (pt : B.tree (B.prim & nat)) (m : B.machine) (o : B.operand) (r : list B.instr) (v : B.val_)
  : Lemma (requires m.B.m_rest == B.IReturn o :: r /\ read_o (code m) (fp m) (st m) o == Some v)
          (ensures B.next e pt m == B.do_return (B.set_rest m r) v) = ()

(* ---------- tests ---------- *)
let com_rest (s : store) (m : B.machine) (r : list B.instr) : Lemma (requires com s m) (ensures com s (B.set_rest m r)) = ()

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec tk_true (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name)
  (#c : B.code) (#f : nat) (#s0 : B.tree B.val_) (#ks : list B.cont) (#w : nat -> prop) (#gd : bool) (#l : nat)
  (#r : list B.instr) (#k : list frame) (tk : tK c f s0 ks w gd l r k) (s : store) (m : B.machine)
  : Lemma (requires com s m /\ code m == c /\ fp m == f /\ st m == s0 /\ cs m == ks /\ m.B.m_rest == r)
          (ensures iout e pt sealed s (cfg (Ret (VBool true)) k s) m) (decreases tk) =
  let c0 = cfg (Ret (VBool true)) k s in
  match tk with
  | %%TK_if 8=a 10=rho 11=k1 12=g 13=top 14=dst 15=r2 18=w1 22=ca 27=kc1%% ->
    let c' = cfg (Eval rho a) k1 s in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_eval g top a dst r2 rho k1 w1 m () ca () () () kc1))
  | %%TK_cond 8=a 10=rho 11=k1 12=g 13=top 14=dst 15=r2 18=w1 22=ca 27=kc1%% ->
    let c' = cfg (Eval rho a) k1 s in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_eval g top a dst r2 rho k1 w1 m () ca () () () kc1))
  | %%TK_and 6=gd1 7=l1 9=y 10=rho 11=k1 12=g 13=top 14=r2 15=w1 19=cy 22=tk1%% ->
    let c' = cfg (Eval rho y) (KAndR :: k1) s in
    let tk2 = TK_andr c f s0 ks w1 gd1 l1 r2 k1 w1 () tk1 in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top y l1 r2 rho (KAndR :: k1) w1 m () cy () () () tk2))
  | %%TK_andr 9=k1 12=tk1%% ->
    tk_true e pt sealed tk1 s m; iout_s e pt sealed s c0 (cfg (Ret (VBool true)) k1 s) m
  | %%TK_or 12=k1 26=tk2%% ->
    tk_true e pt sealed tk2 s m; iout_s e pt sealed s c0 (cfg (Ret (VBool true)) k1 s) m
  | %%TK_orr 9=k1 12=tk1%% ->
    tk_true e pt sealed tk1 s m; iout_s e pt sealed s c0 (cfg (Ret (VBool true)) k1 s) m
  | %%TK_jump 8=e0 9=r0 10=r1 13=tk1%% ->
    com_rest s m r1; n_jump e pt m e0 r0 r1;
    tk_true e pt sealed tk1 s (B.set_rest m r1); iout_t e pt sealed s c0 m (B.set_rest m r1)
  | %%TK_label 8=x 9=r0 11=tk1%% ->
    com_rest s m r0; n_label e pt m x r0;
    tk_true e pt sealed tk1 s (B.set_rest m r0); iout_t e pt sealed s c0 m (B.set_rest m r0)
  | %%TK_value 7=d 8=kt 10=r2 13=w1 19=kd1%% ->
    n_const e pt m d kt r2 (B.VBool true);
    let m1 = wr m r2 d (B.VBool true) in
    inhabits (O_step #e #pt #sealed #s #c0 #m c0 m1 (SS_refl c0) (Inl (TPlus m1 () (TS_refl m1)))
      (ms_write #s #m (KC_slot c f s0 ks w1 d r2 k () kd1) (VR_bool true)))

let rec tk_false (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name)
  (#c : B.code) (#f : nat) (#s0 : B.tree B.val_) (#ks : list B.cont) (#w : nat -> prop) (#gd : bool) (#l : nat)
  (#r : list B.instr) (#k : list frame) (tk : tK c f s0 ks w gd l r k) (s : store) (m : B.machine) (re : list B.instr)
  : Lemma (requires com s m /\ code m == c /\ fp m == f /\ st m == s0 /\ cs m == ks /\ lbl c l == Some re /\ m.B.m_rest == re)
          (ensures iout e pt sealed s (cfg (Ret (VBool false)) k s) m) (decreases tk) =
  let c0 = cfg (Ret (VBool false)) k s in
  match tk with
  | %%TK_if 9=b 10=rho 11=k1 12=g 13=top 14=dst 16=r3 17=r4 18=w1 24=cb 28=kc2%% ->
    let c' = cfg (Eval rho b) k1 s in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_eval g top b dst r4 rho k1 w1 m () cb () () () kc2))
  | %%TK_cond 9=rest 10=rho 11=k1 12=g 13=top 14=dst 16=r3 17=r4 18=w1 24=cb 28=kc2%% ->
    let c' = cfg (Eval rho (ECond rest)) k1 s in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_eval g top (ECond rest) dst r4 rho k1 w1 m () cb () () () kc2))
  | %%TK_and 11=k1 22=tk1%% ->
    tk_false e pt sealed tk1 s m re; iout_s e pt sealed s c0 (cfg (Ret (VBool false)) k1 s) m
  | %%TK_andr 9=k1 12=tk1%% ->
    tk_false e pt sealed tk1 s m re; iout_s e pt sealed s c0 (cfg (Ret (VBool false)) k1 s) m
  | %%TK_or 6=gd1 7=l1 10=y 11=rho 12=k1 13=g 14=top 15=r2 16=r3 17=w1 22=cy 25=tk1%% ->
    let c' = cfg (Eval rho y) (KOrR :: k1) s in
    let tk2 = TK_orr c f s0 ks w1 gd1 l1 r3 k1 w1 () tk1 in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top y l1 r3 rho (KOrR :: k1) w1 m () cy () () () tk2))
  | %%TK_orr 9=k1 12=tk1%% ->
    tk_false e pt sealed tk1 s m re; iout_s e pt sealed s c0 (cfg (Ret (VBool false)) k1 s) m
  | %%TK_jump 13=tk1%% -> tk_false e pt sealed tk1 s m re
  | %%TK_label 11=tk1%% -> tk_false e pt sealed tk1 s m re
  | %%TK_value 7=d 9=kf 11=r4 13=w1 20=kd2%% ->
    n_const e pt m d kf r4 (B.VBool false);
    let m1 = wr m r4 d (B.VBool false) in
    inhabits (O_step #e #pt #sealed #s #c0 #m c0 m1 (SS_refl c0) (Inl (TPlus m1 () (TS_refl m1)))
      (ms_write #s #m (KC_slot c f s0 ks w1 d r4 k () kd2) (VR_bool false)))

let rec tk_nb (sealed : list name)
  (#c : B.code) (#f : nat) (#s0 : B.tree B.val_) (#ks : list B.cont) (#w : nat -> prop) (#gd : bool) (#l : nat)
  (#r : list B.instr) (#k : list frame) (tk : tK c f s0 ks w gd l r k) (s : store) (v : value)
  : Pure (k' : list frame & sstar sealed (cfg (Ret v) k s) (cfg (Throw XNotBoolean) k' s))
    (requires gd = true /\ not (VBool? v)) (ensures fun res -> notrap (dfst res)) (decreases tk) =
  let c0 = cfg (Ret v) k s in
  match tk with
  | %%TK_if 11=k1 27=kc1%% -> kC_notrap kc1; (| k1, s1' c0 (cfg (Throw XNotBoolean) k1 s) () |)
  | %%TK_cond 11=k1 27=kc1%% -> kC_notrap kc1; (| k1, s1' c0 (cfg (Throw XNotBoolean) k1 s) () |)
  | %%TK_and 11=k1 22=tk1%% -> tK_notrap tk1; (| k1, s1' c0 (cfg (Throw XNotBoolean) k1 s) () |)
  | %%TK_andr 9=k1 12=tk1%% -> tK_notrap tk1; (| k1, s1' c0 (cfg (Throw XNotBoolean) k1 s) () |)
  | %%TK_or 12=k1 25=tk1%% -> tK_notrap tk1; (| k1, s1' c0 (cfg (Throw XNotBoolean) k1 s) () |)
  | %%TK_orr 9=k1 12=tk1%% -> tK_notrap tk1; (| k1, s1' c0 (cfg (Throw XNotBoolean) k1 s) () |)
  | %%TK_jump 13=tk1%% -> tk_nb sealed tk1 s v
  | %%TK_label 11=tk1%% -> tk_nb sealed tk1 s v
#pop-options

(* ---------- primitives ---------- *)
let rec all_some_app (#x #y : Type) (g : x -> option y) (a b : list x) (xa xb : list y)
  : Lemma (requires B.all_some (map g a) == Some xa /\ B.all_some (map g b) == Some xb)
          (ensures B.all_some (map g (app a b)) == Some (app xa xb)) =
  match a with
  | [] -> ()
  | h :: a' -> (match g h with Some yv -> (match B.all_some (map g a') with Some ys -> all_some_app g a' b ys xb))

let read_eq (m : B.machine) (o : B.operand) : Lemma (B.read_op m o == read_o (code m) (fp m) (st m) o) = ()

let rec vrs_app (#a #a' #b #b' : _) (h1 : vrs a a') (h2 : vrs b b') : Tot (vrs (app a b) (app a' b')) (decreases h1) =
  match h1 with
  | VRs_nil -> h2
  | VRs_cons x x' l l' dx rest -> VRs_cons x x' (app l b) (app l' b') dx (vrs_app rest h2)

let rec done_all (#c : B.code) (#f : nat) (#s0 : B.tree B.val_) (#vals : list value) (#dops : list B.operand)
  (d : doneR c f s0 vals dops) (m : B.machine)
  : Pure (xs : list B.val_ & vrs (rev vals) xs)
    (requires code m == c /\ fp m == f /\ st m == s0)
    (ensures fun res -> B.all_some (map (B.read_op m) (rev dops)) == Some (dfst res)) (decreases d) =
  match d with
  | DR_nil -> (| [], VRs_nil |)
  | DR_cons v v' o vs os _ dv rest ->
    let (| xs, h |) = done_all rest m in
    read_eq m o;
    all_some_app (B.read_op m) (rev os) [o] xs [v'];
    (| app xs [v'], vrs_app h (VRs_cons v v' [] [] dv VRs_nil) |)

let rec vrs_length (#a : list value) (#b : list B.val_) (h : vrs a b) : Lemma (ensures length a = length b) (decreases h) =
  match h with VRs_nil -> () | VRs_cons _ _ _ _ _ r -> vrs_length r

let prim_call (sealed : list name) (s : store) (f : name) (p : prim) (args : list value) (k : list frame) (o : pout)
  : Lemma (requires lookup f s.gfuns == Some (FPrim p) /\ length args = prim_arity p /\
                    prim_rule_r (rr sealed) pr p args s == PDone o)
          (ensures call_named_r (rr sealed) pr f args k s == MTau (pout_config pr o [] k s)) =
  firstn_len args (prim_arity p); skipn_len args (prim_arity p)

let rec below_safe (f top : nat) (l : list B.operand)
  : Lemma (requires forall_l (o_below top) l) (ensures forall_l (o_safe f (w_top f top)) l) =
  match l with [] -> () | _ :: r -> below_safe f top r
let rec below_mono (a b : nat) (l : list B.operand)
  : Lemma (requires a <= b /\ forall_l (o_below a) l) (ensures forall_l (o_below b) l) =
  match l with [] -> () | _ :: r -> below_mono a b r
let rec safe_mono (f : nat) (w w1 : nat -> prop) (l : list B.operand)
  : Lemma (requires forall_l (o_safe f w1) l /\ sub w w1) (ensures forall_l (o_safe f w) l) =
  match l with [] -> () | _ :: r -> safe_mono f w w1 r

(* ---------- an argument arrives ---------- *)
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let ret_prim (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (v : value) (v' : B.val_)
  (m : B.machine) (o : B.operand) (f : name) (p : prim) (q : B.prim) (vals : list value) (es : list expr) (rho : lenv)
  (k1 : list frame) (g : env) (top : nat) (ops dops : list B.operand) (d : nat) (r1 : list B.instr) (w w1 : nat -> prop)
  (dv : vr v v') (co : compOps (code m) g top es ops m.B.m_rest (B.IPrim d q (app (rev dops) (o :: ops)) :: r1))
  (dr : doneR (code m) (fp m) (st m) vals dops) (kd : kD (code m) (fp m) (st m) (cs m) w1 (B.OSlot d) r1 k1)
  : Lemma (requires com s m /\ read_o (code m) (fp m) (st m) o == Some v' /\ prim_of_name f == Some p /\
                    pmap p == Some q /\ length vals + 1 + length es = prim_arity p /\
                    menv (fp m) (st m) g rho /\ prot g (fp m) w /\ envBelow g top /\
                    forall_l (o_safe (fp m) w) dops /\ forall_l (o_below top) dops /\ o_below top o /\
                    sub w w1 /\ above (fp m) top w1 /\ w1 (fp m + d))
          (ensures iout e pt sealed s (cfg (Ret v) (KCallArgs f vals es rho :: k1) s) m) =
  let c0 = cfg (Ret v) (KCallArgs f vals es rho :: k1) s in
  kD_notrap kd;
  match co with
  | %%Os_nil%% ->
    let m' = B.set_rest m r1 in
    com_same s m m';
    let (| xs, hx |) = done_all dr m' in
    read_eq m' o;
    all_some_app (B.read_op m') (rev dops) [o] xs [v'];
    let args = rev (v :: vals) in
    let args' = app xs [v'] in
    let hv : vrs args args' = vrs_app hx (VRs_cons v v' [] [] dv VRs_nil) in
    vrs_length hv; rev_length (v :: vals);
    assert (lookup f s.gfuns == Some (FPrim p));
    assert (next_r (rr sealed) pr c0 == call_named_r (rr sealed) pr f args k1 s);
    assert (B.next e pt m == (if B.allocates q && e.B.e_oom m.B.m_allocs then B.raise_s m' "out of memory"
                              else B.prim_step e pt m' d q args'));
    if B.allocates q && e.B.e_oom m.B.m_allocs then begin
      let x = XUser (of_string "out of memory") in
      let st1 : step_r (rr sealed) pr c0 Tau (cfg (Throw x) c0.kont c0.mem) = Step_r_resource c0 RHeap x () () in
      inhabits (finish_raise #e #pt #sealed s c0 m m' x (KCallArgs f vals [] rho :: k1) (B.t "out of memory") B.VCleared
        (SS_step c0 (cfg (Throw x) c0.kont c0.mem) _ st1 (SS_refl _)))
    end else begin
      prim_agree sealed e pt m' d p q args args' s hv;
      eliminate (exists v0 v0'. prim_rule_r (jit_rules sealed) jit_profile p args s == PDone (ORet v0 s) /\
                   B.prim_step e pt m' d q args' == B.ret_to m' d v0' /\ inhabited (vr v0 v0')) \/
                (exists x msg tv. prim_rule_r (jit_rules sealed) jit_profile p args s == PDone (OThrow x) /\
                   B.prim_step e pt m' d q args' == B.raise m' msg tv /\ exn_ok x msg)
      with begin
        eliminate exists v0 v0'. prim_rule_r (jit_rules sealed) jit_profile p args s == PDone (ORet v0 s) /\
                   B.prim_step e pt m' d q args' == B.ret_to m' d v0' /\ inhabited (vr v0 v0')
        with eliminate exists (dv0 : vr v0 v0'). True
        with begin
          prim_call sealed s f p args k1 (ORet v0 s);
          let c' = cfg (Ret v0) k1 s in
          let m1 = wr m r1 d v0' in
          inhabits (O_step #e #pt #sealed #s #c0 #m c' m1 (s1' c0 c' ()) (Inl (TPlus m1 () (TS_refl m1)))
            (ms_write #s #m (KC_slot (code m) (fp m) (st m) (cs m) w1 d r1 k1 () kd) dv0))
        end
      end
      and begin
        eliminate exists x msg tv. prim_rule_r (jit_rules sealed) jit_profile p args s == PDone (OThrow x) /\
                   B.prim_step e pt m' d q args' == B.raise m' msg tv /\ exn_ok x msg
        with begin
          prim_call sealed s f p args k1 (OThrow x);
          inhabits (finish_raise #e #pt #sealed s c0 m m' x k1 msg tv (s1' c0 (cfg (Throw x) k1 s) ()))
        end
      end
    end
  | %%Os_cons 3=a 4=es' 5=o2 6=os 7=top2 9=r1' 11=co1 12=co2%% ->
    compOp_mono co1;
    app_assoc (rev dops) [o] (o2 :: os);
    let wt = w_top (fp m) top in
    prot_below g (fp m) top wt;
    below_safe (fp m) top dops;
    below_mono top top2 dops;
    let k' = KCallArgs f (v :: vals) es' rho :: k1 in
    let c' = cfg (Eval rho a) k' s in
    let kd' = KD_prim (code m) (fp m) (st m) (cs m) wt o2 r1' f p q (v :: vals) es' rho k1 g top2 os (o :: dops) d r1 w1
      () () () () () () co2 (DR_cons v v' o vals dops () dv dr) () () () () () () kd in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_op g top a o2 top2 r1' rho k' wt m () co1 () () () kd'))
#pop-options
