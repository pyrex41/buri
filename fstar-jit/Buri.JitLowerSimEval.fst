(* Port of rocq/JitLowerStep.v, last part: an expression starts (step_eval0, step_op, step_test)
   and the one-step simulation `sim`. GENERATED from Buri.JitLowerSimEval.fst.tpl by gen_sim.sh. *)
module Buri.JitLowerSimEval
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
open Buri.JitLowerSim
module B = Buri.JitBytecode

let kc_slot_inv (#c : B.code) (#f : nat) (#s0 : B.tree B.val_) (#ks : list B.cont) (#w : nat -> prop) (#dst : dest)
  (#r : list B.instr) (#k : list frame) (kc : kC c f s0 ks w dst r k) (d : nat)
  : Pure (kD c f s0 ks w (B.OSlot d) r k) (requires dst == DSlot d) (ensures fun _ -> w (f + d)) =
  match kc with KC_slot _ _ _ _ _ _ _ _ _ kd -> kd
let kc_ret_inv (#c : B.code) (#f : nat) (#s0 : B.tree B.val_) (#ks : list B.cont) (#w : nat -> prop) (#dst : dest)
  (#r : list B.instr) (#k : list frame) (kc : kC c f s0 ks w dst r k)
  : Pure (rK f s0 ks k) (requires dst == DRet) (ensures fun _ -> sub w (fun a -> f <= a)) =
  match kc with KC_ret _ _ _ _ _ _ _ _ rk -> rk

#push-options "--z3rlimit 300 --fuel 2 --ifuel 1"
let rec step_eval0 (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (m : B.machine)
  (#ex : expr) (#g : env) (#top : nat) (#dst : dest) (#r2 : list B.instr) (rho : lenv) (#k : list frame) (w : nat -> prop)
  (cc : comp (code m) g top ex dst m.B.m_rest r2) (kc : kC (code m) (fp m) (st m) (cs m) w dst r2 k)
  : Lemma (requires com s m /\ menv (fp m) (st m) g rho /\ envBelow g top /\ above (fp m) top w)
          (ensures iout e pt sealed s (cfg (Eval rho ex) k s) m) (decreases cc) =
  let c0 = cfg (Eval rho ex) k s in
  let c = code m in
  let f = fp m in
  let s0 = st m in
  let ks = cs m in
  let wt = w_top f top in
  prot_below g f top wt;
  kC_notrap kc;
  match cc with
  | C_lit _ _ _ v v' d k0 _ _ _ dv ->
    let kd = kc_slot_inv kc d in
    lit_step sealed rho ex k s v;
    n_const e pt m d k0 r2 v';
    let m1 = wr m r2 d v' in
    inhabits (O_step #e #pt #sealed #s #c0 #m (cfg (Ret v) k s) m1 (s1' c0 (cfg (Ret v) k s) ())
      (Inl (TPlus m1 () (TS_refl m1))) (ms_write #s #m (KC_slot c f s0 ks w d r2 k () kd) dv))
  | C_move _ _ x s1 d _ _ _ ->
    let kd = kc_slot_inv kc d in
    menv_at f s0 g rho x s1;
    eliminate exists v v'. lookup x rho == Some v /\ slotv s0 (f + s1) == Some v' /\ vrp v v'
    with begin
      n_move e pt m d s1 r2 v';
      let m1 = wr m r2 d v' in
      inhabits (O_step #e #pt #sealed #s #c0 #m (cfg (Ret v) k s) m1 (s1' c0 (cfg (Ret v) k s) ())
        (Inl (TPlus m1 () (TS_refl m1))) (ms_write #s #m (KC_slot c f s0 ks w d r2 k () kd) (vr_of_vrp v v')))
    end
  | C_same _ _ x d _ _ ->
    let kd = kc_slot_inv kc d in
    menv_at f s0 g rho x d;
    eliminate exists v v'. lookup x rho == Some v /\ slotv s0 (f + d) == Some v' /\ vrp v v'
    with
      inhabits (O_step #e #pt #sealed #s #c0 #m (cfg (Ret v) k s) m (s1' c0 (cfg (Ret v) k s) ()) (Inr ())
        (MS_ret v v' (B.OSlot d) k w m () () (vr_of_vrp v v') kd))
  | C_prim _ _ f0 p q args ops d _ _ _ _ _ _ co ->
    let kd = kc_slot_inv kc d in
    (match co with
     | Os_cons _ _ a es o os top2 _ r1 _ co1 co2 ->
       compOp_mono co1;
       let k' = KCallArgs f0 [] es rho :: k in
       let c' = cfg (Eval rho a) k' s in
       let kd' = KD_prim c f s0 ks wt o r1 f0 p q [] es rho k g top2 os [] d r2 w
         () () () () () () co2 DR_nil () () () () () () kd in
       inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
         (MS_op g top a o top2 r1 rho k' wt m () co1 () () () kd')))
  | C_let _ _ x a b _ _ r1 _ ca cb ->
    let k' = KLet x b rho :: k in
    let c' = cfg (Eval rho a) k' s in
    let kd' = KD_let c f s0 ks wt top r1 x b rho k g (top + 1) dst r2 w () () () () cb () () kc in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_eval g (top + 1) a (DSlot top) r1 rho k' wt m () ca () () () (KC_slot c f s0 ks wt top r1 k' () kd')))
  | C_alias _ _ x y s1 b _ r _ _ cb ->
    let k' = KLet x b rho :: k in
    let c' = cfg (Eval rho (EVar y)) k' s in
    let kd' = KD_let c f s0 ks wt s1 r x b rho k g top dst r2 w () () () () cb () () kc in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_op g top (EVar y) (B.OSlot s1) top r rho k' wt m () (O_var g top y s1 r () ()) () () () kd'))
  | C_if_slot _ _ t a b d l e0 _ r1 r3 _ ct ca _ cb _ ->
    let kd = kc_slot_inv kc d in
    let k' = KIf a b rho :: k in
    let c' = cfg (Eval rho t) k' s in
    let kc1 = KC_slot c f s0 ks w d (B.IJump e0 :: B.ILabel l :: r3) k () (KD_jump c f s0 ks w (B.OSlot d) e0 (B.ILabel l :: r3) r2 k () kd) in
    let kc2 = KC_slot c f s0 ks w d (B.ILabel e0 :: r2) k () (KD_label c f s0 ks w (B.OSlot d) e0 r2 k kd) in
    let tk = TK_if c f s0 ks wt l r1 a b rho k g top (DSlot d) (B.IJump e0 :: B.ILabel l :: r3) r3 (B.ILabel e0 :: r2) w
      () () () ca () cb () () kc1 kc2 in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top t l r1 rho k' wt m () ct () () () tk))
  | C_if_ret _ _ t a b l _ r1 r3 _ ct ca _ cb ->
    let rk = kc_ret_inv kc in
    let k' = KIf a b rho :: k in
    let c' = cfg (Eval rho t) k' s in
    let tk = TK_if c f s0 ks wt l r1 a b rho k g top DRet (B.ILabel l :: r3) r3 r2 w
      () () () ca () cb () () (KC_ret c f s0 ks w (B.ILabel l :: r3) k () rk) (KC_ret c f s0 ks w r2 k () rk) in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top t l r1 rho k' wt m () ct () () () tk))
  | C_cond_nil _ _ d _ ->
    let m' = B.set_rest m r2 in
    assert (B.next e pt m == B.raise_s m' "cond: no clause applies");
    inhabits (finish_raise #e #pt #sealed s c0 m m' XCondFail k (B.t "cond: no clause applies") B.VCleared
      (s1' c0 (cfg (Throw XCondFail) k s) ()))
  | C_cond_true _ _ x rest _ _ _ cx ->
    let c1 = cfg (Eval rho (EBool true)) (KCond x rest rho :: k) s in
    let c2 = cfg (Ret (VBool true)) (KCond x rest rho :: k) s in
    let c' = cfg (Eval rho x) k s in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1 c0 c1 c' () (s1 c1 c2 c' () (s1' c2 c' ()))) (Inr ())
      (MS_eval g top x dst r2 rho k w m () cx () () () kc))
  | C_cond_slot _ _ t a rest d l e0 _ r1 r3 _ ct ca _ cb _ ->
    let kd = kc_slot_inv kc d in
    let k' = KCond a rest rho :: k in
    let c' = cfg (Eval rho t) k' s in
    let kc1 = KC_slot c f s0 ks w d (B.IJump e0 :: B.ILabel l :: r3) k () (KD_jump c f s0 ks w (B.OSlot d) e0 (B.ILabel l :: r3) r2 k () kd) in
    let kc2 = KC_slot c f s0 ks w d (B.ILabel e0 :: r2) k () (KD_label c f s0 ks w (B.OSlot d) e0 r2 k kd) in
    let tk = TK_cond c f s0 ks wt l r1 a rest rho k g top (DSlot d) (B.IJump e0 :: B.ILabel l :: r3) r3 (B.ILabel e0 :: r2) w
      () () () ca () cb () () kc1 kc2 in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top t l r1 rho k' wt m () ct () () () tk))
  | C_cond_ret _ _ t a rest l _ r1 r3 _ ct ca _ cb ->
    let rk = kc_ret_inv kc in
    let k' = KCond a rest rho :: k in
    let c' = cfg (Eval rho t) k' s in
    let tk = TK_cond c f s0 ks wt l r1 a rest rho k g top DRet (B.ILabel l :: r3) r3 r2 w
      () () () ca () cb () () (KC_ret c f s0 ks w (B.ILabel l :: r3) k () rk) (KC_ret c f s0 ks w r2 k () rk) in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top t l r1 rho k' wt m () ct () () () tk))
  | C_type _ _ e1 _ _ _ ce ->
    let c' = cfg (Eval rho e1) k s in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_eval g top e1 dst r2 rho k w m () ce () () () kc))
  | C_and _ _ x y d l e0 kt kf _ r1 _ cx cy _ _ _ _ ->
    let kd = kc_slot_inv kc d in
    let tl = B.IJump e0 :: B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r2 in
    let tv = TK_value c f s0 ks w l d kt kf tl (B.ILabel e0 :: r2) k w () () () () ()
      (KD_jump c f s0 ks w (B.OSlot d) e0 (B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r2) r2 k () kd)
      (KD_label c f s0 ks w (B.OSlot d) e0 r2 k kd) in
    let k' = KAnd y rho :: k in
    let c' = cfg (Eval rho x) k' s in
    let tk = TK_and c f s0 ks wt false l r1 y rho k g top (B.IConst d kt :: tl) w () () () cy () () tv in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top x l r1 rho k' wt m () cx () () () tk))
  | C_or _ _ x y d l nx th e0 kt kf _ r2' _ cx _ cy _ _ _ _ _ ->
    let kd = kc_slot_inv kc d in
    let tl = B.IJump e0 :: B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r2 in
    let tv = TK_value c f s0 ks w l d kt kf tl (B.ILabel e0 :: r2) k w () () () () ()
      (KD_jump c f s0 ks w (B.OSlot d) e0 (B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r2) r2 k () kd)
      (KD_label c f s0 ks w (B.OSlot d) e0 r2 k kd) in
    let k' = KOr y rho :: k in
    let c' = cfg (Eval rho x) k' s in
    let tk1 = TK_label c f s0 ks w false l th (B.IConst d kt :: tl) k tv in
    let tk2 = TK_jump c f s0 ks w false l th (B.ILabel nx :: r2') (B.IConst d kt :: tl) k () tv in
    let tk = TK_or c f s0 ks wt false l nx (B.IJump th :: B.ILabel nx :: r2') y rho k g top r2'
      (B.ILabel th :: B.IConst d kt :: tl) w () () () () cy () () tk1 tk2 in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top x nx (B.IJump th :: B.ILabel nx :: r2') rho k' wt m () cx () () () tk))
  | C_ret _ _ _ o top2 _ r' co ->
    let rk = kc_ret_inv kc in
    step_op e pt sealed s m rho w co (KD_ret c f s0 ks w o r' k () rk)
  | C_call _ _ f0 args d n i _ _ _ _ cw _ ->
    let kd = kc_slot_inv kc d in
    (match cw with
     | W_nil _ _ _ ->
       named_call e pt sealed s c0 k m f0 [] k i d top n r2 w (AA_nil (fp m + top + 2)) kd
     | W_cons _ _ a es _ r1 _ c1 c2 ->
       let k' = KCallArgs f0 [] es rho :: k in
       let c' = cfg (Eval rho a) k' s in
       let wt2 = w_top f (top + 2) in
       prot_below g f (top + 2) wt2;
       let kd' = KD_call c f s0 ks wt2 r1 f0 [] es rho k g top (top + 2) d n i r2 w
         () () () () () () c2 () (AA_nil (f + top + 2)) () () () () kd in
       inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
         (MS_eval g (top + 2 + 1) a (DSlot (top + 2)) r1 rho k' wt2 m () c1 () () ()
           (KC_slot c f s0 ks wt2 (top + 2) r1 k' () kd'))))
  | C_tail _ _ f0 args n t i _ _ _ _ _ _ cta _ ->
    let rk = kc_ret_inv kc in
    (match args with
     | [] ->
       (match cta with
        | TA_nil _ _ _ _ _ -> tail_fire e pt sealed s c0 k m f0 [] k [] i n r2 2 (PA_nil 2) rk)
     | a :: es ->
       let k' = KCallArgs f0 [] es rho :: k in
       let c' = cfg (Eval rho a) k' s in
       inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
         (ta_start #s m rho a es [] r2 i 2 t f0 [] k g n cta (PA_nil 2) rk)))
  | C_chain _ _ f0 a e1 v v' k0 d _ _ _ _ _ dv ce ->
    let kd = kc_slot_inv kc d in
    let c1 = cfg (Eval rho a) (KCallArgs f0 [] [e1] rho :: k) s in
    let c2 = cfg (Ret v) (KCallArgs f0 [] [e1] rho :: k) s in
    let k' = KCallArgs f0 [v] [] rho :: k in
    let c' = cfg (Eval rho e1) k' s in
    lit_step sealed rho a (KCallArgs f0 [] [e1] rho :: k) s v;
    esize_pos a;
    assert (esize_l [a; e1] == 2 + esize a + esize e1 + esize_l []);
    assert (msr c' == 1 + esize e1 + (esize (ECall f0 []) + ksize k));
    assert (msr c0 == 1 + esize (ECall f0 [a; e1]) + ksize k);
    let rp = B.IPrim d B.PCons [B.OConst k0; B.OSlot d] :: r2 in
    let kd' = KD_prim c f s0 ks w (B.OSlot d) rp f0 PCons B.PCons [v] [] rho k [] (top + d + 1) [] [B.OConst k0] d r2 w
      () () () () () () (Os_nil [] (top + d + 1) rp) (DR_cons v v' (B.OConst k0) [] [] () dv DR_nil) () () () () () () kd in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1 c0 c1 c' () (s1 c1 c2 c' () (s1' c2 c' ()))) (Inr ())
      (MS_eval g top e1 (DSlot d) rp rho k' w m () ce () () () (KC_slot c f s0 ks w d rp k' () kd')))

and step_op (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (m : B.machine)
  (#ex : expr) (#g : env) (#top : nat) (#o : B.operand) (#top2 : nat) (#r2 : list B.instr) (rho : lenv) (#k : list frame)
  (w : nat -> prop) (co : compOp (code m) g top ex o top2 m.B.m_rest r2) (kd : kD (code m) (fp m) (st m) (cs m) w o r2 k)
  : Lemma (requires com s m /\ menv (fp m) (st m) g rho /\ envBelow g top /\ above (fp m) top w)
          (ensures iout e pt sealed s (cfg (Eval rho ex) k s) m) (decreases co) =
  let c0 = cfg (Eval rho ex) k s in
  match co with
  | O_var _ _ x s1 _ _ _ ->
    menv_at (fp m) (st m) g rho x s1;
    eliminate exists v v'. lookup x rho == Some v /\ slotv (st m) (fp m + s1) == Some v' /\ vrp v v'
    with
      inhabits (O_step #e #pt #sealed #s #c0 #m (cfg (Ret v) k s) m (s1' c0 (cfg (Ret v) k s) ()) (Inr ())
        (MS_ret v v' (B.OSlot s1) k w m () () (vr_of_vrp v v') kd))
  | O_lit _ _ _ v v' k0 _ _ _ dv ->
    lit_step sealed rho ex k s v;
    esize_pos ex;
    inhabits (O_step #e #pt #sealed #s #c0 #m (cfg (Ret v) k s) m (s1' c0 (cfg (Ret v) k s) ()) (Inr ())
      (MS_ret v v' (B.OConst k0) k w m () () dv kd))
  | O_val _ _ _ _ _ ce ->
    step_eval0 e pt sealed s m rho w ce (KC_slot (code m) (fp m) (st m) (cs m) w top r2 k () kd)
  | O_type _ _ e1 _ _ _ _ co1 ->
    let c' = cfg (Eval rho e1) k s in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_op g top e1 o top2 r2 rho k w m () co1 () () () kd))

let step_test (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (m : B.machine)
  (#ex : expr) (#g : env) (#top : nat) (#l : nat) (#r2 : list B.instr) (rho : lenv) (#k : list frame) (w : nat -> prop)
  (ct : compT (code m) g top ex l m.B.m_rest r2) (tk : tK (code m) (fp m) (st m) (cs m) w true l r2 k)
  : Lemma (requires com s m /\ menv (fp m) (st m) g rho /\ envBelow g top /\ above (fp m) top w)
          (ensures iout e pt sealed s (cfg (Eval rho ex) k s) m) =
  let c0 = cfg (Eval rho ex) k s in
  let c = code m in
  let f = fp m in
  let s0 = st m in
  let ks = cs m in
  let wt = w_top f top in
  prot_below g f top wt;
  match ct with
  | T_leaf _ _ _ o _ _ _ _ co -> step_op e pt sealed s m rho w co (KD_test c f s0 ks w o l r2 k tk)
  | T_and _ _ x y _ _ r1 _ cx cy ->
    let k' = KAnd y rho :: k in
    let c' = cfg (Eval rho x) k' s in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top x l r1 rho k' wt m () cx () () ()
        (TK_and c f s0 ks wt true l r1 y rho k g top r2 w () () () cy () () tk)))
  | T_or _ _ x y _ nx th _ r2' _ cx _ cy _ ->
    let k' = KOr y rho :: k in
    let c' = cfg (Eval rho x) k' s in
    let tk1 = TK_label c f s0 ks w true l th r2 k tk in
    let tk2 = TK_jump c f s0 ks w true l th (B.ILabel nx :: r2') r2 k () tk in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top x nx (B.IJump th :: B.ILabel nx :: r2') rho k' wt m () cx () () ()
        (TK_or c f s0 ks wt true l nx (B.IJump th :: B.ILabel nx :: r2') y rho k g top r2' (B.ILabel th :: r2) w
          () () () () cy () () tk1 tk2)))
  | T_let _ _ x a b _ _ r1 _ ca cb ->
    let k' = KLet x b rho :: k in
    let c' = cfg (Eval rho a) k' s in
    let kd' = KD_lett c f s0 ks wt top r1 x b rho k g (top + 1) l r2 w () () () () cb () () tk in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_eval g (top + 1) a (DSlot top) r1 rho k' wt m () ca () () () (KC_slot c f s0 ks wt top r1 k' () kd')))
  | T_alias _ _ x y s1 b _ r _ _ cb ->
    let k' = KLet x b rho :: k in
    let c' = cfg (Eval rho (EVar y)) k' s in
    let kd' = KD_lett c f s0 ks wt s1 r x b rho k g top l r2 w () () () () cb () () tk in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_op g top (EVar y) (B.OSlot s1) top r rho k' wt m () (O_var g top y s1 r () ()) () () () kd'))
  | T_type _ _ e1 _ _ _ ct1 ->
    let c' = cfg (Eval rho e1) k s in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top e1 l r2 rho k w m () ct1 () () () tk))
#pop-options

(* One step of the simulation (rocq/JitLowerStep.v, Theorem sim). *)
let sim (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (c : config) (m : B.machine)
  (h : mS s c m) : Lemma (iout e pt sealed s c m) =
  match h with
  | MS_eval _ _ _ _ _ rho _ w _ _ cc _ _ _ kc -> step_eval0 e pt sealed s m rho w cc kc
  | MS_test _ _ _ _ _ rho _ w _ _ ct _ _ _ tk -> step_test e pt sealed s m rho w ct tk
  | MS_op _ _ _ _ _ _ rho _ w _ _ co _ _ _ kd -> step_op e pt sealed s m rho w co kd
  | MS_ret v v' _ _ _ _ _ _ dv kd -> step_ret e pt sealed kd s v v' m dv
