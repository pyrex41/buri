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
  match kc with %%KC_slot 10=kd%% -> kd
let kc_ret_inv (#c : B.code) (#f : nat) (#s0 : B.tree B.val_) (#ks : list B.cont) (#w : nat -> prop) (#dst : dest)
  (#r : list B.instr) (#k : list frame) (kc : kC c f s0 ks w dst r k)
  : Pure (rK f s0 ks k) (requires dst == DRet) (ensures fun _ -> sub w (fun a -> f <= a)) =
  match kc with %%KC_ret 9=rk%% -> rk

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
  | %%C_lit 4=v 5=v' 6=d 7=k0 11=dv%% ->
    let kd = kc_slot_inv kc d in
    lit_step sealed rho ex k s v;
    n_const e pt m d k0 r2 v';
    let m1 = wr m r2 d v' in
    inhabits (O_step #e #pt #sealed #s #c0 #m (cfg (Ret v) k s) m1 (s1' c0 (cfg (Ret v) k s) ())
      (Inl (TPlus m1 () (TS_refl m1))) (ms_write #s #m (KC_slot c f s0 ks w d r2 k () kd) dv))
  | %%C_move 3=x 4=s1 5=d%% ->
    let kd = kc_slot_inv kc d in
    menv_at f s0 g rho x s1;
    eliminate exists v v'. lookup x rho == Some v /\ slotv s0 (f + s1) == Some v' /\ vrp v v'
    with begin
      n_move e pt m d s1 r2 v';
      let m1 = wr m r2 d v' in
      inhabits (O_step #e #pt #sealed #s #c0 #m (cfg (Ret v) k s) m1 (s1' c0 (cfg (Ret v) k s) ())
        (Inl (TPlus m1 () (TS_refl m1))) (ms_write #s #m (KC_slot c f s0 ks w d r2 k () kd) (vr_of_vrp v v')))
    end
  | %%C_same 3=x 4=d%% ->
    let kd = kc_slot_inv kc d in
    menv_at f s0 g rho x d;
    eliminate exists v v'. lookup x rho == Some v /\ slotv s0 (f + d) == Some v' /\ vrp v v'
    with
      inhabits (O_step #e #pt #sealed #s #c0 #m (cfg (Ret v) k s) m (s1' c0 (cfg (Ret v) k s) ()) (Inr ())
        (MS_ret v v' (B.OSlot d) k w m () () (vr_of_vrp v v') kd))
  | %%C_prim 3=f0 4=p 5=q 6=args 7=ops 8=d 15=co%% ->
    let kd = kc_slot_inv kc d in
    (match co with
     | %%Os_cons 3=a 4=es 5=o 6=os 7=top2 9=r1 11=co1 12=co2%% ->
       compOp_mono co1;
       let k' = KCallArgs f0 [] es rho :: k in
       let c' = cfg (Eval rho a) k' s in
       let kd' = KD_prim c f s0 ks wt o r1 f0 p q [] es rho k g top2 os [] d r2 w
         () () () () () () co2 DR_nil () () () () () () kd in
       inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
         (MS_op g top a o top2 r1 rho k' wt m () co1 () () () kd')))
  | %%C_let 3=x 4=a 5=b 8=r1 10=ca 11=cb%% ->
    let k' = KLet x b rho :: k in
    let c' = cfg (Eval rho a) k' s in
    let kd' = KD_let c f s0 ks wt top r1 x b rho k g (top + 1) dst r2 w () () () () cb () () kc in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_eval g (top + 1) a (DSlot top) r1 rho k' wt m () ca () () () (KC_slot c f s0 ks wt top r1 k' () kd')))
  | %%C_alias 3=x 4=y 5=s1 6=b 8=r 11=cb%% ->
    let k' = KLet x b rho :: k in
    let c' = cfg (Eval rho (EVar y)) k' s in
    let kd' = KD_let c f s0 ks wt s1 r x b rho k g top dst r2 w () () () () cb () () kc in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_op g top (EVar y) (B.OSlot s1) top r rho k' wt m () (O_var g top y s1 r () ()) () () () kd'))
  | %%C_if_slot 3=t 4=a 5=b 6=d 7=l 8=e0 10=r1 11=r3 13=ct 14=ca 16=cb%% ->
    let kd = kc_slot_inv kc d in
    let k' = KIf a b rho :: k in
    let c' = cfg (Eval rho t) k' s in
    let kc1 = KC_slot c f s0 ks w d (B.IJump e0 :: B.ILabel l :: r3) k () (KD_jump c f s0 ks w (B.OSlot d) e0 (B.ILabel l :: r3) r2 k () kd) in
    let kc2 = KC_slot c f s0 ks w d (B.ILabel e0 :: r2) k () (KD_label c f s0 ks w (B.OSlot d) e0 r2 k kd) in
    let tk = TK_if c f s0 ks wt l r1 a b rho k g top (DSlot d) (B.IJump e0 :: B.ILabel l :: r3) r3 (B.ILabel e0 :: r2) w
      () () () ca () cb () () kc1 kc2 in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top t l r1 rho k' wt m () ct () () () tk))
  | %%C_if_ret 3=t 4=a 5=b 6=l 8=r1 9=r3 11=ct 12=ca 14=cb%% ->
    let rk = kc_ret_inv kc in
    let k' = KIf a b rho :: k in
    let c' = cfg (Eval rho t) k' s in
    let tk = TK_if c f s0 ks wt l r1 a b rho k g top DRet (B.ILabel l :: r3) r3 r2 w
      () () () ca () cb () () (KC_ret c f s0 ks w (B.ILabel l :: r3) k () rk) (KC_ret c f s0 ks w r2 k () rk) in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top t l r1 rho k' wt m () ct () () () tk))
  | %%C_cond_nil 3=d%% ->
    let m' = B.set_rest m r2 in
    assert (B.next e pt m == B.raise_s m' "cond: no clause applies");
    inhabits (finish_raise #e #pt #sealed s c0 m m' XCondFail k (B.t "cond: no clause applies") B.VCleared
      (s1' c0 (cfg (Throw XCondFail) k s) ()))
  | %%C_cond_true 3=x 4=rest 8=cx%% ->
    let c1 = cfg (Eval rho (EBool true)) (KCond x rest rho :: k) s in
    let c2 = cfg (Ret (VBool true)) (KCond x rest rho :: k) s in
    let c' = cfg (Eval rho x) k s in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1 c0 c1 c' () (s1 c1 c2 c' () (s1' c2 c' ()))) (Inr ())
      (MS_eval g top x dst r2 rho k w m () cx () () () kc))
  | %%C_cond_slot 3=t 4=a 5=rest 6=d 7=l 8=e0 10=r1 11=r3 13=ct 14=ca 16=cb%% ->
    let kd = kc_slot_inv kc d in
    let k' = KCond a rest rho :: k in
    let c' = cfg (Eval rho t) k' s in
    let kc1 = KC_slot c f s0 ks w d (B.IJump e0 :: B.ILabel l :: r3) k () (KD_jump c f s0 ks w (B.OSlot d) e0 (B.ILabel l :: r3) r2 k () kd) in
    let kc2 = KC_slot c f s0 ks w d (B.ILabel e0 :: r2) k () (KD_label c f s0 ks w (B.OSlot d) e0 r2 k kd) in
    let tk = TK_cond c f s0 ks wt l r1 a rest rho k g top (DSlot d) (B.IJump e0 :: B.ILabel l :: r3) r3 (B.ILabel e0 :: r2) w
      () () () ca () cb () () kc1 kc2 in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top t l r1 rho k' wt m () ct () () () tk))
  | %%C_cond_ret 3=t 4=a 5=rest 6=l 8=r1 9=r3 11=ct 12=ca 14=cb%% ->
    let rk = kc_ret_inv kc in
    let k' = KCond a rest rho :: k in
    let c' = cfg (Eval rho t) k' s in
    let tk = TK_cond c f s0 ks wt l r1 a rest rho k g top DRet (B.ILabel l :: r3) r3 r2 w
      () () () ca () cb () () (KC_ret c f s0 ks w (B.ILabel l :: r3) k () rk) (KC_ret c f s0 ks w r2 k () rk) in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top t l r1 rho k' wt m () ct () () () tk))
  | %%C_type 3=e1 7=ce%% ->
    let c' = cfg (Eval rho e1) k s in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_eval g top e1 dst r2 rho k w m () ce () () () kc))
  | %%C_and 3=x 4=y 5=d 6=l 7=e0 8=kt 9=kf 11=r1 13=cx 14=cy%% ->
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
  | %%C_or 3=x 4=y 5=d 6=l 7=nx 8=th 9=e0 10=kt 11=kf 13=r2' 15=cx 17=cy%% ->
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
  | %%C_ret 4=o 5=top2 7=r' 8=co%% ->
    let rk = kc_ret_inv kc in
    step_op e pt sealed s m rho w co (KD_ret c f s0 ks w o r' k () rk)
  | %%C_call 3=f0 4=args 5=d 6=n 7=i 12=cw%% ->
    let kd = kc_slot_inv kc d in
    (match cw with
     | %%W_nil%% ->
       named_call e pt sealed s c0 k m f0 [] k i d top n r2 w (AA_nil (fp m + top + 2)) kd
     | %%W_cons 3=a 4=es 6=r1 8=c1 9=c2%% ->
       let k' = KCallArgs f0 [] es rho :: k in
       let c' = cfg (Eval rho a) k' s in
       let wt2 = w_top f (top + 2) in
       prot_below g f (top + 2) wt2;
       let kd' = KD_call c f s0 ks wt2 r1 f0 [] es rho k g top (top + 2) d n i r2 w
         () () () () () () c2 () (AA_nil (f + top + 2)) () () () () kd in
       inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
         (MS_eval g (top + 2 + 1) a (DSlot (top + 2)) r1 rho k' wt2 m () c1 () () ()
           (KC_slot c f s0 ks wt2 (top + 2) r1 k' () kd'))))
  | %%C_tail 3=f0 4=args 5=n 6=t 7=i 14=cta%% ->
    let rk = kc_ret_inv kc in
    (match args with
     | [] ->
       (match cta with
        | %%TA_nil%% -> tail_fire e pt sealed s c0 k m f0 [] k [] i n r2 2 (PA_nil 2) rk)
     | a :: es ->
       let k' = KCallArgs f0 [] es rho :: k in
       let c' = cfg (Eval rho a) k' s in
       inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
         (ta_start #s m rho a es [] r2 i 2 t f0 [] k g n cta (PA_nil 2) rk)))
  | %%C_chain 3=f0 4=a 5=e1 6=v 7=v' 8=k0 9=d 15=dv 16=ce%% ->
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
  | %%O_var 3=x 4=s1%% ->
    menv_at (fp m) (st m) g rho x s1;
    eliminate exists v v'. lookup x rho == Some v /\ slotv (st m) (fp m + s1) == Some v' /\ vrp v v'
    with
      inhabits (O_step #e #pt #sealed #s #c0 #m (cfg (Ret v) k s) m (s1' c0 (cfg (Ret v) k s) ()) (Inr ())
        (MS_ret v v' (B.OSlot s1) k w m () () (vr_of_vrp v v') kd))
  | %%O_lit 4=v 5=v' 6=k0 10=dv%% ->
    lit_step sealed rho ex k s v;
    esize_pos ex;
    inhabits (O_step #e #pt #sealed #s #c0 #m (cfg (Ret v) k s) m (s1' c0 (cfg (Ret v) k s) ()) (Inr ())
      (MS_ret v v' (B.OConst k0) k w m () () dv kd))
  | %%O_val 6=ce%% ->
    step_eval0 e pt sealed s m rho w ce (KC_slot (code m) (fp m) (st m) (cs m) w top r2 k () kd)
  | %%O_type 3=e1 8=co1%% ->
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
  | %%T_leaf 4=o 9=co%% -> step_op e pt sealed s m rho w co (KD_test c f s0 ks w o l r2 k tk)
  | %%T_and 3=x 4=y 7=r1 9=cx 10=cy%% ->
    let k' = KAnd y rho :: k in
    let c' = cfg (Eval rho x) k' s in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top x l r1 rho k' wt m () cx () () ()
        (TK_and c f s0 ks wt true l r1 y rho k g top r2 w () () () cy () () tk)))
  | %%T_or 3=x 4=y 6=nx 7=th 9=r2' 11=cx 13=cy%% ->
    let k' = KOr y rho :: k in
    let c' = cfg (Eval rho x) k' s in
    let tk1 = TK_label c f s0 ks w true l th r2 k tk in
    let tk2 = TK_jump c f s0 ks w true l th (B.ILabel nx :: r2') r2 k () tk in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top x nx (B.IJump th :: B.ILabel nx :: r2') rho k' wt m () cx () () ()
        (TK_or c f s0 ks wt true l nx (B.IJump th :: B.ILabel nx :: r2') y rho k g top r2' (B.ILabel th :: r2) w
          () () () () cy () () tk1 tk2)))
  | %%T_let 3=x 4=a 5=b 8=r1 10=ca 11=cb%% ->
    let k' = KLet x b rho :: k in
    let c' = cfg (Eval rho a) k' s in
    let kd' = KD_lett c f s0 ks wt top r1 x b rho k g (top + 1) l r2 w () () () () cb () () tk in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_eval g (top + 1) a (DSlot top) r1 rho k' wt m () ca () () () (KC_slot c f s0 ks wt top r1 k' () kd')))
  | %%T_alias 3=x 4=y 5=s1 6=b 8=r 11=cb%% ->
    let k' = KLet x b rho :: k in
    let c' = cfg (Eval rho (EVar y)) k' s in
    let kd' = KD_lett c f s0 ks wt s1 r x b rho k g top l r2 w () () () () cb () () tk in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_op g top (EVar y) (B.OSlot s1) top r rho k' wt m () (O_var g top y s1 r () ()) () () () kd'))
  | %%T_type 3=e1 7=ct1%% ->
    let c' = cfg (Eval rho e1) k s in
    inhabits (O_step #e #pt #sealed #s #c0 #m c' m (s1' c0 c' ()) (Inr ())
      (MS_test g top e1 l r2 rho k w m () ct1 () () () tk))
#pop-options

(* One step of the simulation (rocq/JitLowerStep.v, Theorem sim). *)
let sim (e : B.env) (pt : B.tree (B.prim & nat)) (sealed : list name) (s : store) (c : config) (m : B.machine)
  (h : mS s c m) : Lemma (iout e pt sealed s c m) =
  match h with
  | %%MS_eval 6=rho 8=w 11=cc 15=kc%% -> step_eval0 e pt sealed s m rho w cc kc
  | %%MS_test 6=rho 8=w 11=ct 15=tk%% -> step_test e pt sealed s m rho w ct tk
  | %%MS_op 7=rho 9=w 12=co 16=kd%% -> step_op e pt sealed s m rho w co kd
  | %%MS_ret 1=v 2=v' 9=dv 10=kd%% -> step_ret e pt sealed kd s v v' m dv
